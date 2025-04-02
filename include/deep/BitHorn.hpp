#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include "Horn.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"

using namespace std;

namespace ufo
{
  class BitHorn 
  {
    private:
    ExprFactory &m_efac;
    EZ3 &m_z3;
    CHCs* m_liaChcs;  // Changed to pointer
    CHCs m_bvChcs;   
    Lia2BvTranslator m_Lia2BvTranslator;
    Bv2LiaTranslator m_Bv2LiaTranslator; 
    int debug; 
    std::vector<ExprSet> m_learnedLemmas;  // Stores learned lemmas per iteration

    ExprSet m_liaSolution;  // Solution found in LIA as set of expressions
    ExprMap m_bvSolution;   // Translated solution in BV

    public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) : 
      m_efac(efac), 
      m_z3(z3),
      m_liaChcs(new CHCs(input)), // Create new CHCs object
      m_bvChcs(input),
      m_Lia2BvTranslator(efac, z3, 4, _debug),
      m_Bv2LiaTranslator(efac, z3, 4, _debug),
      debug(_debug),
      m_learnedLemmas(1) // Initialize with size 1 to store lemmas for the first relation
    { 
      if (debug >= 1) {
        outs() << "Initializing BitHorn solver\n";
      }
    }

    ~BitHorn() {
      if (m_liaChcs) delete m_liaChcs;
    }

    // Add reset method
    void resetLiaChcs() {
      if (m_liaChcs) {
        m_liaChcs->reinitialize(m_bvChcs);
      } else {
        m_liaChcs = new CHCs(m_bvChcs);
      }
    }

    bool translateToBv()
    {
      if(debug >= 3)
      {
        outs() << "Beginning translation\n";
      }
      
      // Create temporary CHCs for the translation
      CHCs translatedChcs = m_Lia2BvTranslator.translate(m_bvChcs);
      
      // Properly reinitialize m_bvChcs from translated version
      m_bvChcs.reinitialize(translatedChcs);

      if (debug >= 3)
      {
        outs() << "Ending translation\n";
        m_bvChcs.print(true);
      }

      // Serialize the translated program  
      m_bvChcs.serialize(false);

      return true;
    }

    bool translateToLia()
    {
      if (debug >= 2)
      {
        outs() << "Translating BV to LIA\n";
      }

      // Create temporary CHCs for the translation
      CHCs translatedChcs = m_Bv2LiaTranslator.translate(m_bvChcs);
      for (auto d : translatedChcs.decls)
      {
        outs() << "Decl: " << d->left() << "\n";
        outs() << "Decl: " << d->right() << "\n";
        outs() << "Decl: " << d->left() << "\n";
      }

      for (auto v : translatedChcs.invVars)
      {
        outs() << "InvVar: " << v.first << "\n";
        for (auto a : v.second)
        {
          outs() << "  Var: " << a << "\n";
          outs() << "  Type: " << bind::typeOf(a) << "\n";
        }
      }
      for (auto v : translatedChcs.invVarsPrime)
      {
        outs() << "InvVarPrime: " << v.first << "\n";
        for (auto a : v.second)
        {
          outs() << "  Var: " << a << "\n";
          outs() << "  Type: " << bind::typeOf(a) << "\n";
        }
      }
      // Reset and reinitialize liaChcs
      resetLiaChcs();
      m_liaChcs->reinitialize(translatedChcs);

      for(auto d: m_liaChcs->decls)
      {
        outs() << "Decl: " << d->left() << "\n";
        outs() << "Decl: " << d->right() << "\n";
        outs() << "Decl: " << d->left() << "\n";
      }

      for(auto v: m_liaChcs->invVars)
      {
        outs() << "InvVar: " << v.first << "\n";
        for(auto a: v.second)
        {
          outs() << "  Var: " << a << "\n";
          outs() << "  Type: " << bind::typeOf(a) << "\n";
        }
      }
      for(auto v: m_liaChcs->invVarsPrime)
      {
        outs() << "InvVarPrime: " << v.first << "\n";
        for(auto a: v.second)
        {
          outs() << "  Var: " << a << "\n";
          outs() << "  Type: " << bind::typeOf(a) << "\n";
        }
      }

      m_liaChcs->serialize(false);
      delete m_liaChcs;
      m_liaChcs = new CHCs(m_efac, m_z3, debug);
      m_liaChcs->parse("chc.smt2");

      return true;
    }

    CHCs& getLiaChcs() { return *m_liaChcs; }
    CHCs& getBvChcs() { return m_bvChcs; }

    void getSolution(ExprMap &e) {
      e = m_bvSolution;
    }

    ExprMap getSolution() {
      return m_bvSolution;
    }

    bool solve(unsigned to = 100) {
      if (debug >= 1) {
        outs() << "Starting BitHorn solver with timeout " << to << "\n";
      }

      for (unsigned i = 0; i < to; i++) {
        if (debug >= 2) {
          outs() << "\nIteration " << i << " of " << to << "\n";
        }

        // 1. Translate current BV system to LIA
        if (!translateToLia()) {
          if (debug >= 1) outs() << "Failed to translate BV to LIA\n";
          return false;
        }
        
        if (debug >= 3) {
          outs() << "Translated BV -> LIA system:\n";
          m_liaChcs->print(true);
        }

        // 2. Try to solve LIA system with timeout
        if (!solveLIA()) {
          if (debug >= 1) outs() << "Could not find LIA solution\n";
          return false;
        }

        if (debug >= 3) {
          outs() << "Found LIA solution with " << m_liaSolution.size() << " variables\n";
        }

        // 3. Translate LIA solution back to BV
        if (!translateSolutionToBv()) {
          if (debug >= 1) outs() << "Failed to translate solution to BV\n";
          return false;
        }

        if (debug >= 3) {
          outs() << "Translated solution back to BV with " << m_bvSolution.size() << " variables\n";
        }

        // 4. Check if solution is safe in BV
        if (checkSafetyInBV()) {
          if (debug >= 1) {
            outs() << "Found safe BV solution after " << (i+1) << " iterations!\n";
          }
          return true;
        }

        if (debug >= 2) {
          outs() << "Solution not safe in BV, strengthening...\n";
        }

        // 5. Strengthen transition relation and continue
        if (!strengthenTransitionRelation()) {
          if (debug >= 1) outs() << "Failed to strengthen transition relation\n";
          return false;
        }
      }

      if (debug >= 1) {
        outs() << "No solution found after " << to << " iterations\n";
      }
      return false;
    }

    private:
    void initializeSolver(std::unique_ptr<RndLearnerV4> solver)
    {
      
    }

    bool solveLIA(unsigned int to = 10) {
      if (debug >= 2) {
        outs() << "Attempting to solve LIA system\n";  
      }

      // Before creating solver, normalize and validate all expressions
      for (auto &rule : m_liaChcs->chcs) {
        if (containsOp<IDIV>(rule.body) || containsOp<MOD>(rule.body)) {
          if (debug >= 1) outs() << "Warning: Skipping rule with division\n";
          continue;
        }
        rule.body = normalizeExpr(rule.body);
      }

      // Configure solver with safe parameters
      bool freqs = true;
      bool aggp = false;  // Disable aggressive pruning to avoid FPE
      int mut = 0;       // Disable mutations
      int da = 0;
      bool doDisj = false;
      int mbpEqs = 0;
      bool dAllMbp = false;
      bool dAddProp = false;
      bool dAddDat = false;
      bool dStrenMbp = false;
      int dFwd = 0;
      bool dRec = false;
      bool dGen = false;

      // Create solver
      std::unique_ptr<RndLearnerV4> solver(new RndLearnerV4(m_efac, m_z3, 
                                        *m_liaChcs, to,
                                        freqs, aggp, mut, da,
                                        doDisj, mbpEqs, dAllMbp,
                                        dAddProp, dAddDat, dStrenMbp,
                                        dFwd, dRec, dGen, debug));

      if (!solver) {
        if (debug >= 1) outs() << "Error: Failed to create solver\n";
        return false;
      }

      // Initialize solver with candidates 
      map<Expr, ExprSet> cands;
      BndExpl bnd(*m_liaChcs, to, debug);

      // Process each cycle to generate candidates
      for (auto& cyc : m_liaChcs->cycles) {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++) {
          assert(rel == m_liaChcs->chcs[cyc.second[i][0]].srcRelation);
          
          if (solver->initializedDecl(rel)) continue;
          solver->initializeDecl(rel);

          // Process prefix for candidates
          Expr pref = bnd.compactPrefix(rel, i);
          ExprSet tmp;
          getConj(pref, tmp);
          
          // Filter candidates that only use invariant variables  
          for (auto & t : tmp) {
            if (hasOnlyVars(t, m_liaChcs->invVars[rel])) {
              cands[rel].insert(t);
            }
          }

          solver->initializeAux(cands[rel], bnd, rel, i, pref);
        }
      }

      // Generate data-based candidates if enabled
      if (da > 0) {
        solver->getDataCandidates(cands);
      }

      // Process declarations with priority propagation
      for (auto & dcl : m_liaChcs->wtoDecls) {
        solver->addCandidates(dcl, cands[dcl]);
        solver->prepareSeeds(dcl, cands[dcl]);
      }

      // Bootstrap and calculate initial statistics
      if (solver->bootstrap()) {
        if (debug >= 2) outs() << "Bootstrap successful\n";
        return true;
      }

      solver->calculateStatistics();
      solver->deferredPriorities();
      std::srand(std::time(0));

      // Try synthesis
      if (solver->synthesize(to)) {
        if (debug >= 2) {
          outs() << "V4 solver found solution\n";
        }

        // Get lemmas safely
        ExprSet lemmas = solver->getlearnedLemmas(0);
        if (lemmas.empty()) {
          if (debug >= 1) outs() << "Warning: No lemmas found\n";
          return false;
        }

        // Validate and normalize lemmas
        ExprSet validLemmas;
        for (auto &lemma : lemmas) {
          validLemmas.insert(normalizeExpr(lemma));
        }

        m_liaSolution = validLemmas;
        return !m_liaSolution.empty();
      }

      return false;
    }

    bool translateSolutionToBv() {
      // Translate m_liaSolution to BV using m_Lia2BvTranslator
      // Store in m_bvSolution  
      return false; // TODO
    }

    bool checkSafetyInBV() {
      // Check if m_bvSolution satisfies safety in m_bvChcs
      return false; // TODO
    }

    bool strengthenTransitionRelation() {
      // Add constraints from m_bvSolution to m_bvChcs transition relation
      return false; // TODO
    }

    void printSolution() {
      outs() << "BV Solution: \n";
      // Print m_bvSolution
    }

    // Add helper to normalize expressions
    Expr normalizeExpr(Expr e) {
      if (!e) return e;
      
      // Handle division and mod operations safely
      if (containsOp<IDIV>(e) || containsOp<MOD>(e)) {
        return mk<TRUE>(e->getFactory());
      }

      // Ensure numeric operations use safe ranges
      if (isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e)) {
        ExprVector safeArgs;
        for (unsigned i = 0; i < e->arity(); i++) {
          safeArgs.push_back(normalizeExpr(e->arg(i)));
        }
        return e->efac().mkNary(e->op(), safeArgs);
      }

      return e;
    }
  };

  // Main entry point for BV translation and solving
  inline void learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, int debug)
  {
    // Create factories and parse input
    ExprFactory efac;
    EZ3 z3(efac); 

    // Parse the original CHC system
    CHCs ruleManager(efac, z3, debug);
    if (!ruleManager.parse(smt, doElim, doArithm))
    {
      outs() << "Error parsing input file\n";
      return;
    }

    // For non-serialization case, check if input is BV format
    if (!ruleManager.hasBV && !ser)
    {
      outs() << "Input is not in BV format\n";
      return;
    }

    // Create BitHorn solver and pass through maxAttempts parameter 
    BitHorn bh(efac, z3, ruleManager, debug);

    if (ser) {
      // Just translate and serialize
      if(debug >= 2) 
      {
        outs() << "Translating LIA to BV.\n";
      }
      if (!bh.translateToBv()) {
        outs() << "Error translating LIA to BV\n"; 
        return;
      }
      bh.getBvChcs().serialize(false);
      if(debug >= 2) outs() << "Serialized BV translation\n";
      return;
    }

    // Solve BV system with maxAttempts
    bh.solve(to);
  }
}

#endif
