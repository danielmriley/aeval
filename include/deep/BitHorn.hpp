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
    SMTUtils u;
    Lia2BvTranslator m_Lia2BvTranslator;
    Bv2LiaTranslator m_Bv2LiaTranslator; 
    int debug; 
    std::vector<ExprSet> m_learnedLemmas;  // Stores learned lemmas per iteration
    unsigned m_original_bv_width = 0; // Store original BV width

    ExprSet m_liaSolution;  // Solution found in LIA as set of expressions
    ExprMap m_bvSolution;   // Translated solution in BV

    map<Expr, ExprVector> origBvVars;  // Original BV variables in the program
    map<Expr, ExprVector> origBvVarsPrime;  // Original primed BV variables in the program
    map<Expr, ExprVector> origLiaVars; // Original LIA variables in the program
    map<Expr, ExprVector> origLiaVarsPrime; // Original primed LIA variables in the program

  public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) : 
      m_efac(efac), 
      m_z3(z3),
      m_liaChcs(new CHCs(efac,z3,_debug)), // Create new CHCs object
      m_bvChcs(input),
      u(efac),
      m_Lia2BvTranslator(efac, z3, 4, _debug),
      m_Bv2LiaTranslator(efac, z3, 4, _debug),
      debug(_debug),
      m_learnedLemmas(1) // Initialize with size 1 to store lemmas for the first relation
    { 
      if (debug >= 1) {
        outs() << "Initializing BitHorn solver\n";
      }
      // --- Modification: Detect and store original BV width ---
      if (m_bvChcs.hasBV) {
          for (auto decl : m_bvChcs.decls) {
              if (decl && decl->arity() > 1) {
                  for (unsigned i = 1; i < decl->arity() - 1; ++i) {
                      Expr sort = decl->arg(i);
                      if (isOpX<BVSORT>(sort)) {
                          m_original_bv_width = bv::width(sort);
                          if (debug >= 2) {
                              outs() << "BitHorn: Detected original BV width " << m_original_bv_width << " from decl " << *decl << "\n";
                          }
                          goto width_detected_constructor; // Found it
                      }
                  }
              }
          }
          width_detected_constructor:; 
          // Pass the detected width to the LIA->BV translator instance
          if (m_original_bv_width > 0) {
              m_Lia2BvTranslator.setOriginalBvWidth(m_original_bv_width);
          }
      }
      // --- End Modification ---

      for (auto dd : m_bvChcs.decls)
      {
        Expr d = dd->left();
        // Copy vectors directly
        origBvVars[d] = m_bvChcs.invVars[d];
        origBvVarsPrime[d] = m_bvChcs.invVarsPrime[d];
      }
      for(auto v: origBvVars)
      {
        if (debug >= 3) {
          outs() << "origBvVars: " << v.first << "\n";
          for(auto a: v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
        }
      }
      for(auto v: origBvVarsPrime)
      {
        if (debug >= 3) {
          outs() << "origBvVarsPrime: " << v.first << "\n";
          for(auto a: v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
        }
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
      for(auto d: translatedChcs.decls)
      {
        // Copy vectors directly
        origBvVars[d] = translatedChcs.invVars[d];
        origBvVarsPrime[d] = translatedChcs.invVarsPrime[d];
      }
      
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
        // Copy vectors directly
        origLiaVars[d] = translatedChcs.invVars[d];
        origLiaVarsPrime[d] = translatedChcs.invVarsPrime[d];
      }

      m_liaChcs->reinitialize(translatedChcs);

      if(debug >= 3)
      {
        outs() << "Ending translation\n";
        m_liaChcs->print(true);
      }
      // // Serialize the translated program
      // m_liaChcs->serialize(false);

      // if(debug >= 3)
      // {
      //   outs() << "Serialized LIA program\n";
      // }

      // delete m_liaChcs;
      // m_liaChcs = new CHCs(m_efac, m_z3, debug);
      // m_liaChcs->parse("chc.smt2");

      // Debug dump of CHCs contents
      if (debug >= 5)
      {
        outs() << "\n=== Debug dump of LIA CHCs ===\n";

        // Print declarations
        outs() << "Declarations:\n";
        for (auto decl : m_liaChcs->decls)
        {
          outs() << "decl: " << *decl << "\n";
          if (decl && decl->left())
          {
            outs() << "decl->left(): " << *decl->left() << "\n";
          }
        }

        // Print variables per declaration
        outs() << "\nVariables per declaration:\n";
        for (auto &kv : m_liaChcs->invVars)
        {
          if (kv.first)
          {
            outs() << "For declaration " << *kv.first << ":\n";
            for (auto &var : kv.second)
            {
              outs() << "  var: " << *var << "\n";
              if (var && var->left())
              {
                outs() << "  var->left(): " << *var->left() << "\n";
              }
            }
          }
        }

        // Print Horn rules
        outs() << "\nHorn Rules:\n";
        for (auto &rule : m_liaChcs->chcs)
        {
          outs() << "Rule:\n";
          if (rule.srcRelation)
          {
            outs() << "  src: " << *rule.srcRelation << "\n";
            if (rule.srcRelation->left())
            {
              outs() << "  src->left(): " << *rule.srcRelation->left() << "\n";
            }
          }
          if (rule.dstRelation)
          {
            outs() << "  dst: " << *rule.dstRelation << "\n";
            if (rule.dstRelation->left())
            {
              outs() << "  dst->left(): " << *rule.dstRelation->left() << "\n";
            }
          }
          if (rule.body)
          {
            outs() << "  body: " << *rule.body << "\n";
            if (rule.body->left())
            {
              outs() << "  body->left(): " << *rule.body->left() << "\n";
            }
          }

          outs() << "  Source vars:\n";
          for (auto &v : rule.srcVars)
          {
            outs() << "    var: " << *v << "\n";
            if (v && v->left())
            {
              outs() << "    var->left(): " << *v->left() << "\n";
            }
          }

          outs() << "  Destination vars:\n";
          for (auto &v : rule.dstVars)
          {
            outs() << "    var: " << *v << "\n";
            if (v && v->left())
            {
              outs() << "    var->left(): " << *v->left() << "\n";
            }
          }
        }

        // Print WTO info
        outs() << "\nWTO Declarations:\n";
        for (auto &decl : m_liaChcs->wtoDecls)
        {
          outs() << "decl: " << *decl << "\n";
          if (decl && decl->left())
          {
            outs() << "decl->left(): " << *decl->left() << "\n";
          }
        }

        outs() << "\nWTO CHCs:\n";
        for (auto &wto : m_liaChcs->wtoCHCs)
        {
          outs() << "WTO rule:\n";
          if (wto && wto->srcRelation)
          {
            outs() << "  src: " << *wto->srcRelation << "\n";
            if (wto->srcRelation->left())
            {
              outs() << "  src->left(): " << *wto->srcRelation->left() << "\n";
            }
          }
          if (wto && wto->dstRelation)
          {
            outs() << "  dst: " << *wto->dstRelation << "\n";
            if (wto->dstRelation->left())
            {
              outs() << "  dst->left(): " << *wto->dstRelation->left() << "\n";
            }
          }
        }

        outs() << "\ndWTO CHCs:\n";
        for (auto &wto : m_liaChcs->dwtoCHCs)
        {
          outs() << "WTO rule:\n";
          if (wto && wto->srcRelation)
          {
            outs() << "  src: " << *wto->srcRelation << "\n";
            if (wto->srcRelation->left())
            {
              outs() << "  src->left(): " << *wto->srcRelation->left() << "\n";
            }
          }
          if (wto && wto->dstRelation)
          {
            outs() << "  dst: " << *wto->dstRelation << "\n";
            if (wto->dstRelation->left())
            {
              outs() << "  dst->left(): " << *wto->dstRelation->left() << "\n";
            }
          }
        }

        outs() << "=== End debug dump ===\n\n";
      }

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
        map<Expr, ExprSet> candidates;
        if (!applySolutionToBvSystem(candidates)) {
          if (debug >= 1) outs() << "Failed to apply BV solution\n";
          return false;
        }

        bool isSafe = checkSafetyInBV(candidates);
        
        if (isSafe) {
          if (debug >= 1) {
            outs() << "Found safe BV solution after " << (i+1) << " iterations!\n";
            printSolution();
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
      int mut = 1;       // Disable mutations
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

          if (mut > 0) solver->mutateHeuristicEq(cands[rel], cands[rel], rel, true);
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
      bool bootstrap = solver->bootstrap();
      if (bootstrap) {
        if (debug >= 2)
          outs() << "Bootstrap successful\n";

        // Get lemmas safely
        ExprSet lemmas = solver->getlearnedLemmas(0);
        if (lemmas.empty())
        {
          if (debug >= 1)
            outs() << "Warning: No lemmas found\n";
          return false;
        }

        if (debug >= 3)
        {
          outs() << "Lemmas found:\n";
          for (auto &lemma : lemmas)
          {
            outs() << "  " << lemma << "\n";
          }
        }

        // Validate and normalize lemmas
        ExprSet validLemmas;
        for (auto &lemma : lemmas)
        {
          validLemmas.insert(normalizeExpr(lemma));
        }

        m_liaSolution = validLemmas;
        return !m_liaSolution.empty();
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

        if(debug >= 3)
        {
          outs() << "Lemmas found:\n";
          for (auto &lemma : lemmas) {
            outs() << "  " << lemma << "\n";
          }
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
      if (debug >= 2) {
        outs() << "Translating LIA solution to BV...\n";
      }

      // Clear any previous solution 
      m_bvSolution.clear();

      // Safety check - ensure we have declarations
      if (m_bvChcs.decls.empty()) {
        if (debug >= 1) {
          outs() << "Error: No declarations found in BV CHCs\n";
        }
        return false;
      }

      // --- Modification: Use the member translator directly ---
      // Lia2BvTranslator translator(m_efac, m_z3, 4, debug); // Don't create a new one

      // Print original LIA solution
      if (debug >= 3) {
        outs() << "\nLIA Solution:\n";
        for (auto& expr : m_liaSolution) {
          outs() << "  " << ineqReverter(expr) << "\n";
        }
        outs() << "\n";
      }

      // Get first relation and ensure it exists
      auto firstDecl = m_bvChcs.decls.begin();
      if (firstDecl == m_bvChcs.decls.end() || !*firstDecl) {
        if (debug >= 1) {
          outs() << "Error: Invalid first declaration\n";
        }
        return false;
      }
      
      Expr rel = (*firstDecl)->left();
      if (!rel) {
        if (debug >= 1) {
          outs() << "Error: Invalid relation expression\n";
        }
        return false;
      }

      // Translate each expression in the solution
      for (auto& expr : m_liaSolution) {
        if (!expr) continue; // Skip invalid expressions
        
        // --- Modification: Pass the stored original BV width ---
        Expr bvExpr = m_Lia2BvTranslator.translateExpr(expr, m_original_bv_width); 
        // --- End Modification ---

        if (!bvExpr) {
          if (debug >= 2) {
            outs() << "Warning: Failed to translate expression: " << *expr << "\n";
          }
          continue;
        }

        // Replace variables and add to solution if successful
        bvExpr = replaceAll(bvExpr, origBvVars[rel], m_bvChcs.invVars[rel]);
        if (bvExpr) {
          if (debug >= 3) {
            outs() << "Translated: " << *expr << "\n";
            outs() << "      To: " << *bvExpr << "\n";
          }
          m_bvSolution[expr] = bvExpr;
        }
      }

      // Print full translation results
      if (debug >= 2) {
        outs() << "\nTranslated BV Solution:\n";
        for (auto& kv : m_bvSolution) {
          outs() << "Original: " << *kv.first << "\n";
          outs() << "     BV: " << *kv.second << "\n";
        }
        outs() << "\n";
      }

      return !m_bvSolution.empty();
    }

    bool multiHoudini(vector<HornRuleExt*> worklist, bool recur = true) 
    {
      if (debug >= 3) outs() << "MultiHoudini\n";

      bool res1 = true;
      for (auto &hr : worklist) 
      {
        if (debug >= 3) {
          outs() << "  Doing CHC check (" << hr->srcRelation << " -> "
                 << hr->dstRelation << ")\n";
        }
        
        if (hr->isQuery) continue;

        // Build candidates map for this check
        map<int, ExprVector> cands;
        for (auto& kv : m_bvSolution) {
          int idx = getVarIndex(hr->dstRelation, m_bvChcs.decls);
          if (idx >= 0) {
            cands[idx].push_back(kv.second);
          }
        }

        ExprSet exprs = {hr->body};
        
        if (!hr->isFact) {
          // Add source solution constraints
          ExprSet srcCnjs;
          auto srcSolnIt = m_bvSolution.find(hr->srcRelation); 
          if (srcSolnIt != m_bvSolution.end()) {
            Expr srcSoln = replaceAll(srcSolnIt->second, 
                                    m_bvChcs.invVars[hr->srcRelation],
                                    hr->srcVars);
            exprs.insert(srcSoln);
          }
        }

        if (!hr->isQuery) {
          // Add destination solution constraints
          ExprSet dstCnjs;
          auto dstSolnIt = m_bvSolution.find(hr->dstRelation);
          if (dstSolnIt != m_bvSolution.end()) {
            Expr dstSoln = replaceAll(dstSolnIt->second,
                                    m_bvChcs.invVars[hr->dstRelation], 
                                    hr->dstVars);
            dstCnjs.insert(mkNeg(dstSoln));
          }
          exprs.insert(disjoin(dstCnjs, m_efac));
        }

        if (u.isSat(exprs)) {
          if (debug >= 3) outs() << "    CHC check failed\n";
          if (recur) {
            res1 = false;
            break;
          }
        }
        else if (debug >= 3) outs() << "    CHC check succeeded\n";
      }

      if (!recur) return false;
      if (res1) return true;
      return multiHoudini(worklist);
    }

    bool checkSafetyInBV(map<Expr, ExprSet>& candidates) {
      if (debug >= 2) {
        outs() << "Checking safety of BV solution\n";
      }

      vector<HornRuleExt*> worklist;

      // Add all query rules to the worklist
      for (auto& hr : m_bvChcs.chcs) {
        if (hr.isQuery) {
          worklist.push_back(&hr);
        }
      }

      if (worklist.empty()) {
        if (debug >= 2) {
          outs() << "No queries to check\n";
        }
        return true;
      }

      // Call multiHoudini to check safety
      return !multiHoudini(worklist, true);
    }

    bool strengthenTransitionRelation() {
      if (debug >= 2) {
        outs() << "Strengthening transition relation\n";
      }

      // Get lemmas for strengthening from current solution
      for (auto& hr : m_bvChcs.chcs) {
        if (hr.isQuery) continue;

        // Get solution for dst relation 
        auto it = m_bvSolution.find(hr.dstRelation);
        if (it == m_bvSolution.end()) continue;

        // Convert single expression to set
        ExprSet dstSoln;
        dstSoln.insert(it->second);

        // Add solution to body as constraints
        ExprSet newBody;
        newBody.insert(hr.body);
        for (auto& soln : dstSoln) {
          newBody.insert(soln);
        }

        // Update CHC body with strengthened version
        hr.body = conjoin(newBody, m_efac);
      }

      if (debug >= 3) {
        outs() << "Strengthened BV system:\n";
        m_bvChcs.print(true);
      }

      return true;
    }

    void printSolution() {
      // For each declaration in the BV CHCs
      for (auto& decl : m_bvChcs.decls) {
        Expr rel = decl->left();
        
        // Get all BV solutions - m_bvSolution maps LIA expr -> BV expr
        ExprSet bvSolutions;
        for(auto v: m_liaChcs->invVars[rel])
        {
          if (debug >= 3) {
            outs() << "inv var liaChcs: " << v->left() << "\n";
          }
        }
        for (auto v : m_bvChcs.invVars[rel])
        {
          if (debug >= 3) {
            outs() << "inv var bvChcs: " << v->left() << "\n";
          }
        }
        for (auto& kv : m_bvSolution) {
          if (debug >= 3) {
            outs() << "kv.second: " << kv.second << "\n";
          }
          // Replace LIA vars with corresponding BV vars before adding to solution set
          Expr bvSoln = replaceAll(kv.second, 
                                 m_liaChcs->invVars[rel], 
                                 m_bvChcs.invVars[rel]);
          if (debug >= 3) {
            outs() << "bvSoln: " << bvSoln << "\n"; 
          }
          bvSolutions.insert(bvSoln);
        }

        // Print function definition header 
        outs() << "(define-fun " << *rel << " (";
        for (auto& var : m_bvChcs.invVars[rel]) {
          outs() << "(" << *var << " ";
          u.print(typeOf(var));
          outs() << ")";
        }
        outs() << ") Bool\n  ";

        // Print conjunction of all BV solution expressions
        Expr solution = simplifyArithm(conjoin(bvSolutions, m_efac));
        u.print(solution);
        outs() << ")\n";

        // Verify solution only uses allowed variables
        bool valid = hasOnlyVars(solution, m_bvChcs.invVars[rel]);
        assert(valid);
      }
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
        for (unsigned i = 0; e && i < e->arity(); i++) {
          safeArgs.push_back(normalizeExpr(e->arg(i)));
        }
        return e->efac().mkNary(e->op(), safeArgs);
      }

      return ineqReverter(e);
    }

    // Add new method to apply solution to CHC system
    bool applySolutionToBvSystem(map<Expr, ExprSet>& cands) {
      if (debug >= 3) {
        outs() << "Applying solution to BV system\n";
        outs() << "Solution size: " << m_bvSolution.size() << "\n";
      }

      // Convert ExprMap solution to map<Expr,ExprSet> format
      for (auto& kv : m_bvSolution) {
        cands[kv.first] = ExprSet{kv.second};
      }

      return true;
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
