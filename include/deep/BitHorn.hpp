#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include <utility>          // Needed for std::pair

#include "Horn.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"
#include "ae/ExprSimpl.hpp" // Include ExprSimpl for simplification functions
#include "sampl/Sampl.hpp"
#include "sampl/SeedMiner.hpp"

using namespace std;

namespace ufo
{
  class BitHorn
  {
  private:

    ExprFactory &m_efac;
    EZ3 &m_z3;
    CHCs *m_liaChcs; // Changed to pointer
    CHCs& m_bvChcs;
    SMTUtils u;
    Lia2BvTranslator m_Lia2BvTranslator;
    Bv2LiaTranslator m_Bv2LiaTranslator;
    bool d2;
    bool doReg;
    bool doConnect;
    bool doGJ;
    int debug;

    std::vector<ExprSet> m_learnedLemmas; // Stores learned lemmas per iteration
    unsigned m_original_bv_width = 0;
    map<Expr, ExprSet> m_liaSolutionMap; // Maps LIA relation -> LIA solution ExprSet
    map<Expr, Expr> m_bvSolutionMap;     // Maps BV relation -> combined BV solution Expr

    map<Expr, ExprVector> origBvVars;       // Original BV variables in the program
    map<Expr, ExprVector> origBvVarsPrime;  // Original primed BV variables in the program
    map<Expr, ExprVector> origLiaVars;      // Original LIA variables in the program
    map<Expr, ExprVector> origLiaVarsPrime; // Original primed LIA variables in the program

    void printBvSolutionMap(const map<Expr, Expr> &bvSolutionMap)
    {
      for (const auto &kv : bvSolutionMap)
      {
        Expr rel = kv.first;
        Expr solution = kv.second; // This is the combined BV solution

        // Check if relation exists in invVars map
        if (!m_bvChcs.invVars.count(rel))
        {
          if (debug >= 1)
          {
            outs() << "  ; Warning: Cannot print solution for " << *rel << " - missing variables.\n";
          }
          continue;
        }
        const ExprVector &invVars = m_bvChcs.invVars.at(rel);

        // Print function definition header
        outs() << "  (define-fun " << *rel << " (";
        for (const auto &var : invVars)
        {
          // Print var name and type
          outs() << "(" << *var << " ";
          u.print(typeOf(var));
          outs() << ")";
        }
        outs() << ") Bool\n    ";

        // Print the combined BV solution expression
        u.print(solution);
        outs() << ")\n";

        ExprVector nonConstInvVars = invVars; // Create non-const copy for validation
        bool valid = hasOnlyVars(solution, nonConstInvVars);
        if (!valid && debug >= 1)
        {
          outs() << "  ; Warning: Solution for " << *rel << " contains unexpected variables!\n";
          outs() << "    ; Extra vars: ";
          ExprSet extra;
          getExtraVars(solution, nonConstInvVars, extra);
          for (const auto &v : extra)
            outs() << *v << " ";
          outs() << "\n";
        }
      }
    }

    Expr normalizeExpr(Expr e)
    {
      if (!e)
        return e;

      if (debug >= 5)
      {
        outs() << "Entering normalizeExpr: " << *e << "\n";
      }

      // Handle division and mod operations safely
      if (containsOp<IDIV>(e) || containsOp<MOD>(e))
      {
        return mk<TRUE>(e->getFactory());
      }

      // Ensure numeric operations use safe ranges
      if (isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e))
      {
        ExprVector safeArgs;
        for (unsigned i = 0; e && i < e->arity(); i++)
        {
          safeArgs.push_back(normalizeExpr(e->arg(i)));
        }
        return e->efac().mkNary(e->op(), safeArgs);
      }

      // Use ineqReverter from ExprSimpl.hpp
      return ineqReverter(e);
    }

    void processLearnedLiaLemmas(RndLearnerV4 &solver)
    {
      if (debug >= 3)
      {
        outs() << "\n--- Processing Learned LIA Lemmas ---\n";
      }
      m_liaSolutionMap.clear();
      for (auto &liaDecl : m_liaChcs->decls)
      {
        Expr liaDeclExpr = liaDecl->left();
        int invNum = getVarIndex(liaDecl, m_liaChcs->decls);

        if (debug >= 4)
        {
          outs() << "  Processing relation: " << *liaDeclExpr << "\n";
        }
        if (debug >= 5)
        {
          outs() << "    Full decl: " << *liaDecl << ", invNum: " << invNum << "\n";
          if (invNum >= 0)
            solver.printSolutionForRelation(invNum);
        }

        if (invNum < 0)
        {
          if (debug >= 1)
          {
            outs() << "  Error: Could not find index for LIA declaration: " << *liaDecl << "\n";
          }
          continue;
        }

        ExprSet lemmas = solver.getlearnedLemmas(invNum);
        if (debug >= 4)
        {
          outs() << "    Lemmas size for " << *liaDeclExpr << ": " << lemmas.size() << "\n";
        }
        if (!lemmas.empty())
        {
          ExprSet simplifiedLemmas;
          if (debug >= 4)
          {
            outs() << "    Simplifying individual lemmas for " << *liaDeclExpr << ":\n";
          }
          for (auto &lemma : lemmas)
          {
            if (debug >= 5)
            {
              outs() << "      Original: " << *lemma << "\n";
            }
            Expr normalized = normalizeExpr(lemma);
            if (debug >= 5)
            {
              outs() << "      Normalized (normalizeExpr): " << *normalized << "\n";
            }
            Expr simplified_lemma = simplifyArithm(normalized, false, false);
            if (debug >= 5)
            {
              outs() << "      Simplified (simplifyArithm): " << *simplified_lemma << "\n";
            }

            if (!isOpX<TRUE>(simplified_lemma))
            {
              simplifiedLemmas.insert(simplified_lemma);
            }
          }

          Expr conjunction = conjoin(simplifiedLemmas, m_efac);
          Expr simplifiedArithConj = simplifyArithmConjunctions(conjunction, false);
          Expr finalConjunction = simplifyBool(simplifiedArithConj);

          ExprSet conjunctLemmas;
          getConj(finalConjunction, conjunctLemmas);

          ExprSet finalNormalizedLemmas;
          if (debug >= 4)
          {
            outs() << "    Applying final positive normalization for " << *liaDeclExpr << ":\n";
          }
          for (auto &conjLemma : conjunctLemmas)
          {
            if (debug >= 5)
            {
              outs() << "      Input to normalizePositive: " << *conjLemma << "\n";
            }
            Expr posNormalized = normalizePositive(conjLemma, m_efac, debug);
            if (debug >= 5)
            {
              outs() << "      Output of normalizePositive: " << *posNormalized << "\n";
            }
            if (!isOpX<TRUE>(posNormalized))
            {
              finalNormalizedLemmas.insert(posNormalized);
            }
          }

          m_liaSolutionMap[liaDeclExpr] = finalNormalizedLemmas;

          if (debug >= 3)
          {
            outs() << "  Final LIA Lemmas for " << *liaDeclExpr << " (" << finalNormalizedLemmas.size() << "):\n";
            for (auto &l : finalNormalizedLemmas)
            {
              outs() << "    " << *l << "\n";
            }
          }
        }
        else
        {
          if (debug >= 2)
          {
            outs() << "  Warning: No LIA lemmas found for " << *liaDeclExpr << "\n";
          }
          m_liaSolutionMap[liaDeclExpr] = ExprSet();
        }
      }
    }

    bool checkLemmasAgainstRules(const vector<HornRuleExt *> &worklist, const map<Expr, Expr> &solutionMap)
    {
      if (debug >= 5)
      {
        outs() << "\n--- Checking Lemmas Against Rules (" << worklist.size() << " rules) ---\n";
      }
      for (const auto *hr : worklist)
      {
        if (debug >= 5)
        {
          outs() << "  Checking Rule: (";
          if (hr->srcRelation)
            outs() << *hr->srcRelation;
          else
            outs() << "null";
          outs() << " -> ";
          if (hr->dstRelation)
            outs() << *hr->dstRelation;
          else
            outs() << "null";
          outs() << ")\n";
        }

        ExprSet checkExprs;
        checkExprs.insert(hr->body);

        if (!hr->isFact && hr->srcRelation)
        {
          auto srcSolnIt = solutionMap.find(hr->srcRelation);
          if (srcSolnIt != solutionMap.end() && m_bvChcs.invVars.count(hr->srcRelation))
          {
            Expr srcSolnCombined = srcSolnIt->second;
            ExprVector invVars = m_bvChcs.invVars.at(hr->srcRelation);
            ExprVector srcVars = hr->srcVars;
            if (invVars.size() == srcVars.size())
            {
              Expr srcSolnSubst = replaceAll(srcSolnCombined, invVars, srcVars);
              checkExprs.insert(srcSolnSubst);
              if (debug >= 5)
              {
                outs() << "    Adding SrcInv (" << *hr->srcRelation << "): " << *srcSolnSubst << "\n";
              }
            }
            else
            {
              if (debug >= 5)
              {
                outs() << "  Warning: Var mismatch for src " << *hr->srcRelation << ". Skipping rule.\n";
              }
              continue;
            }
          }
          else
          {
            if (debug >= 5)
            {
              outs() << "    SrcInv missing or vars missing for " << *hr->srcRelation << ", assuming true.\n";
            }
          }
        }

        if (!hr->isQuery && hr->dstRelation)
        {
          auto dstSolnIt = solutionMap.find(hr->dstRelation);
          if (dstSolnIt != solutionMap.end() && m_bvChcs.invVars.count(hr->dstRelation))
          {
            Expr dstSolnCombined = dstSolnIt->second;
            ExprVector invVars = m_bvChcs.invVars.at(hr->dstRelation);
            ExprVector dstVars = hr->dstVars;
            if (invVars.size() == dstVars.size())
            {
              Expr dstSolnSubst = replaceAll(dstSolnCombined, invVars, dstVars);
              checkExprs.insert(mkNeg(dstSolnSubst));
              if (debug >= 5)
              {
                outs() << "    Adding !DstInv (" << *hr->dstRelation << "): " << *mkNeg(dstSolnSubst) << "\n";
              }
            }
            else
            {
              if (debug >= 5)
              {
                outs() << "  Warning: Var mismatch for dst " << *hr->dstRelation << ". Skipping rule.\n";
              }
              continue;
            }
          }
          else
          {
            if (debug >= 5)
            {
              outs() << "    DstInv missing or vars missing for " << *hr->dstRelation << ". Rule check skipped.\n";
            }
            continue;
          }
        }

        if (debug >= 5)
        {
          outs() << "    Checking SMT query:\n";
          pprint(conjoin(checkExprs, m_efac), 6);
          outs() << "\n";
        }
        boost::tribool checkResult = u.isSat(checkExprs);

        if (checkResult)
        {
          if (debug >= 5)
          {
            outs() << "  Rule FAILED (SAT/Indeterminate): (";
            if (hr->srcRelation)
              outs() << *hr->srcRelation;
            else
              outs() << "null";
            outs() << " -> ";
            if (hr->dstRelation)
              outs() << *hr->dstRelation;
            else
              outs() << "null";
            outs() << ")\n";
          }
          return false;
        }
        else
        {
          if (debug >= 5)
          {
            outs() << "    Rule PASSED (UNSAT)\n";
          }
        }
      }

      if (debug >= 5)
      {
        outs() << "Finished checkLemmasAgainstRules: All rules PASSED.\n";
      }
      return true;
    }

  public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, bool _d2, bool _doGJ, bool _doReg, bool _doCon, int _debug = 0) : 
      m_efac(efac),
      m_z3(z3),
      m_liaChcs(new CHCs(efac, z3, _debug)),
      m_bvChcs(input),
      u(efac),
      m_Lia2BvTranslator(efac, z3, 4, _debug),
      m_Bv2LiaTranslator(efac, z3, 4, _debug),
      m_learnedLemmas(1),
      d2(_d2),
      doGJ(_doGJ),
      doReg(_doReg),
      doConnect(_doCon),
      debug(_debug)
    {
      if (debug >= 1)
      {
        outs() << "\n--- Initializing BitHorn Solver ---\n";
      }

      bool width_detected = false;
      if (m_bvChcs.hasBV)
      {
        for (auto decl : m_bvChcs.decls)
        {
          if (decl && decl->arity() > 1)
          {
            for (unsigned i = 1; i < decl->arity() - 1; ++i)
            {
              Expr sort = decl->arg(i);
              if (isOpX<BVSORT>(sort))
              {
                m_original_bv_width = bv::width(sort);
                if (debug >= 2)
                {
                  outs() << "  Detected original BV width " << m_original_bv_width << " from decl " << *decl << "\n";
                }
                width_detected = true;
                break;
              }
            }
          }
          if (width_detected)
          {
            break;
          }
        }

        if (width_detected && m_original_bv_width > 0)
        {
          m_Lia2BvTranslator.setOriginalBvWidth(m_original_bv_width);
        }
        else if (debug >= 1 && m_bvChcs.hasBV)
        {
          outs() << "  Warning: Could not detect original BV width from declarations. Using default.\n";
        }
      }

      for (auto dd : m_bvChcs.decls)
      {
        Expr d = dd->left();
        if (!d)
          continue;

        if (m_bvChcs.invVars.count(d))
        {
          origBvVars[d] = m_bvChcs.invVars[d];
          if (debug >= 3)
          {
            outs() << "  origBvVars: Populated for " << *d << " with " << origBvVars[d].size() << " vars\n";
          }
        }
        else if (debug >= 2)
        {
          outs() << "  Warning: invVars not found for relation " << *d << ".\n";
        }

        if (m_bvChcs.invVarsPrime.count(d))
        {
          origBvVarsPrime[d] = m_bvChcs.invVarsPrime[d];
          if (debug >= 3)
          {
            outs() << "  origBvVarsPrime: Populated for " << *d << " with " << origBvVarsPrime[d].size() << " vars\n";
          }
        }
        else if (debug >= 2)
        {
          outs() << "  Warning: invVarsPrime not found for relation " << *d << ".\n";
        }
      }
    }

    bool translateToBv()
    {
      if (debug >= 1)
      {
        outs() << "\n--- Translating LIA to BV (for serialization) ---\n";
      }

      // Ensure the input CHCs (stored in m_bvChcs initially) are treated as LIA
      // The Lia2BvTranslator will handle the conversion based on the types it finds.
      // It also detects original BV width if input.hasBV is true, which might be relevant
      // if the input is mixed or already BV.

      // Perform the translation using the Lia2BvTranslator
      // The translate method takes the input CHCs (m_bvChcs) and returns the translated BV CHCs.
      m_bvChcs = m_Lia2BvTranslator.translate(m_bvChcs);

      // Check if translation produced a valid result (basic check)
      if (m_bvChcs.decls.empty() && !m_bvChcs.chcs.empty()) {
          if (debug >= 1) {
              outs() << "  Error: LIA to BV translation resulted in CHCs with rules but no declarations.\n";
          }
          return false;
      }

      if (debug >= 2)
      {
        outs() << "  LIA to BV translation complete.\n";
        if (debug >= 3) {
            outs() << "    --- Translated BV System (m_bvChcs) ---\n";
            m_bvChcs.print(true);
            outs() << "    --- End Translated BV System ---\n";
        }
        outs() << "  Serializing translated BV CHCs...\n";
      }

      // Serialize the resulting BV CHCs
      m_bvChcs.serialize(false); // Pass false to avoid adding .smt2 extension

      if (debug >= 1)
      {
        outs() << "  Translation and serialization successful.\n";
      }

      return true;
    }

    bool translateToLia(bool addBitWidthBounds = false)
    {
      if (debug >= 1)
      {
        outs() << "\n--- Translating BV to LIA ---\n";
      }

      origLiaVars.clear();
      origLiaVarsPrime.clear();

      delete m_liaChcs;
      m_liaChcs = new CHCs(m_Bv2LiaTranslator.translate(m_bvChcs, addBitWidthBounds));

      if (!m_liaChcs)
      {
        if (debug >= 1)
        {
          outs() << "  Error: Bv2LiaTranslator returned a null CHCs object.\n";
        }
        m_liaChcs = new CHCs(m_efac, m_z3, debug);
        return false;
      }

      const auto &bvToLiaDeclNameMap = m_Bv2LiaTranslator.getBvToLiaDeclMap();

      for (const auto &bvDecl : m_bvChcs.decls)
      {
        Expr bvRelName = bvDecl->left();
        if (!bvRelName)
          continue;

        auto nameMapIt = bvToLiaDeclNameMap.find(bvRelName);
        if (nameMapIt == bvToLiaDeclNameMap.end())
        {
          if (debug >= 1)
          {
            outs() << "  Warning: Could not find translated LIA name for BV relation " << *bvRelName << " in map.\n";
          }
          continue;
        }
        Expr liaRelName = nameMapIt->second;

        if (m_bvChcs.invVars.count(bvRelName))
        {
          const ExprVector &bvInvVars = m_bvChcs.invVars.at(bvRelName);
          ExprVector translatedLiaVars;
          for (const auto &bvVar : bvInvVars)
          {
            Expr liaVar = m_Bv2LiaTranslator.translateExpr(bvVar);
            if (liaVar && liaVar != bvVar)
            {
              translatedLiaVars.push_back(liaVar);
            }
            else if (liaVar == bvVar)
            {
              if (debug >= 3)
              {
                outs() << "    Var " << *bvVar << " kept as is during origLiaVars population.\n";
              }
              translatedLiaVars.push_back(bvVar);
            }
            else
            {
              if (debug >= 1)
              {
                outs() << "  Warning: Failed to translate BV variable " << *bvVar << " for relation " << *bvRelName << "\n";
              }
            }
          }
          origLiaVars[liaRelName] = translatedLiaVars;
          if (debug >= 4)
          {
            outs() << "  Stored origLiaVars for LIA rel " << *liaRelName << " (from BV " << *bvRelName << "): " << translatedLiaVars.size() << " vars\n";
          }
        }
        else
        {
          if (debug >= 2)
          {
            outs() << "  Warning: Original BV invVars not found for relation " << *bvRelName << "\n";
          }
        }

        if (m_bvChcs.invVarsPrime.count(bvRelName))
        {
          const ExprVector &bvInvVarsPrime = m_bvChcs.invVarsPrime.at(bvRelName);
          ExprVector translatedLiaVarsPrime;
          for (const auto &bvVarPrime : bvInvVarsPrime)
          {
            Expr liaVarPrime = m_Bv2LiaTranslator.translateExpr(bvVarPrime);
            if (liaVarPrime && liaVarPrime != bvVarPrime)
            {
              translatedLiaVarsPrime.push_back(liaVarPrime);
            }
            else if (liaVarPrime == bvVarPrime)
            {
              if (debug >= 3)
              {
                outs() << "    Primed Var " << *bvVarPrime << " kept as is during origLiaVarsPrime population.\n";
              }
              translatedLiaVarsPrime.push_back(bvVarPrime);
            }
            else
            {
              if (debug >= 1)
              {
                outs() << "  Warning: Failed to translate primed BV variable " << *bvVarPrime << " for relation " << *bvRelName << "\n";
              }
            }
          }
          origLiaVarsPrime[liaRelName] = translatedLiaVarsPrime;
          if (debug >= 4)
          {
            outs() << "  Stored origLiaVarsPrime for LIA rel " << *liaRelName << " (from BV " << *bvRelName << "): " << translatedLiaVarsPrime.size() << " vars\n";
          }
        }
      }

      if (debug >= 2)
      {
        outs() << "  Finished translating BV to LIA using Bv2LiaTranslator::translate.\n";
        if (debug >= 3)
        {
          outs() << "    --- Translated LIA System (m_liaChcs) ---\n";
          m_liaChcs->print(true);
          outs() << "    --- End Translated LIA System ---\n";
          outs() << "    --- OrigLiaVars Map (" << origLiaVars.size() << " entries) ---\n";
          for (const auto &pair : origLiaVars)
          {
            outs() << "      Rel: " << *pair.first << " -> ";
            for (const auto &v : pair.second)
              outs() << *v << " ";
            outs() << "\n";
          }
          outs() << "    --- End OrigLiaVars Map ---\n";
        }
      }
      return true;
    }

    CHCs &getBvChcs()
    {
      return m_bvChcs;
    }

    std::vector<std::map<int, Expr>> invarVars;

    void initializeSampl(SamplFactory& sf, Expr invRel, ExprSet& cands, set<cpp_int>& progConsts, set<cpp_int>& intCoefs)
    {
      ExprSet arr1, arr2;
      ExprVector arrVars;
      // InitializeSampl

      if (sf.bvf.nonlinVars.size() > 0)
      {
        if (debug >= 4)
          outs() << "Multed vars: ";
        for (auto &a : sf.bvf.nonlinVars)
        {
          if (debug >= 4)
            outs() << *a.first << " = " << *a.second << "\n";
          sf.bvf.addVar(a.second);
          Expr b = a.first->right();
          if (is_bvconst(b))
            intCoefs.insert(lexical_cast<cpp_int>(b));
        }
      }

      for (auto &c : progConsts) progConsts.insert(-c);
      for (auto &a : intCoefs) intCoefs.insert(-a);
      for (auto &a : intCoefs) if (a != 0) sf.bvf.addIntCoef(a);

      auto progConstsTmp = progConsts;
      for (auto &a : progConstsTmp)
        for (auto &b : intCoefs)
          progConsts.insert(a*b);

      // sort progConsts and push to vector:
      while (progConsts.size() > 0)
      {
        cpp_int min = *progConsts.begin();
        for (auto c : progConsts)
        {
          if (c < min)
          {
            min = c;
          }
        }
        progConsts.erase(min);
        sf.bvf.addConst(min);
      }

      sf.initialize(arr1, arrVars, arr2, m_original_bv_width);

      // normalize samples obtained from CHCs
      for (auto & cand : cands) Sampl& s = sf.exprToSampl(cand);
    }

    void doSeedMining(SamplFactory& sf, Expr invRel, ExprSet& cands, set<cpp_int>& progConsts, set<cpp_int>& intCoefs)
    {
      if (debug >= 2)
      {
        outs() << "\n--- Performing Seed Mining for " << *invRel << " ---\n";
      }

      for(auto &hr : m_bvChcs.chcs)
      {
        SeedMiner sm(hr, invRel, invarVars.back(), sf.bvf.nonlinVars);
        sm.analyzeCode();

        // convert intConsts to progConsts and add additive inverses (if applicable):
        for (auto &a : sm.intConsts) progConsts.insert(a);
        for (auto &a : sm.intCoefs) intCoefs.insert(a); // same for intCoefs
        for (auto &a : sm.candidates) cands.insert(a);
      }

      if (debug >= 3)
      {
        outs() << "  Seed mining complete. Candidates found: " << cands.size() << "\n";
        for(const auto &c : cands) outs() << c << " ";
        outs() << "\n";
        outs() << "  Program constants: ";
        for (const auto &c : progConsts) outs() << c << " ";
        outs() << "\n";
        outs() << "  Integer coefficients: ";
        for (const auto &c : intCoefs) outs() << c << " ";
        outs() << "\n";
      }
    }

    void prepareSeeds(SamplFactory& sf, Expr invDecl)
    {
      invarVars.push_back(map<int, Expr>());

      for (int i = 0; i < m_bvChcs.invVars[invDecl].size(); i++)
      {

        Expr var = m_bvChcs.invVars[invDecl][i];
        if(sf.addVar(var))
        {
          invarVars.back()[i] = var;
        }
      }

      set<cpp_int> progConsts, intCoefs;
      ExprSet cands;
      doSeedMining(sf, invDecl, cands, progConsts, intCoefs);
      initializeSampl(sf, invDecl, cands, progConsts, intCoefs);
    }

    bool isTautology(Expr a) // adjusted for big disjunctions
    {
      if (isOpX<TRUE>(a))
        return true;

      ExprSet disjs;
      getDisj(a, disjs);
      if (disjs.size() == 1)
        return false;

      map<ExprSet, ExprSet> varComb;
      for (auto &a : disjs)
      {
        ExprSet avars;
        expr::filter(a, bind::IsConst(), std::inserter(avars, avars.begin()));
        if (avars.size() == 0)
          continue;
        varComb[avars].insert(mkNeg(a));
      }

      if (varComb.size() == 0)
        return false;

      bool res = false;
      for (auto &v : varComb)
      {
        if (!u.isSat(conjoin(v.second, m_efac)))
        {
          res = true;
          break;
        }
      }
      return res;
    }

    void testBVcom()
    {
      if (debug >= 1)
      {
        outs() << "\n--- Testing BVCom ---\n";
        m_bvChcs.print(true);
        outs() << "\n";
      }

      SamplFactory sf(m_efac, false);

      Expr invDecl = (*m_bvChcs.decls.begin())->left();
      prepareSeeds(sf, invDecl);
      sf.calculateStatistics(false, false);

      if(debug >= 3)
      {
        outs() << "Seed mining complete. Statistics:\n=================================\n";
        sf.printStatistics();
      }

      outs() << "\nSAMPLING\n========\n";
      
      bool skip = false;
      for(int i = 0; i < 10; i++)
      {
        Expr cand = sf.getFreshCandidate();
        if(cand == NULL) continue;
        if(debug >= 2) outs() << "Sample " << i+1 << ": " << cand << "\n";

        // Do some checks on the candidate produced and update the densities.
        if(isTautology(cand))
        {
          sf.assignPrioritiesForLearned();
          skip = true;
        }

        if(sf.bvf.nonlinVars.size() > 0 && u.isFalse(cand))
        {
          sf.assignPrioritiesForFailed();
          skip = true;
        }

        if(skip) continue;

        bool isSafe = assembleAndCheck(cand);

        if(isSafe)
        {
          sf.assignPrioritiesForLearned();
          if(checkSafetyInBV())
          {
            outs() << "Success after sampling " << i+1 << " sample" << (i+1>1 ? "s" : "") << ".\n";
            printSolution();
            return;
          }
        }
        else
        {
          sf.assignPrioritiesForFailed();
          if (debug >= 2)
          {
            outs() << "Sample " << i+1 << " is UNSAFE.\n";
          }
        }
      }

      outs() << "No safe solution found after sampling.\n";
      printBvSolutionMap(m_bvSolutionMap);

    }

    bool solve(unsigned int to = 100)
    {
      if (debug >= 1)
      {
        outs() << "\n--- Starting BitHorn Solve Process ---\n";
      }

      bool isSafe = false;

      testBVcom();
      exit(0);

      for (int i = 0; i < to; i++)
      {
        if (debug >= 2)
        {
          outs() << "  Solve iteration: " << i << "\n";
        }

        if (!translateToLia(i > 0))
        {
          outs() << "Error: Failed during BV to LIA translation.\n";
          return false;
        }

        bool liaSolved = solveLIA(to);
        if (!liaSolved)
        {
          if (debug >= 1)
          {
            outs() << "  LIA solver failed to find solution.\n";
            outs() << "  Attempting to strengthen transition relation...\n";
          }
          // return false;
        }

        if (!translateSolutionToBv())
        {
          outs() << "Error: Failed translating LIA solution to BV.\n";
          return false;
        }

        isSafe = checkSafetyInBV();

        if (isSafe)
        {
          outs() << "Success after " << i+1 << " iteration" << (i+1>1 ? "s" : "") << "\n";
          printSolution();
          return true;
        }
        else if (i >= to)
        {
          outs() << "unknown\n";
          break;
        }

        if(debug >= 5) {
          outs() << "  Iteration " << i << " completed. No solution found yet.\n";
          for(auto& b: m_bvSolutionMap) {
            outs() << "    Relation: " << *b.first << "\n";
            outs() << "    Solution: " << *b.second << "\n";
          }
        }

        if(!strengthenTransitionRelation())
        {
          if (debug >= 1)
          {
            outs() << "  Failed to strengthen transition relation.\n";
            outs() << "  Synthesizing alternative invariants...\n";
          }
          // Attempt to synthesize alternative invariants
          // This is a placeholder for the actual synthesis process
          // In a real implementation, this would involve more complex logic
          // to generate new invariants based on the current state of the system
          // For now, we just print a message and exit
          applyAbduction();
        }
        else
        {
          if (debug >= 1)
          {
            outs() << "  Successfully strengthened transition relation.\n";
          }
        }
      }

      outs() << "Failed to find a safe solution after " << to << " iterations.\n";
      return false;
    }

    bool solveLIA(unsigned int to = 100)
    {
      if (debug >= 2)
      {
        outs() << "\n--- Attempting to Solve LIA System ---\n";
      }

      for (auto &rule : m_liaChcs->chcs)
      {
        if (containsOp<IDIV>(rule.body) || containsOp<MOD>(rule.body))
        {
          if (debug >= 1)
          {
            outs() << "  Warning: Skipping rule with division/mod: " << *rule.body << "\n";
          }
          continue;
        }
        Expr normalized_body = normalizeExpr(normalizePositive(rule.body, m_efac, debug));
        rule.body = simplifyArithm(normalized_body, false, false);
      }

      m_liaSolutionMap.clear();

      bool freqs = true;
      bool aggp = false;
      int mut = 1;
      int da = 1;
      bool doDisj = true;
      int mbpEqs = 0;
      bool dAllMbp = true;
      bool dAddProp = false;
      bool dAddDat = true;
      bool dStrenMbp = false;
      int dFwd = 1;
      bool dRec = false;
      bool dGen = true;
      unsigned int maxAttempts = 100;

      std::unique_ptr<RndLearnerV4> solver(new RndLearnerV4(m_efac, m_z3,
        *m_liaChcs, maxAttempts, freqs, aggp, mut, da,
        doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
        dFwd, dRec, dGen, d2, doGJ, doReg, doConnect, debug));

      if (!solver)
      {
        if (debug >= 1)
        {
          outs() << "  Error: Failed to create solver\n";
        }
        return false;
      }

      map<Expr, ExprSet> cands;
      BndExpl bnd(*m_liaChcs, to, debug);

      for (auto &cyc : m_liaChcs->cycles)
      {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++)
        {
          assert(rel == m_liaChcs->chcs[cyc.second[i][0]].srcRelation);

          Expr pref = bnd.compactPrefix(rel, i);
          ExprSet tmp;
          getConj(pref, tmp);

          ExprSet normalizedCandsForRel;
          for (auto &t : tmp)
          {
            Expr normalized_t = normalizeExpr(normalizePositive(t, m_efac, debug));
            Expr simplified_t = simplifyArithm(normalized_t, false, false);
            if (!isOpX<TRUE>(simplified_t) && hasOnlyVars(simplified_t, m_liaChcs->invVars[rel]))
            {
              normalizedCandsForRel.insert(simplified_t);
              if (debug >= 5)
              {
                outs() << "    Added normalized prefix cand for " << *rel << ": " << *simplified_t << "\n";
              }
            }
          }
          cands[rel].insert(normalizedCandsForRel.begin(), normalizedCandsForRel.end());

          if (!solver->initializedDecl(rel))
          {
            solver->initializeDecl(rel);
          }

          if (mut > 0)
          {
            solver->mutateHeuristicEq(cands[rel], cands[rel], rel, true);
            if (debug >= 5)
            {
              outs() << "    Mutated candidates for " << *rel << "\n";
            }
          }
          solver->initializeAux(cands[rel], bnd, rel, i, pref);
        }
      }

      if (da > 0)
      {
        solver->getDataCandidates(cands);
        if (debug >= 4)
        {
          outs() << "  Got data candidates.\n";
        }

        if (debug >= 4)
        {
          outs() << "  Normalizing all candidates (prefix + data + mutated)...\n";
        }
        for (auto &pair : cands)
        {
          Expr rel = pair.first;
          ExprSet &currentCands = pair.second;
          ExprSet finalNormalizedCands;
          for (auto &cand : currentCands)
          {
            Expr normalized_cand = normalizeExpr(normalizePositive(cand, m_efac, debug));
            Expr simplified_cand = simplifyArithm(normalized_cand, false, false);
            if (!isOpX<TRUE>(simplified_cand))
            {
              finalNormalizedCands.insert(simplified_cand);
            }
          }
          currentCands = finalNormalizedCands;
          if (debug >= 5)
          {
            outs() << "    Normalized cands for " << *rel << " (" << currentCands.size() << "):\n";
          }
        }
      }

      for (auto &dcl : m_liaChcs->wtoDecls)
      {
        if (cands.find(dcl) == cands.end())
        {
          cands[dcl] = ExprSet();
        }
        solver->addCandidates(dcl, cands[dcl]);
        solver->prepareSeeds(dcl, cands[dcl]);
      }

      bool bootstrap = solver->bootstrap();
      if (bootstrap)
      {
        if (debug >= 2)
        {
          outs() << "  Bootstrap successful\n";
        }
        processLearnedLiaLemmas(*solver);
        return true;
      }

      solver->calculateStatistics();
      solver->deferredPriorities();
      std::srand(std::time(0));

      if (solver->synthesize(to))
      {
        if (debug >= 2)
        {
          outs() << "  V4 solver found solution via synthesis\n";
        }
        processLearnedLiaLemmas(*solver);
        return true;
      }

      if (debug >= 1)
      {
        outs() << "  LIA solver failed (bootstrap and synthesis)\n";
      }
      return false;
    }

    bool translateSolutionToBv()
    {
      if (debug >= 2)
      {
        outs() << "\n--- Translating LIA Solution to BV ---\n";
      }

      m_bvSolutionMap.clear();

      if (m_bvChcs.decls.empty())
      {
        if (debug >= 1)
        {
          outs() << "  Error: No declarations found in BV CHCs\n";
        }
        return false;
      }

      const auto &bvToLiaMap = m_Bv2LiaTranslator.getBvToLiaDeclMap();

      if (debug >= 4)
      {
        outs() << "  BV to LIA Relation Map (bvToLiaMap):\n";
        for (const auto &pair : bvToLiaMap)
        {
          if (pair.first && pair.second)
          {
            outs() << "    BV: " << *(pair.first) << " -> LIA: " << *(pair.second) << "\n";
          }
          else
          {
            outs() << "    BV: (null?) -> LIA: (null?)\n";
          }
        }
        outs() << "  LIA Solution Map (m_liaSolutionMap):\n";
        for (const auto &pair : m_liaSolutionMap)
        {
          if (pair.first)
          {
            outs() << "    LIA: " << *(pair.first) << " -> " << pair.second.size() << " lemmas\n";
          }
          else
          {
            outs() << "    LIA: (null?) -> " << pair.second.size() << " lemmas\n";
          }
        }
      }

      for (auto &bvDecl : m_bvChcs.decls)
      {
        Expr bvRel = bvDecl->left();
        if (!bvRel)
          continue;

        if (debug >= 4)
        {
          outs() << "  Processing BV relation: " << *bvRel << "\n";
        }

        auto mapIt = bvToLiaMap.find(bvRel);
        if (mapIt == bvToLiaMap.end())
        {
          if (debug >= 1)
          {
            outs() << "  Warning: Could not find LIA relation for BV relation " << *bvRel << " in bvToLiaMap\n";
          }
          continue;
        }
        Expr liaRel = mapIt->second;

        if (debug >= 4)
        {
          outs() << "    Found corresponding LIA relation name: " << *liaRel << "\n";
        }

        auto liaSolnIt = m_liaSolutionMap.find(liaRel);
        if (liaSolnIt == m_liaSolutionMap.end() || liaSolnIt->second.empty())
        {
          if (debug >= 2)
          {
            outs() << "  Warning: No LIA solution found for relation " << *liaRel << " (BV: " << *bvRel << ") in m_liaSolutionMap. Setting to TRUE.\n";
          }
          m_bvSolutionMap[bvRel] = mk<TRUE>(m_efac);
          continue;
        }

        ExprSet &liaExprSet = liaSolnIt->second;
        ExprSet bvExprSet;

        for (auto &liaExpr : liaExprSet)
        {
          if (!liaExpr)
            continue;

          Expr bvExpr = m_Lia2BvTranslator.translateExpr(liaExpr, m_original_bv_width);

          if (!bvExpr)
          {
            if (debug >= 2)
            {
              outs() << "  Warning: Failed to translate LIA expression: " << *liaExpr << " for relation " << *liaRel << "\n";
            }
            continue;
          }

          if (debug >= 4)
          {
            outs() << "    Checking variable maps for BV='" << *bvRel << "' / LIA='" << *liaRel << "'\n";
            outs() << "      m_bvChcs.invVars.count(" << *bvRel << "): " << m_bvChcs.invVars.count(bvRel) << "\n";
            outs() << "      origLiaVars.count(" << *liaRel << "): " << origLiaVars.count(liaRel) << "\n";
            if (m_bvChcs.invVars.count(bvRel))
            {
              outs() << "      BV Vars (" << m_bvChcs.invVars.at(bvRel).size() << "): ";
              for (const auto &v : m_bvChcs.invVars.at(bvRel))
                outs() << *v << " ";
              outs() << "\n";
            }
            if (origLiaVars.count(liaRel))
            {
              outs() << "      LIA Vars (" << origLiaVars.at(liaRel).size() << "): ";
              for (const auto &v : origLiaVars.at(liaRel))
                outs() << *v << " ";
              outs() << "\n";
            }
          }

          if (origLiaVars.count(liaRel) && m_bvChcs.invVars.count(bvRel))
          {
            ExprVector liaVars = origLiaVars.at(liaRel);
            ExprVector bvVars = m_bvChcs.invVars.at(bvRel);

            if (debug >= 4 && liaVars.size() != bvVars.size())
            {
              outs() << "    Warning: LIA var count (" << liaVars.size()
                     << ") != BV var count (" << bvVars.size() << ") for relation " << *liaRel << "\n";
            }

            bvExpr = replaceAll(bvExpr, liaVars, bvVars);
            if (bvExpr)
            {
              if (debug >= 4)
              {
                outs() << "    Translated LIA: " << *liaExpr << "\n";
                outs() << "          to BV (after var replace): " << *bvExpr << "\n";
              }
              bvExprSet.insert(bvExpr);
            }
          }
          else
          {
            if (debug >= 2)
            {
              outs() << "  Warning: Missing variables for relation pair " << *liaRel << "/" << *bvRel << " during translation.\n";
            }
          }
        }

        m_bvSolutionMap[bvRel] = conjoin(bvExprSet, m_efac);
        if (debug >= 3)
        {
          outs() << "  BV Solution for " << *bvRel << ": " << *m_bvSolutionMap[bvRel] << "\n";
        }
      }

      if (debug >= 2)
      {
        outs() << "  Final Translated BV Solution Map (" << m_bvSolutionMap.size() << " entries):\n";
        for (auto &kv : m_bvSolutionMap)
        {
          outs() << "    Relation: " << *kv.first << "\n";
          outs() << "       BV Solution: " << *kv.second << "\n";
        }
        outs() << "\n";
      }

      return !m_bvSolutionMap.empty();
    }

    boost::tribool checkRule(HornRuleExt *hr, map<Expr, ExprSet> &candidates)
    {
      if (debug >= 4)
      {
        outs() << "  Checking rule: " << *hr->srcRelation << " -> " << *hr->dstRelation << "\n";
      }

      ExprVector checkExprs;
      checkExprs.push_back(hr->body);

      if (!hr->isFact)
      {
        auto srcCandIt = candidates.find(hr->srcRelation);
        if (srcCandIt != candidates.end())
        {
          for (auto &cand : srcCandIt->second)
          {
            Expr srcCandSubst = replaceAll(cand, m_bvChcs.invVars[hr->srcRelation], hr->srcVars);
            checkExprs.push_back(srcCandSubst);
          }
        }
      }

      if (!hr->isQuery)
      {
        auto dstCandIt = candidates.find(hr->dstRelation);
        ExprVector negged;
        if (dstCandIt != candidates.end())
        {
          for (auto &cand : dstCandIt->second)
          {
            Expr dstCandSubst = replaceAll(cand, m_bvChcs.invVars[hr->dstRelation], hr->dstVars);
            negged.push_back(mkNeg(dstCandSubst));
          }
        }
        checkExprs.push_back(disjoin(negged, m_efac));
      }

      if (debug >= 5)
      {
        outs() << "    Checking expressions:\n";
        for (int i = 0; i < checkExprs.size(); i++)
        {
          if (i != 0)
            outs() << "    /\\ ";
          else
            outs() << "    ";
          outs() << *checkExprs[i] << "\n";
        }
      }

      boost::tribool res = u.isSat(checkExprs);

      if (debug >= 5)
      {
        if (res == true)
        {
          outs() << "    Rule failed: " << *hr->srcRelation << " -> " << *hr->dstRelation << "\n";
        }
        else if (res == false)
        {
          outs() << "    Rule passed: " << *hr->srcRelation << " -> " << *hr->dstRelation << "\n";
        }
        else
        {
          outs() << "    Rule indeterminate: " << *hr->srcRelation << " -> " << *hr->dstRelation << "\n";
        }
      }

      return res;
    }

    bool checkAllOver(vector<HornRuleExt *> &worklist,
                      map<Expr, ExprSet> &candidates)
    {
      if (debug >= 4)
      {
        outs() << "  Checking for progress...\n";
      }
      for (auto *hr : worklist)
      {
        boost::tribool res = checkRule(hr, candidates);
        if (res || indeterminate(res))
        {
          return false;
        }
      }
      return true;
    }

    bool multiHoudini(vector<HornRuleExt *> &worklist,
                      map<Expr, ExprSet> &candidates)
    {
      if (debug >= 4)
      {
        outs() << "  Checking " << worklist.size() << " rules (multiHoudini)\n";
      }

      bool checkAgain = false;
      for (auto *hr : worklist)
      {
        if (hr->isQuery)
          continue;
        if (candidates[hr->dstRelation].empty())
          continue;
        boost::tribool res = checkRule(hr, candidates);

        if (res || indeterminate(res))
        {
          weakenCandidates(hr, candidates);
          checkAgain = true;
        }
      }

      if (checkAgain)
      {
        if (debug >= 4)
        {
          outs() << "  Candidates weakened, rechecking (multiHoudini)...\n";
        }
        return multiHoudini(worklist, candidates);
      }

      return checkAllOver(worklist, candidates);
    }

    void weakenCandidates(HornRuleExt *hr, map<Expr, ExprSet> &candidates)
    {
      if (debug >= 4)
      {
        outs() << "  Starting candidate weakening\n";
      }

      map<Expr, ExprSet> resCands;
      for (auto &kv : candidates)
      {
        Expr rel = kv.first;
        ExprSet &cands = kv.second;

        for (auto &cand : cands)
        {
          if (debug >= 4)
          {
            outs() << "    Checking candidate: " << *cand << "\n";
          }
          map<Expr, ExprSet> tmpCands;
          tmpCands[rel].insert(cand);
          boost::tribool res = checkRule(hr, tmpCands);

          if (res || indeterminate(res))
          {
            if (debug >= 4)
            {
              outs() << "    Candidate failed: " << *cand << " 🔥\n";
            }
          }
          else
          {
            resCands[rel].insert(cand);
          }
        }
      }

      candidates = resCands;
      if (debug >= 4)
      {
        outs() << "  Candidate weakening complete\n";
      }
    }

    bool assembleAndCheck(Expr cand, bool checkSafety = false)
    {
      if (debug >= 5)
      {
        outs() << "\n--- Starting Safety Check in BV ---\n";
      }

      vector<HornRuleExt *> allRules;
      for (auto &hr : m_bvChcs.chcs)
      {
        if(!hr.isQuery) { allRules.push_back(&hr); }
        if(checkSafety && hr.isQuery) { allRules.push_back(&hr); }
      }

      map<Expr, ExprSet> candidates;
      for (const auto &kv : m_bvSolutionMap)
      {
        ExprSet candSet;
        getConj(kv.second, candSet);
        if(cand != mk<TRUE>(m_efac)) 
        { 
          ExprSet tmpSet;
          getConj(cand, tmpSet);
          candSet.insert(tmpSet.begin(), tmpSet.end());
        }
        candidates[kv.first] = candSet;
      }

      bool res = multiHoudini(allRules, candidates);

      for (const auto &kv : candidates)
      {
        m_bvSolutionMap[kv.first] = conjoin(kv.second, m_efac);
      }

      if (res)
      {
        if (debug >= 5)
        {
          outs() << "  PASSED with initial candidates\n";
        }
        return true;
      }

      bool finalResult = multiHoudini(allRules, candidates);
      if (debug >= 5)
      {
        if (finalResult)
        {
          outs() << "  System is safe after weakening\n";
        }
        else
        {
          outs() << "  System remains unsafe after weakening\n";
        }
      }

      return finalResult;
    }

    bool checkSafetyInBV()
    {
      return assembleAndCheck(mk<TRUE>(m_efac), true);
      // if (debug >= 2)
      // {
      //   outs() << "\n--- Starting Safety Check in BV ---\n";
      // }

      // vector<HornRuleExt *> allRules;
      // for (auto &hr : m_bvChcs.chcs)
      // {
      //   allRules.push_back(&hr);
      // }

      // map<Expr, ExprSet> candidates;
      // for (const auto &kv : m_bvSolutionMap)
      // {
      //   ExprSet candSet;
      //   getConj(kv.second, candSet);
      //   candidates[kv.first] = candSet;
      // }

      // bool res = multiHoudini(allRules, candidates);

      // for (const auto &kv : candidates)
      // {
      //   m_bvSolutionMap[kv.first] = conjoin(kv.second, m_efac);
      // }

      // if (res)
      // {
      //   if (debug >= 1)
      //   {
      //     outs() << "  System is safe with initial candidates\n";
      //   }
      //   return true;
      // }

      // bool finalResult = multiHoudini(allRules, candidates);
      // if (debug >= 1)
      // {
      //   if (finalResult)
      //   {
      //     outs() << "  System is safe after weakening\n";
      //   }
      //   else
      //   {
      //     outs() << "  System remains unsafe after weakening\n";
      //   }
      // }

      // return finalResult;
    }

    bool strengthenTransitionRelation()
    {
      if (debug >= 2)
      {
        outs() << "\n--- Strengthening Transition Relation ---\n";
      }

      for (auto &hr : m_bvChcs.chcs)
      {
        if (hr.isQuery ||hr.isFact)
          continue;

        auto it = m_bvSolutionMap.find(hr.dstRelation);
        if (it == m_bvSolutionMap.end())
          continue;

        Expr dstSolnExpr = it->second;

        ExprSet newBody;
        if (m_bvChcs.invVars.count(hr.dstRelation))
        {
          ExprVector &invVars = m_bvChcs.invVars.at(hr.dstRelation);
          ExprVector &srcVars = hr.srcVars;

          if (invVars.size() == srcVars.size())
          {
            Expr dstSolnSubst = replaceAll(dstSolnExpr, invVars, srcVars);
            newBody.insert(dstSolnSubst);
          }
          else
          {
            if (debug >= 1)
            {
              outs() << "  Warning: Variable count mismatch for rule involving " << *hr.dstRelation
                     << ". Invariant vars (" << invVars.size() << ") vs Destination vars (" << srcVars.size() << ").\n";
            }
          }
        }
        else
        {
          if (debug >= 2)
          {
            outs() << "  Warning: Missing invVars for " << *hr.dstRelation << ".\n";
          }
        }

        Expr newBodyExpr = conjoin(newBody, m_efac);
        if (debug >= 3)
        {
          outs() << "  Strengthening rule for " << *hr.dstRelation << " with: " << newBodyExpr << "\n";
        }

        if(newBodyExpr == mk<TRUE>(m_efac))
        {
          if (debug >= 2)
          {
            outs() << "  Warning: New body is TRUE for rule " << *hr.dstRelation << "\n";
          }
          return false;
        }
        newBody.insert(hr.body);
        newBodyExpr = conjoin(newBody, m_efac);
        hr.body = newBodyExpr;
      }

      if (debug >= 3)
      {
        outs() << "  Strengthened BV system:\n";
        m_bvChcs.print(true);
      }

      return true;
    }

    void printSolution()
    {
      printBvSolutionMap(m_bvSolutionMap);
    }

    Expr abduce(Expr goal, Expr assm)
    {
      if (debug >= 2)
      {
        outs() << "\n--- Starting Abduction Process ---\n";
        outs() << "  Goal: " << *goal << "\n";
        outs() << "  Assumption: " << *assm << "\n";
      }

      ExprFactory &efac = goal->getFactory();
      SMTUtils u(efac);
      ExprSet complex;
      findComplexNumerics(assm, complex);
      findComplexNumerics(goal, complex);
      
      if (debug >= 3)
      {
        outs() << "  Found " << complex.size() << " complex numeric expressions to replace\n";
        if (debug >= 4)
        {
          for (auto &expr : complex)
          {
            outs() << "    Complex expr: " << *expr << "\n";
          }
        }
      }
      
      ExprMap repls;
      ExprMap replsRev;
      for (auto &a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>("__repl_" + lexical_cast<string>(repls.size()), efac));
        repls[a] = repl;
        replsRev[repl] = a;
        
        if (debug >= 5)
        {
          outs() << "    Replacing: " << *a << " with " << *repl << "\n";
        }
      }
      
      Expr goalTmp = replaceAll(goal, repls);
      Expr assmTmp = replaceAll(assm, repls);
      
      if (debug >= 4)
      {
        outs() << "  Simplified goal: " << *goalTmp << "\n";
        outs() << "  Simplified assumption: " << *assmTmp << "\n";
      }

      ExprSet vars;
      filter(assmTmp, bind::IsConst(), inserter(vars, vars.begin()));
      
      if (debug >= 3)
      {
        outs() << "  Eliminating quantifiers over " << vars.size() << " variables\n";
      }
      
      Expr tmp = mkNeg(eliminateQuantifiers(mkNeg(mk<IMPL>(assmTmp, goalTmp)), vars));
      tmp = replaceAll(tmp, replsRev);
      
      if (debug >= 2)
      {
        outs() << "  Raw abduction result: " << *tmp << "\n";
      }

      if (isOpX<FALSE>(tmp))
      {
        if (debug >= 1)
        {
          outs() << "  Abduction failed: result is FALSE\n";
        }
        return NULL; // abduction unsuccessful
      }

      // sanity check:
      if (!u.implies(mk<AND>(tmp, assm), goal))
      {
        if (debug >= 1)
        {
          outs() << "  WARNING: Abduction failed sanity check: " << *mk<AND>(tmp, assm) 
                 << "\n  does not imply\n  " << *goal << "\n";
        }
        return NULL;
      }
      
      if (debug >= 2)
      {
        outs() << "  Abduction successful: " << *tmp << "\n";
      }
      
      return tmp;
    }
    // inline static Expr abduce(Expr goal, Expr assm)
    // {
    //   ExprFactory &efac = goal->getFactory();
    //   SMTUtils u(efac);
    //   ExprSet complex;
    //   findComplexNumerics(assm, complex);
    //   findComplexNumerics(goal, complex);
    //   ExprMap repls;
    //   ExprMap replsRev;
    //   for (auto &a : complex)
    //   {
    //     Expr repl = bind::intConst(mkTerm<string>("__repl_" + lexical_cast<string>(repls.size()), efac));
    //     repls[a] = repl;
    //     replsRev[repl] = a;
    //   }
    //   Expr goalTmp = replaceAll(goal, repls);
    //   Expr assmTmp = replaceAll(assm, repls);

    //   ExprSet vars;
    //   filter(assmTmp, bind::IsConst(), inserter(vars, vars.begin()));
    //   Expr tmp = mkNeg(eliminateQuantifiers(mkNeg(mk<IMPL>(assmTmp, goalTmp)), vars));
    //   tmp = replaceAll(tmp, replsRev);

    //   if (isOpX<FALSE>(tmp))
    //     return NULL; // abduction unsuccessful

    //   // sanity check:
    //   if (!u.implies(mk<AND>(tmp, assm), goal))
    //   {
    //     errs() << "WARNING: abduction fail: " << *mk<AND>(tmp, assm) << "   does not imply " << *goal << "\n";
    //     return NULL;
    //   }
    //   return tmp;
    // }

    void applyAbduction()
    {
        if (debug >= 2)
        {
            outs() << "  Attempting abduction on the transition relation...\n";
        }

        // Construct the transition relation by conjoining the bodies of isFact and isInductive clauses
        ExprSet transitionRelationSet;
        Expr goal = mk<TRUE>(m_efac); // Default to TRUE if no query is found
        for (const auto &hr : m_liaChcs->chcs)
        {
            if (hr.isFact || hr.isInductive)
            {
                transitionRelationSet.insert(hr.body);
            }
            if (hr.isQuery)
            {
                goal = hr.body;
                if (debug >= 2)
                {
                    outs() << "  Found goal from query clause: " << *goal << "\n";
                }
            }
        }
        Expr transitionRelation = conjoin(transitionRelationSet, m_efac);

        // Perform abduction to find a hypothesis
        Expr hypothesis = abduce(goal, transitionRelation);

        if (hypothesis != NULL)
        {
            if (debug >= 2)
            {
                outs() << "  Abduction successful. Hypothesis:\n";
                pprint(hypothesis, 4);
            }

            // Strengthen the transition relation with the abducted hypothesis
            m_bvSolutionMap[mk<TRUE>(m_efac)] = hypothesis;
        }
        else
        {
            if (debug >= 1)
            {
                outs() << "  Abduction failed. No hypothesis generated.\n";
            }
        }
    }
  }; // End BitHorn class

  inline bool learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, bool d2, bool doGJ, 
                               bool doReg, bool doCon, int debug)
  {
    ExprFactory efac;
    EZ3 z3(efac);

    CHCs ruleManager(efac, z3, debug);
    if (!ruleManager.parse(smt, doElim, doArithm))
    {
      outs() << "Error parsing input file\n";
      return 1;
    }

    if (!ruleManager.hasBV && !ser)
    {
      outs() << "Input is not in BV format\n";
      return 1;
    }

    BitHorn bh(efac, z3, ruleManager, d2, doGJ, doReg, doCon, debug);

    if (ser)
    {
      if (debug >= 2)
      {
        outs() << "Translating LIA to BV for serialization.\n";
      }
      // Call the newly implemented method
      if (!bh.translateToBv())
      {
        outs() << "Error translating LIA to BV\n";
        return 1;
      }
      // Serialization is now handled inside translateToBv
      if (debug >= 2)
      {
        outs() << "Serialized BV translation\n";
      }
      return 0; // Indicate success
    }

    std::srand(std::time(0));
    return bh.solve(to);
  }
}

#endif