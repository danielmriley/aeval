// DR: Here we introduce Bit Vector capability.

#ifndef BitHorn__HPP__
#define BitHorn__HPP__

#include "RndLearnerV4.hpp"
#include "ufo/ExprTranslations.h"
#include "simpl/SimplificationPasses.hpp"
#include "deep/LIA2BV2.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  static void getCombinations(vector<vector<int>> &in, vector<vector<int>> &out, int pos = 0)
  {
    if (pos == 0)
      out.push_back(vector<int>());
    if (pos == in.size())
      return;

    vector<vector<int>> out2;

    for (auto &a : in[pos])
    {
      for (auto &b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  class BitHorn : public RndLearnerV4
  {
    private:
      int bitWidth;
      int varCnt = 0;
      ExprVector ssaSteps;
      map<Expr, ExprSet> candidates;
      ExprSet propProgress; // for stats
      Expr invDecl;

    public:
      BitHorn(CHCs &_r, unsigned _to, bool _freqs,
                   bool _aggp, int _mu, int _da, bool _d, int _m, bool _dAllMbp,
                   bool _dAddProp, bool _dAddDat, bool _dStrenMbp, int _dFwd,
                   bool _dR, bool _dG, int _debug) : 
        RndLearnerV4(_r.m_efac, _r.m_z3, _r, _to, _freqs, _aggp, _mu, _da, _d, _m, _dAllMbp,
                    _dAddProp, _dAddDat, _dStrenMbp, _dFwd, _dR, _dG, _debug) { invDecl = _r.chcs[0].dstRelation; }

      BitHorn(CHCs &r, int debug = 0) : BitHorn(r, 2000000, false, false, 1, 0, false, 1,
                                           false, false, false, false, 1, false, false, debug) {}

      void getSolution(ExprMap &e, bool simplify = true)
      {
        if(printLog >= 3)
        {
          outs() << "Getting solution\n";
          outs() << "Decl: " << invDecl << "\n";
          outs() << "decls.size(): " << decls.size() << "\n";
          for(auto& d: decls)
            outs() << "Decl: " << d << "\n";
        } 

        e.clear();
        outs() << "e.size(): " << e.size() << "\n";
        int invIndex = getVarIndex(invDecl, decls);
        ExprSet llms = getlearnedLemmas(invIndex);

        if(printLog >= 3) outs() << "Got " << llms.size() << " lemmas\n";
        u.removeRedundantConjuncts(llms);
        if(printLog >= 3) outs() << "After removing redundant lemmas: " << llms.size() << "\n";
        
        ExprSet llmsSimplified;
        for(auto& a : llms)
        {
          Expr tmp = ineqReverter(a);
          llmsSimplified.insert(tmp);
        }
        llms = llmsSimplified;
        if(printLog >= 3)
        {
          outs() << "Printing learned lemmas\n";
          for(auto& a : llms)
            outs() << a << "\n";
        } 
        candidates[invDecl].insert(llms.begin(), llms.end());
        // for (auto &a : llms)
        // {
          ExprSet sol = llms;
          if (simplify) // we might need more lemmas from the solution (while generalizing later)
            u.removeRedundantConjuncts(sol);
          Expr tmp = simplifyArithm(conjoin(sol, m_efac));
          e[invDecl] = tmp;
        // }
        outs() << "e.size(): " << e.size() << "\n";
      }

      bool checkCHC(HornRuleExt &hr, map<Expr, ExprSet> &annotations)
      {
        if(printLog >= 3) outs() << "Checking CHC with rel: " << hr.srcRelation << " -> " << hr.dstRelation << "\n";
        // if(hr.srcRelation == mk<TRUE>(m_efac))
        //   return false;
        
        ExprSet checkList;
        checkList.insert(hr.body);
        Expr overBody;
        Expr rel = hr.srcRelation;
        ExprSet lms = annotations[rel];
        overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars);
        getConj(overBody, checkList);
        
        if(printLog >= 3) outs() << "Checking CHC with " << annotations[rel].size() << " invariants\n";

        if (!hr.isQuery)
        {
          rel = hr.dstRelation;
          ExprSet negged;
          ExprSet lms = annotations[rel];
          for (auto a : lms)
            negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
          checkList.insert(disjoin(negged, m_efac));
        }
        if(printLog >= 3)
        {
          outs() << "CheckList: ";
          for(auto& a : checkList)
            outs() << a << "  ";

          outs() << "\n";
        }
        return bool(!u.isSat(checkList));
      }

      bool checkQuery (map<Expr, Expr>& candidateInvariants)
      {
        if(printLog >= 3) outs() << "Checking query\n";
        HornRuleExt query;
        for(auto& hr: ruleManager.chcs) 
        {
          if(hr.isQuery) query = hr;
        }
        map<Expr, ExprSet> tmp;
        for (auto const &entry : candidateInvariants)
        {
          tmp.insert(std::make_pair(entry.first, ExprSet{entry.second}));
        }
        if(printLog >= 3) outs() << "Checking query with " << candidateInvariants.size() << " invariants\n";  
        return checkCHC(query, tmp);
      }

      bool filterAndSolve(map<Expr, ExprSet> _candidates, bool checkQuery = true)
      {
        if(printLog >= 3)
        {
          outs() << "Candidates passed here:\n";
          for (auto& entry : _candidates) {
            outs() << entry.first << " - " << entry.second.size() << ":\n";
            for (auto& expr : entry.second) {
              outs() << expr << '\n';
            }
            outs() << "\n";
          }
        }
        setCandidates(_candidates);
        vector<HornRuleExt *> worklist;
        for (auto &hr : ruleManager.chcs)
          worklist.push_back(&hr); // todo: wto

        multiHoudini(worklist);
        
        if(printLog >= 3)
        {
          outs() << "After Houdini " << candidates.size() << '\n';
          for (auto& entry : candidates) {
            outs() << entry.first << " - " << entry.second.size() << ":\n";
            for (auto& expr : entry.second) {
              outs() << expr << '\n';
            }
            outs() << "\n";
          }
        }
        return checkAllOver(checkQuery);
      }

      void setCandidates(map<Expr, ExprSet> _candidates) 
      { 
        this->candidates = std::move(_candidates); 
        if(printLog >= 3)
        {
          outs() << "Candidates set\n";
          for (auto& entry : candidates) {
            outs() << entry.first << " - " << entry.second.size() << ":\n";
            for (auto& expr : entry.second) {
              outs() << expr << '\n';
            }
            outs() << "\n";
          }
        }
      }
      void setCandidates(ExprMap const &_candidates)
      {
        map<Expr, ExprSet> tmp;
        for (auto &entry : _candidates)
        {
          tmp.insert(std::make_pair(entry.first->left(), ExprSet{entry.second}));
        }
        this->candidates = std::move(tmp);
        if (printLog >= 3)
        {
          outs() << "Candidates set\n";
          for (auto &entry : candidates)
          {
            outs() << entry.first << " - " << entry.second.size() << ":\n";
            for (auto &expr : entry.second)
            {
              outs() << expr << '\n';
            }
            outs() << "\n";
          }
        }
      }

      bool checkAllOver (bool checkQuery = false)
      {
        for (auto &hr : ruleManager.chcs)
        {
          if (hr.isQuery && !checkQuery)
            continue;
          if (!checkCHC(hr, candidates))
            return false;
        }
        return true;
      }

      

      Expr quantifierElimination(Expr &cond, ExprSet &vars)
      {
        if (vars.size() == 0)
          return cond;
        Expr newCond;
        if (isNonlinear(cond))
        {
          newCond = simpleQE(cond, vars, true, true);
          if (!u.implies(cond, newCond))
          {
            newCond = mk<TRUE>(m_efac);
          }
        }
        else
        {
          AeValSolver ae(mk<TRUE>(m_efac), cond, vars); // exists quantified . formula
          if (ae.solve())
          {
            newCond = ae.getValidSubset();
          }
          else
          {
            newCond = mk<TRUE>(m_efac);
          }
        }
        return newCond;
      }

      void preproGuessing(Expr e, ExprVector &ev1, ExprVector &ev2, ExprSet &guesses /*, bool useBV=false*/)
      {
        ExprSet ev3;
        filter(e, bind::IsConst(), inserter(ev3, ev3.begin())); // prepare vars
        for (auto it = ev3.begin(); it != ev3.end();)
        {
          if (find(ev1.begin(), ev1.end(), *it) == ev1.end())
            ++it;
          else
            it = ev3.erase(it);
        }
        e = quantifierElimination(e, ev3);
        ExprSet cnjs;

        getConj(e, cnjs);
        for (auto &c1 : cnjs)
        {
          if (isOpX<OR>(c1))
            continue;
          for (auto &c2 : cnjs)
          {
            if (!isOpX<OR>(c2))
              continue;
            ExprSet dsjs;
            ExprSet newDsjs;
            getDisj(c2, dsjs);
            for (auto &d : dsjs)
            {
              if (u.implies(c1, d))
              {
                e = replaceAll(e, c2, mk<TRUE>(m_efac));
                newDsjs.clear();
                break;
              }
              if (!u.implies(mkNeg(c1), d))
                newDsjs.insert(d);
            }
            if (newDsjs.size() > 0)
              e = replaceAll(e, c2, disjoin(newDsjs, m_efac));
          }
        }
        if (ruleManager.hasBV)
        {
          mutateHeuristicBV(replaceAll(e, ev1, ev2), guesses);
        }
        else
        {
          mutateHeuristic(replaceAll(e, ev1, ev2), guesses);
        }
      }

      void bootstrapping()
      {
        for (auto &a : ruleManager.decls)
          propProgress.insert(a->left()); // for stats

        for (auto &hr : ruleManager.chcs)
        {
          if (hr.isQuery)
          {
            if (!containsOp<ARRAY_TY>(hr.body))
            {
              ExprSet vars;
              vars.insert(hr.locVars.begin(), hr.locVars.end());
              Expr q = quantifierElimination(hr.body, vars); // we shouldn't do it here; to fix
              preproGuessing(mkNeg(q), hr.srcVars,
                              ruleManager.invVars[hr.srcRelation], candidates[hr.srcRelation]);
              if (!candidates[hr.srcRelation].empty())
                propProgress.erase(hr.srcRelation); // for stats
            
            }
            continue;
          }

          Expr rel = hr.dstRelation;
          preproGuessing(hr.body, hr.dstVars, ruleManager.invVars[rel], candidates[hr.dstRelation]);
          if (!candidates[hr.dstRelation].empty())
            propProgress.erase(hr.dstRelation); // for stats
        }
      }

      void propagateCandidatesForward()
      {
        for (auto &hr : ruleManager.chcs)
        {
          if (hr.isQuery)
            continue;
          ExprSet all;
          all.insert(hr.body);
          Expr rel = hr.srcRelation;
          // currently, tries all candidates; but in principle, should try various subsets
          for (auto &c : candidates[rel])
            all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars));
        
          preproGuessing(conjoin(all, m_efac), hr.dstVars,
                         ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
        }
      }

      void propagateCandidatesBackward()
      {
        // TODO
      }

      void getImplicationGuesses(map<Expr, ExprSet> &postconds)
      {
        map<Expr, ExprSet> preconds;
        for (auto &r : ruleManager.chcs)
        {
          if (r.isQuery)
            continue;

          int srcRelInd = -1;
          Expr rel = r.dstRelation;
          if (srcRelInd >= 0)
            preproGuessing(r.body, r.srcVars, ruleManager.invVars[rel], preconds[rel]);

          if (srcRelInd == -1)
            continue;
          int tot = 0;
          for (auto guess : postconds[rel])
          {
            if (tot > 5)
              break; // empirically chosen bound
            if (isOpX<IMPL>(guess) || isOpX<OR>(guess))
              continue; // hack

            for (auto &pre : preconds[rel])
            {
              if (u.implies(pre, guess))
                continue;
              tot++;
              Expr newGuess = mk<IMPL>(pre, guess);
              ExprVector tmp;
              tmp.push_back(replaceAll(newGuess, ruleManager.invVars[rel], r.srcVars));
              tmp.push_back(r.body);
              // simple invariant check (for speed, need to be enhanced)
              if (u.implies(conjoin(tmp, m_efac), replaceAll(newGuess, ruleManager.invVars[rel], r.dstVars)))
              {
                candidates[rel].insert(newGuess);
                ExprSet newPost;
                tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[rel], r.dstVars)));
                preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[rel], newPost);
                for (auto &a : newPost)
                {
                  candidates[rel].insert(mk<IMPL>(mk<NEG>(pre), a));
                }
              }
            }
          }
        }
      }

      bool setUp()
      {
        if(printLog >= 3) outs() << "\nSet up BitHorn\n====================\n";
        map<Expr, ExprSet> cands;
        if(printLog >= 3) outs() << "Cycles size: " << ruleManager.cycles.size() << '\n'; 

        for (auto &cyc : ruleManager.cycles)
        {
          Expr rel = cyc.first;
          if(printLog >= 3) outs() << "Rel: " << rel << '\n';
          for (int i = 0; i < cyc.second.size(); i++)
          {
            assert(rel == ruleManager.chcs[cyc.second[i][0]].srcRelation);
            if (initializedDecl(rel))
              continue;
            initializeDecl(rel);
          }
        }

        if(printLog >= 3)
        {
          outs() << "SETUP decls: " << decls.size() << '\n'; 
          for(auto& a : decls)
            outs() << a << '\n';
        }

        return true;
      }

      bool synth(int maxAttempts)
      {
        BndExpl bnd(ruleManager, to, printLog);
        if (!ruleManager.hasCycles())
          return (bool)bnd.exploreTraces(1, ruleManager.chcs.size(), true);

        map<Expr, ExprSet> cands;
        for (auto &cyc : ruleManager.cycles)
        {
          Expr rel = cyc.first;
          for (int i = 0; i < cyc.second.size(); i++)
          {
            assert(rel == ruleManager.chcs[cyc.second[i][0]].srcRelation);
            if (initializedDecl(rel))
              continue;
            initializeDecl(rel);

            Expr pref = bnd.compactPrefix(rel, i);
            ExprSet tmp;
            getConj(pref, tmp);
            for (auto &t : tmp)
              if (hasOnlyVars(t, ruleManager.invVars[rel]))
                cands[rel].insert(t);

            if (mut > 0)
              mutateHeuristicEq(cands[rel], cands[rel], rel, true);
            initializeAux(cands[rel], bnd, rel, i, pref);
          }
        }
        if (dat > 0)
          getDataCandidates(cands);

        for (auto &dcl : ruleManager.wtoDecls)
        {
          for (int i = 0; i < dFwd; i++)
            for (auto &a : cands[dcl])
              propagate(dcl, a, true);
          addCandidates(dcl, cands[dcl]);
          prepareSeeds(dcl, cands[dcl]);
        }

        if (bootstrap())
          return true;

        calculateStatistics();
        deferredPriorities();
        std::srand(std::time(0));
        return synthesize(maxAttempts);
      }

      // very restricted version of FreqHorn (no grammars, limited use of arrays)
      bool guessAndSolve(bool checkQuery = false)
      {
        if(printLog >= 3) outs() << "Bootstrapping..." << std::endl;
        bootstrapping();
        if (printLog >= 3)
        {
          outs() << "\nBootstrapping candidates:" << "\n";
          for (auto& entry : candidates) {
            outs() << *entry.first << " - " << entry.second.size() << ":\n";
            for (auto& expr : entry.second) {
              outs() << *expr << '\n';
            }
            outs() << "\n";
          }
        }

        auto post = candidates;
        filterUnsat();
        if (!ruleManager.hasBV)
          propagateCandidatesForward();

        vector<HornRuleExt *> worklist;
        for (auto &hr : ruleManager.chcs)
          worklist.push_back(&hr); // todo: wto

        multiHoudini(worklist);

        if (printLog >= 3)
        {
          outs() << "\nFirst multiHoudini finished!" << "\n";
          outs() << "After Houdini " << candidates.size() << '\n';
          for (auto& entry : candidates) {
            outs() << *entry.first << " - " << entry.second.size() << ":\n";
            for (auto& expr : entry.second) {
              outs() << *expr << '\n';
            }
            outs() << "\n";
          }
        }

        if (checkAllOver(checkQuery))
        {
          return true;
        }
        if (ruleManager.hasBV)
          return false;

        candidates.clear();
        getImplicationGuesses(post);
        filterUnsat();
        multiHoudini(worklist);
        if (checkAllOver(checkQuery))
        {
          return true;
        }

        candidates.clear();
        // DR: Add arrays back in.
        // for (auto tgt : ruleManager.decls)
        //   arrayGuessing(tgt->left());
        filterUnsat();
        multiHoudini(worklist);
        if (checkAllOver(checkQuery))
        {
          return true;
        }
        return false;
      }

      // naive solving, without invariant generation
      bool solveIncrementally(int unr, ExprVector &rels, vector<ExprVector> &args)
      {
        if (unr > 1000) // hardcoded bound
        {
          outs() << "(maximum bound reached)\n";
          return true;
        }
        else if (rels.empty())
        {
          return false;
        }

        bool res = true;

        // reserve copy;
        auto ssaStepsTmp = ssaSteps;
        int varCntTmp = varCnt;

        vector<vector<int>> availableRules;
        for (int i = 0; i < rels.size(); i++)
        {
          vector<int> available;
          for (auto &b : ruleManager.outgs[rels[i]])
          {
            Expr postcond = ruleManager.getPostcondition(b, args[i]);
            // identifying available rules
            if (u.isSat(postcond, conjoin(ssaSteps, m_efac)))
            {
              available.push_back(b);
            }
          }
          availableRules.push_back(available);
        }
        vector<vector<int>> ruleCombinations;
         (availableRules, ruleCombinations);

        for (auto &c : ruleCombinations)
        {
          ssaSteps = ssaStepsTmp;
          varCnt = varCntTmp;
          ExprVector rels2;
          vector<ExprVector> args2;

          for (int i = 0; i < c.size(); i++)
          {
            // clone all srcVars and rename in the body
            auto &hr = ruleManager.chcs[c[i]];
            Expr body = hr.body;
            if (!hr.dstVars.empty())
              body = replaceAll(body, hr.dstVars, args[i]);
            vector<ExprVector> tmp;
            rels2.push_back(hr.srcRelation);
            ExprVector tmp1;
            for (auto &a : hr.srcVars)
            {
              Expr new_name = mkTerm<string>("_fh_" + to_string(varCnt++), m_efac);
              tmp1.push_back(cloneVar(a, new_name));
            }
            args2.push_back(tmp1);
            body = replaceAll(body, hr.srcVars, tmp1);
            for (auto &a : hr.locVars)
            {
              Expr new_name = mkTerm<string>("_fh_" + to_string(varCnt++), m_efac);
              body = replaceAll(body, a, cloneVar(a, new_name));
            }
          
            ssaSteps.push_back(body);
          }
          if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
          {
            res = res && solveIncrementally(unr + 1, rels2, args2);
          }
        }
        return res;
      }

      // naive solving, without invariant generation
      bool solveIncrementally()
      {
        ExprVector query;
        query.push_back(ruleManager.failDecl);
        vector<ExprVector> empt;
        return solveIncrementally(0, query, empt);
      }

      bool hasQuantifiedCands(map<Expr, ExprSet> &cands)
      {
        for (auto &a : cands)
          for (auto &b : a.second)
            if (containsOp<FORALL>(b))
              return true;

        return false;
      }

      // adapted from RndLearnerV3
      bool multiHoudini(vector<HornRuleExt *> &worklist, bool recur = true)
      {
        if (!anyProgress(worklist))
          return false;
        auto candidatesTmp = candidates;
        bool res1 = true;
        for (auto &hr : worklist)
        {
          if (hr->isQuery)
            continue;

          if (!checkCHC(*hr, candidatesTmp))
          {
            bool res2 = true;
            Expr dstRel = hr->dstRelation;

            Expr model = u.getModel(hr->dstVars);
            if (model == NULL || hasQuantifiedCands(candidatesTmp))
            {
              candidatesTmp[dstRel].clear();
              res2 = false;
            }
            else
            {
              for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end();)
              {
                Expr repl = *it;
                repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

                if (!u.isSat(model, repl))
                {
                  it = candidatesTmp[dstRel].erase(it);
                  res2 = false;
                }
                else
                  ++it;
              }
            }

            if (recur && !res2)
              res1 = false;
            if (!res1)
              break;
          }
        }
        candidates = candidatesTmp;
        if (!recur)
          return false;
        if (res1)
        {
          if (anyProgress(worklist))
          {
            return true;
          }
          else
            return false;
        }
        else
        {
          return multiHoudini(worklist);
        }
      }

      bool anyProgress(vector<HornRuleExt *> &worklist)
      {
        for (auto &a : candidates)
        {
          for (auto &hr : worklist)
          {
            if (a.first != hr->srcRelation || hr->dstRelation == a.first)
            {
              if (!a.second.empty())
                return true;
            }
          }
        }
        return false;
      }

      void addCandidateMap(map<Expr, ExprSet> cands)
      {
        for (auto &c : cands)
        {
          if(printLog >= 3)
          {
            outs() << "Adding candidates for " << *c.first << ":\n";
            for (auto &v : c.second)
              outs() << *v << " ";
            outs() << "\n";
          }
          addCandidates(c.first, c.second);
        }
      }

      // Write a BV version of QE.
      // coreQE check for equisatisfiability with original formula.
      // Start rewriting a QE function. Use simpleQE and coreQE.
      // BV -> simpleQE
      // BV2LIA -> coreQE
      // LIA2BV -> check
      ExprSet getProjections(Expr fla)
      {
        ExprVector prjcts;
        ExprSet res;
        // ExprSet vars;

        // filter(fla, bind::IsConst(), inserter(vars, vars.begin()));
        // AeValSolver ae(mk<TRUE>(m_efac), fla, vars, (printLog > 0));

        // if(ae.solve())
        // {
        //   Expr pr = ae.getValidSubset();
        //   if(printLog >= 3) outs() << "Valid subset: " << pr << "\n";
        // }
        // exit(0);

        u.flatten(fla, prjcts, false, ruleManager.invVars[invDecl], keepQuantifiersRepl);
        for (auto &a : prjcts)
        {
          res.insert(a);
        }

        return res;
      }

      void printSolution(ExprMap llms, bool simplify = true)
      {
        for (int i = 0; i < decls.size(); i++)
        {
          Expr rel = decls[i];
          Expr lms = llms[rel];
          outs() << "(define-fun " << *rel << " (";
          for (auto &b : ruleManager.invVars[rel])
          {
            outs() << "(" << b << " ";
            u.print(typeOf(b));
            outs() << ")";
          }
          outs() << ") Bool\n  ";
          Expr tmp = lms;
          if (simplify && !containsOp<FORALL>(tmp))
            u.removeRedundantConjuncts(lms);
          Expr res = simplifyArithm(lms);
          u.print(res);
          outs() << ")\n";
          assert(hasOnlyVars(res, ruleManager.invVars[rel]));
        }
      }
  };

  void performBV2LIATranslation(CHCs &ruleManager, bool horn, bool serialize, 
    passes::BV1ToBool& cleanup_pass, CHCs& liaRuleManager, passes::BV2LIAPass& bv2lia, 
    CHCs& current, CHCs& lastBVSystem, int printLog = 0)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs original(ruleManager);
    // ruleManager.simplifyCHCSystemSyntactically();
    if (printLog >= 3)
    {
      outs() << "After simplification:\n";
      ruleManager.print(true);
    }
    ruleManager.slice();
    if (printLog >= 3)
    {
      outs() << "After slicing:\n";
      ruleManager.print(true);
    }

    cleanup_pass(ruleManager);
    if (printLog >= 3)
      outs() << "After cleanup:\n";

    current = cleanup_pass.getCHCs();
    if (printLog >= 3)
    {
      outs() << "After cleanup pass:\n";
      current.print(true);
    }

    passes::ITESimplificationPass itepass;
    itepass(current);

    assert(current.hasBV);

    lastBVSystem = current;
    if (printLog >= 3)
    {
      outs() << "Last BV system:\n";
      lastBVSystem.print(true);
    }

    bv2lia(current);
    CHCs *intermediary = bv2lia.getTransformed();
    current = *intermediary;

    if (printLog >= 3)
    {
      outs() << "LIA translation:\n";
      current.print(true);
    }
    if (printLog >= 5)
    {
      outs() << "decls: " << current.decls.size() << '\n';
      for (auto &a : current.decls)
        outs() << a << '\n';

      outs() << "Vars: ";
      for (auto &a : current.invVars)
      {
        for (auto &b : a.second)
          outs() << *b << ' ';
      }

      outs() << "Vars prime: ";
      for (auto &a : current.invVarsPrime)
      {
        for (auto &b : a.second)
          outs() << *b << ' ';
        outs() << "\n";
      }
    }

    if (serialize)
    {
      current.serialize(false);
      exit(0);
    }

    current.serialize(horn);

    
    liaRuleManager.parse("chc.smt2");
    if (printLog >= 3)
    {
      outs() << "After parsing LIA system:\n";
      liaRuleManager.print(true);
    }
  }

  ExprSet qeFromLemmas(CHCs &lastBVSystem, SMTUtils &u, int printLog)
  {
    ExprSet varSet;
    for(auto& v: lastBVSystem.chcs[1].dstVars)
    {
      varSet.insert(v);
    }
    // Expr qeRes = simpleQE(lastBVSystem.chcs[1].body, lastBVSystem.chcs[1].dstVars);
    Expr qeRes = u.quantifierEliminationBV(lastBVSystem.chcs[1].body, varSet);
    ExprSet qeConjs;
    getConj(qeRes, qeConjs);
    if(printLog >= 3)
    {
      outs() << "QE result: " << *qeRes << '\n';
      outs() << "Conjuncts: " << qeConjs.size() << '\n';
      for(auto& a: qeConjs)
      {
        outs() << *a << '\n';
      }
    }

    // now do some translations to perform QE in LIA.
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    passes::BV2LIAPass bv2lia;
    CHCs current(m_efac, z3, printLog);
    CHCs liaRuleManager(m_efac, z3, printLog);
    passes::BV1ToBool cleanup_pass;
    performBV2LIATranslation(lastBVSystem, false, false, cleanup_pass,
      liaRuleManager, bv2lia, current, lastBVSystem, printLog);

    ExprSet liaConjs;
    for(auto& e: qeConjs)
    {
      passes::BV2LIAPass::TranslationResult result = bv2lia.translateGeneralExpression(e);
      liaConjs.insert(result.translated);
    }

    if(printLog >= 3)
    {
      outs() << "LIA conjuncts: " << liaConjs.size() << '\n';
      for(auto& a: liaConjs)
      {
        outs() << a << '\n';
      }
    }

    return liaConjs;
  }

  bool bvSolutionCheck(CHCs &lastBVSystem, ExprMap &translated, map<Expr, ExprSet> &candidates, int printLog)
  {
    for (auto &s : translated)
    {
      ExprSet tmp;
      getConj(s.second, tmp);
      candidates.insert(std::make_pair(bind::fname(s.first), tmp));
    }
    if (printLog >= 3)
    {
      std::cout << "Candidates for BV system:\n";
      outs() << "=============\n";
      for (auto const &entry : candidates)
      {
        std::cout << *entry.first << '\n';
        for (auto const &expr : entry.second)
        {
          std::cout << *expr << '\n';
        }
      }
      outs() << "=============\n";
    }

    if (printLog >= 3)
    {
      outs() << "Last BV System:\n";
      lastBVSystem.print(true);

      outs() << "Setting up BitHorn for BV run\n";
    }

    BitHorn bvsolver(lastBVSystem, printLog);
    bvsolver.setUp();
    bvsolver.setCandidates(candidates);
    if (printLog >= 3) std::cout << "Running filterAndSolve\n" << std::endl;
    bool invariantsFound = bvsolver.filterAndSolve(candidates); // We do not care if the invariant is safe
    if (printLog >= 3) outs() << "filterAndSolve finished " << invariantsFound << std::endl;
    return invariantsFound;
  }

  //DR: A rewrite of the solve function to use the new BitHorn class.
  inline void solve(string smt, bool spacer, bool horn, bool serialize, SMTUtils& u, int printLog = 0)
  {
    const unsigned timeout_seconds = 5;
    const unsigned timeout_milisecs = timeout_seconds * 1000; // in miliseconds
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, printLog);
    ruleManager.parse(smt);
    if (printLog >= 3)
    {
      outs() << "After parsing:\n";
      ruleManager.print(true);
    }

    ExprMap solution; 
    CHCs workingRM(ruleManager);
    map<Expr, ExprSet> candidates;
    while (true)
    {
      passes::BV2LIAPass bv2lia;
      CHCs current(m_efac, z3, printLog);
      CHCs lastBVSystem(m_efac, z3, printLog);
      CHCs liaRuleManager(m_efac, z3, printLog);
      passes::BV1ToBool cleanup_pass;
      performBV2LIATranslation(workingRM, horn, serialize, cleanup_pass,
        liaRuleManager, bv2lia, current, lastBVSystem, printLog);

      // MB: First try to find some useful invariants with FreqHorn
      BitHorn liaSyst(liaRuleManager, printLog);
      liaSyst.setUp();
      liaSyst.setCandidates(candidates);
      candidates.clear();
      solution.clear();
      if (printLog >= 3) std::cout << "Running guessAndSolve\n"<< std::endl;
      const bool invariantFound = liaSyst.synth(1000); // MB: not necessarily safe invariant!
      if (printLog >= 3) outs() << "guessAndSolve finished.." << std::endl;

      // Testing out flatten for projections.
      // ExprSet proj = liaSyst.getProjections(liaRuleManager.chcs[1].body);
      // for(auto& a: proj)
      // {
      //   outs() << "Projection: " << *a << '\n';
      // }
      // exit(0);

      if (!invariantFound)
      {
        outs() << "Synthesize failed\n";
        exit(0);
      }
      liaSyst.getSolution(solution,true);

      for(auto& s: solution)
      {
        s.second = replaceAll(s.second, liaRuleManager.invVars[s.first], current.invVars[s.first]);  
        if (printLog >= 3)
        {
          outs() << "Solution after var replacement: ";
          outs() << *s.first << " - " << *s.second << '\n';
        } 
      }
      // solution contains some invariants that can be used to strengthen the transition relation
      // Translate to BV and check if they are invariants there
      passes::BV2LIAPass::InvariantTranslator invariantTranslator = bv2lia.getInvariantTranslator();
      ExprMap translated = invariantTranslator.translateInvariant(solution);

      // passes::LIA2BVPass lia2bv(liaRuleManager, printLog);
      // lia2bv(liaRuleManager);
      // ExprMap translated;

      // for(auto&s: solution)
      // {
      //   translated[s.first] = lia2bv.translateRecursively(s.second);
      // }

      if (printLog >= 3)
      {
        outs() << "Solution:\n";
        for (auto const &entry : solution)
        {
          std::cout << *entry.first << " - " << *entry.second << '\n';
        }
      }
      
      if (printLog >= 3)
      {
        std::cout << "Translated solution:\n";
        outs() << "=============\n";
        for (auto const &entry : translated)
        {
          std::cout << *entry.first << " - " << *entry.second << '\n';
        }
        outs() << "=============\n";
      }

      for (auto &s : solution)
      {
        // s.second = replaceAll(s.second, liaRuleManager.invVars[s.first], current.invVars[s.first]);
        if (printLog >= 3)
        {
          outs() << "Solution: ";
          outs() << *s.first << " - " << *s.second << '\n';
        }
      }

      {
        bool bvSafe = bvSolutionCheck(lastBVSystem, translated, candidates, printLog);

        if (!bvSafe)
        {
          ExprMap bvInvariants;
          for (auto &t : translated)
          {
            bvInvariants.insert(std::make_pair(t.first->left(), t.second));
          }
          
          // Not Safe invariant, so strengthen and continue
          if (printLog >= 3)
          {
            outs() << "Invariant not safe.\n";
            outs() << "Strengthening with BV invariants\n";
          }
          lastBVSystem.strengthenWithInvariants(bvInvariants);
          if(printLog >= 2)
          {
            outs() << "Strengthened BV system:\n";
            lastBVSystem.print(true);
          } 

          // Experiment with QE here.
          ExprMap qeRes;
          qeRes[(*translated.begin()).first->left()] = conjoin(qeFromLemmas(lastBVSystem, u, printLog), m_efac);

          passes::BV2LIAPass::InvariantTranslator invariantTranslator = bv2lia.getInvariantTranslator();
          ExprMap qeTranslated = invariantTranslator.translateInvariant(qeRes);
          if (printLog >= 10) outs() << "We get here and fail\n";
          for(auto& t: qeTranslated)
          {
            outs() << t.first->left() << " - " << *t.second << '\n';
            candidates[t.first->left()].insert(t.second);
          }
        }
        else
        {
          outs() << "Success! BV Invariant\n";
          for(auto& t: translated)
          {
            outs() << t.first->left() << " - " << *t.second << '\n';
          }
          exit(0);
        }
        workingRM = lastBVSystem;
      }
    }
    exit(0);
  }

  void liaToBv(CHCs& ruleManager, bool horn, int printLog = 0)
  {
    if (printLog >= 1)
    {
      outs() << "LIA 2 BV:\n";
    }
    // Replace old translator with new LIA2BV2 translator
    passes::LIA2BV2 lia2bv(printLog);
    lia2bv(ruleManager);
    
    CHCs *current = lia2bv.getTransformed();
    if(printLog >= 1) current->print(true);
    current->serialize(horn);
  }

  // Test function for LIA2BV2 translations
  inline void testLIA2BV2Translations(ExprFactory &efac, int debug = 0)
  {
    // Create a LIA2BV2 translator instance
    passes::LIA2BV2 translator(debug);

    // Test different types of expressions
    std::vector<std::pair<std::string, Expr>> testCases;

    // Create variables for tests
    Expr x = bind::intConst(mkTerm<string>("x", efac));
    Expr y = bind::intConst(mkTerm<string>("y", efac));
    Expr z = bind::intConst(mkTerm<string>("z", efac));

    // Simple arithmetic
    testCases.emplace_back("x + y", mk<PLUS>(x, y));
    testCases.emplace_back("x - y", mk<MINUS>(x, y));
    testCases.emplace_back("x * y", mk<MULT>(x, y));
    testCases.emplace_back("x / y", mk<IDIV>(x, y));

    // Special cases with negative constants
    testCases.emplace_back("x * (-1)", mk<MULT>(x, mkMPZ(-1, efac)));
    testCases.emplace_back("(-1) * y", mk<MULT>(mkMPZ(-1, efac), y));
    testCases.emplace_back("x - 5", mk<MINUS>(x, mkMPZ(5, efac)));
    testCases.emplace_back("5 - x", mk<MINUS>(mkMPZ(5, efac), x));
    testCases.emplace_back("-x", mk<UN_MINUS>(x));

    // Complex expressions
    testCases.emplace_back("2*x + 3*y - z",
                           mk<MINUS>(
                               mk<PLUS>(
                                   mk<MULT>(mkMPZ(2, efac), x),
                                   mk<MULT>(mkMPZ(3, efac), y)),
                               z));

    testCases.emplace_back("x <= y", mk<LEQ>(x, y));
    testCases.emplace_back("x < y", mk<LT>(x, y));
    testCases.emplace_back("x >= y", mk<GEQ>(x, y));
    testCases.emplace_back("x > y", mk<GT>(x, y));
    testCases.emplace_back("x = y", mk<EQ>(x, y));
    testCases.emplace_back("x != y", mk<NEQ>(x, y));

    // Boolean combinations
    testCases.emplace_back("(x <= y) and (z > 0)",
                           mk<AND>(
                               mk<LEQ>(x, y),
                               mk<GT>(z, mkMPZ(0, efac))));

    // Run the tests
    outs() << "===== LIA2BV2 Translation Tests =====\n";
    for (const auto &test : testCases)
    {
      outs() << "LIA: " << test.first << "\n";
      outs() << "     " << *test.second << "\n";

      Expr translated = translator.translateExpression(test.second, 8); // Use 8-bit width for tests

      outs() << "BV:  " << *translated << "\n\n";
    }
    outs() << "===== Translation Tests Complete =====\n";
  }

  inline void learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    SMTUtils u(m_efac);

    CHCs ruleManager(m_efac, z3, debug - 2);
    ruleManager.parse(smt, doElim, doArithm);

    // testLIA2BV2Translations(m_efac, debug);
    // exit(0);

    if (ser)
    {
      liaToBv(ruleManager, horn, debug); // This now uses LIA2BV2
      exit(0);
    }

    if(!ruleManager.hasBV) {
      outs() << "This is the Bit Vector solver. Use --v4 instead.\n";
      return;
    }
    else if(debug >= 1)
    {
      outs() << "BV system:\n";
    }


    // BV system of CHCs.
    if (debug >= 3)
      ruleManager.print(true);
    
    // Run BitHorn...
    solve(smt, false, horn, serTrans, u, debug);
  }

  

} // Missing closing namespace brace

#endif // BITHORN_HPP