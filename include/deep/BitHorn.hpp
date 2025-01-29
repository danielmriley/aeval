// DR: Here we introduce Bit Vector capability.

#ifndef BitHorn__HPP__
#define BitHorn__HPP__

#include "RndLearnerV4.hpp"
#include "ufo/ExprTranslations.h"
#include "simpl/SimplificationPasses.hpp"

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
        for (auto &a : candidates)
        {
          ExprSet sol = a.second;
          if (simplify) // we might need more lemmas from the solution (while generalizing later)
            u.removeRedundantConjuncts(sol);
          Expr tmp = simplifyArithm(conjoin(sol, m_efac));
          e[a.first] = tmp;
        }
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
          outs() << "Candidates passed here: " << _candidates.size() << '\n';
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

      ExprSet getProjections(Expr fla)
      {
        ExprVector prjcts;
        u.flatten(fla, prjcts, false, ruleManager.invVars[invDecl], keepQuantifiersRepl);
        ExprSet res;
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
  
  // inline void solve(string smt, bool serTrans, int printLog = 0)
  // {
  //   const unsigned timeout_seconds = 5;
  //   const unsigned timeout_milisecs = timeout_seconds * 1000; // in miliseconds
  //   ExprFactory m_efac;
  //   EZ3 z3(m_efac);
  //   CHCs ruleManager(m_efac, z3);
  //   ruleManager.parse(smt);
  //   if (printLog >= 3)
  //     outs() << "After parsing:\n";
  //   ruleManager.print(true);
  //   if (printLog >= 3)
  //     for (auto &e : ruleManager.invVars)
  //     {
  //       outs() << "InvVars for " << *e.first << ":\n";
  //       for (auto &v : e.second)
  //         outs() << *v << " ";
  //       outs() << "\n";
  //     }
  //   CHCs original(ruleManager);
  //   ruleManager.simplifyCHCSystemSyntactically();
  //   if (printLog >= 3)
  //   {
  //     outs() << "After simplification:\n";
  //     ruleManager.print(true);
  //   }
  //   ruleManager.slice();
  //   if (printLog >= 3)
  //   {
  //     outs() << "After slicing:\n";
  //     ruleManager.print(true);

  //   }
  //   passes::BV1ToBool cleanup_pass;
  //   cleanup_pass(ruleManager);
  //   if (printLog >= 3)
  //     outs() << "After cleanup:\n";
  //   CHCs *current = cleanup_pass.getCHCs();
  //      current->print(true);
  //   passes::ITESimplificationPass itepass;
  //   itepass(*current);
  //   if (current->hasBV)
  //   {
  //     CHCs *lastBVSystem = current;
  //     lastBVSystem->print(true);
  //     passes::BV2LIAPass bv2lia;
  //     bv2lia(*current);
  //     current = bv2lia.getTransformed();
  //     if (printLog >= 3)
  //     {
  //       outs() << "LIA translation:\n";
  //       current->print(true);
  //     }
  //     // exit(0);
  //     ExprMap solution;
  //     if (serTrans)
  //     {
  //       current->serialize(false);
  //       exit(0);
  //     }
  //     else
  //     {
  //       current->serialize(false);
  //       // exit(0);

  //       CHCs liaRuleManager(m_efac, z3, printLog);
  //       liaRuleManager.parse("chc.smt2");
  //       if (printLog >= 3)
  //       {
  //         outs() << "After parsing LIA system:\n";
  //         liaRuleManager.print(true);
  //       }
  //       // MB: First try to find some useful invariants with FreqHorn
  //       BitHorn liaSyst(liaRuleManager, printLog);
  //       liaSyst.setUp();
  //       if (printLog >= 3)
  //         std::cout << "Running guessAndSolve\n" << std::endl;
  //       // const bool invariantFound = liaSyst.synth(1000); // MB: not necessarily safe invariant!
  //       const bool invariantFound = liaSyst.guessAndSolve(false); // MB: not necessarily safe invariant!
  //       if(printLog >= 3) outs() << "guessAndSolve finished." << std::endl;
  //       if (invariantFound)
  //       {
  //         liaSyst.getSolution(solution, false);
  //         if(printLog >= 3) outs() << "Solution found" << std::endl;
  //         if (liaSyst.checkQuery(solution))
  //         {
  //           // It is a safe invariant for LIA translation, no need to do additional work on LIA representation
  //           if(printLog >= 3)
  //           {
  //             std::cout << "LIA Solution!" << std::endl;
  //             outs() <<    "=============\n";
  //             for(auto const& entry : solution) {
  //               std::cout << *entry.first << " - " << *entry.second << '\n';
  //             }
  //             outs() << "=============\n";
  //           }
  //         }
  //         else
  //         {
  //           // strengthen and run spacer?
  //           current->strengthenWithInvariants(solution);
  //           auto spacerSolution = current->solve(timeout_milisecs);
  //           if (!spacerSolution.empty())
  //           {
  //             solution = spacerSolution; // MB: or combine them together?
  //           }
  //         }
  //         // solution contains some invariants that can be used to strengthen the transition relation
  //         // Translate to BV and check if they are invariants there
  //         passes::BV2LIAPass::InvariantTranslator invariantTranslator = bv2lia.getInvariantTranslator();
  //         ExprMap translated = invariantTranslator.translateInvariant(solution);
          
  //         if(printLog >= 3)
  //         {
  //           std::cout << "Translated solution:\n";
  //           outs() <<    "=============\n";
  //           for (auto const& entry : translated) {
  //             std::cout << *entry.first << " - " << *entry.second << '\n';
  //           }
  //           outs() << "=============\n";
  //         }
          
  //         {
  //           map<Expr, ExprSet> candidates;
  //           for (auto &s : translated)
  //           {
  //             ExprSet tmp;
  //             getConj(s.second, tmp);
  //             candidates.insert(std::make_pair(bind::fname(s.first), tmp));
  //           }
  //           if(printLog >= 3)
  //           {
  //             std::cout << "Candidates for BV system:\n";
  //             outs() << "=============\n";
  //             for (auto const& entry : candidates) {
  //               std::cout << *entry.first << '\n';
  //               for (auto const& expr : entry.second) {
  //                 std::cout << *expr << '\n';
  //               }
  //             }
  //             outs() << "=============\n";
  //           }
  //           BitHorn bvsolver(*lastBVSystem, printLog);
  //           bvsolver.setUp();
  //           bvsolver.setCandidates(candidates);
  //           if(printLog >= 3)
  //             std::cout << "Running filterAndSolve\n" << std::endl;
  //           bool invariantsFound = bvsolver.filterAndSolve(candidates, false); // We do not care if the invariant is safe
  //           if(printLog >= 3) outs() << "filterAndSolve finished" << std::endl;
  //           if (invariantFound)
  //           {
  //             if(printLog >= 3)
  //             {
  //               outs() << "Invariant found.\n";
  //               for(auto const& entry : candidates) {
  //                 outs() << *entry.first << " - " << entry.second.size() << ":\n";
  //                 for(auto const& expr : entry.second) {
  //                   outs() << *expr << '\n';
  //                 }
  //                 outs() << "\n";
  //               }
  //             }
  //             // BV invariant, let's add it to the transition relations, see if it simplifies anything
  //             ExprMap bvInvariants;
  //             outs() << "get solution from bvsolver\n";
  //             for(auto& t: translated)
  //             {
  //               bvInvariants.insert(std::make_pair(t.first, t.second));
  //             }
  //             // bvsolver.getSolution(bvInvariants);
  //             outs() << "got solution from bvsolver\n";
  //             if (printLog >= 3)
  //             {
  //               std::cout << "BV Solution:\n";
  //               outs() << "BV Solution Size: " << bvInvariants.size() << '\n';
  //               for (auto const& entry : bvInvariants) {
  //                 std::cout << *entry.first << " --> " << *entry.second << '\n';
  //               }
  //             }
  //             // TEST if it is not safe invariant
  //             bvsolver.setCandidates(bvInvariants);
  //             if (bvsolver.checkAllOver(true))
  //             {
  //               std::cout << "Success! Safe Invariant found!" << std::endl;
  //               for(auto const& entry : bvInvariants) {
  //                 std::cout << *entry.first << " - " << *entry.second << '\n';
  //               }
  //               exit(0);
  //             }
  //             // Not Safe invariant, so strengthen and continue
  //             if(printLog >= 3)
  //             {
  //               outs() << "Invariant not safe.\n";
  //               outs() << "Strengthening with BV invariants\n";
  //             }
  //             lastBVSystem->strengthenWithInvariants(bvInvariants);
  //             //              lastBVSystem->print();
  //             auto bvsolution = lastBVSystem->solve(timeout_milisecs);
  //             if (!bvsolution.empty())
  //             {
  //               std::cout << "BV solution found after strengthening with invariants from LIA\n";
  //             }
  //             else
  //             {
  //               std::cout << "UNKNOWN" << std::endl;
  //             }
  //           }
  //           else
  //           {
  //             // No new invariant learnt
  //             std::cout << "UNKNOWN" << std::endl;
  //           }
  //         }
  //       }
  //       else
  //       {
  //         std::cout << "Guess and solve failed!" << std::endl;
  //         // TODO: counterexample (using liaSyst.solveIncrementally)
  //         exit(0);
  //       }
  //       exit(0);
  //     }
  //     if (!solution.empty())
  //     {
  //              std::cout << "Solution in LIA found!\n";
  //              for (auto const& entry : solution) {
  //                std::cout << *entry.first << " - " << *entry.second << '\n';
  //              }
  //       auto invariantTranslator = bv2lia.getInvariantTranslator();
  //       auto translated = invariantTranslator.translateInvariant(solution);
  //              std::cout << "Translated solution:\n";
  //              for (auto const& entry : translated) {
  //                std::cout << *entry.first << " - " << *entry.second << '\n';
  //              }
  //       auto originalSol = cleanup_pass.getInvariantTranslation().getOriginalSolution(translated);
  //       std::map<Expr, ExprSet> candidates;
  //       for (auto &s : originalSol)
  //       {
  //         ExprSet tmp;
  //         getConj(s.second, tmp);
  //         candidates.insert(std::make_pair(bind::fname(s.first), tmp));
  //         //          std::cout << *bind::fname(s.first) << " - " << *s.second << std::endl;
  //       }
  //       BitHorn nonlin(original, printLog);
  //       if (nonlin.filterAndSolve(candidates))
  //       {
  //         std::cout << "Solved!\n";
  //       }
  //       else
  //       {
  //         std::cout << "Some part of invariant does not work\n";
  //       }
  //     }
  //     else
  //     {
  //       std::cout << "LIA Spacer found counterexample" << std::endl;
  //     }
  //   }
  // }

  //DR: A rewrite of the solve function to use the new BitHorn class.
  inline void solve(string smt, bool spacer, bool horn, bool serialize, int printLog = 0)
  {
    const unsigned timeout_seconds = 5;
    const unsigned timeout_milisecs = timeout_seconds * 1000; // in miliseconds
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    if (printLog >= 3)
    {
      outs() << "After parsing:\n";
      ruleManager.print(true);
    }

    CHCs original(ruleManager);
    ruleManager.simplifyCHCSystemSyntactically();
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
    
    passes::BV1ToBool cleanup_pass;
    cleanup_pass(ruleManager);
    if (printLog >= 3) outs() << "After cleanup:\n";

    CHCs *current = cleanup_pass.getCHCs();
    if (printLog >= 3)
    {
      outs() << "After cleanup pass:\n";
      current->print(true);
    }

    passes::ITESimplificationPass itepass;
    itepass(*current);
    
    assert(current->hasBV);

    CHCs *lastBVSystem = current;
    if(printLog >= 3)
    {
      outs() << "Last BV system:\n";
      lastBVSystem->print(true);
    }
    passes::BV2LIAPass bv2lia;
    bv2lia(*current);
    current = bv2lia.getTransformed();
  
    if (printLog >= 3)
    {
      outs() << "LIA translation:\n";
      current->print(true);
    }
    if (printLog >= 5) 
    {
      outs() << "decls: " << current->decls.size() << '\n';
      for(auto& a : current->decls)
        outs() << a << '\n';

      outs() << "Vars: ";
      for(auto& a : current->invVars)
      {
        for(auto& b : a.second)
          outs() << *b << ' ';
      }

      outs() << "Vars prime: ";
      for (auto &a : current->invVarsPrime)
      {
        for (auto &b : a.second)
          outs() << *b << ' ';
        outs() << "\n";
      }
    }

    ExprMap solution;
    if (serialize)
    {
      current->serialize(false);
      exit(0);
    }

    current->serialize(horn);
    // exit(0);
    CHCs liaRuleManager(m_efac, z3, printLog);
    liaRuleManager.parse("chc.smt2");
    if(printLog >= 3)
    {
      outs() << "After parsing LIA system:\n";
      liaRuleManager.print(true);
    }

    // MB: First try to find some useful invariants with FreqHorn
    BitHorn liaSyst(liaRuleManager, printLog);
    liaSyst.setUp();

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

    if (invariantFound)
    {
      liaSyst.getSolution(solution, false);
      if (printLog >= 3)
        outs() << "Solution found" << std::endl;
      if (liaSyst.checkQuery(solution))
      {
        // It is a safe invariant for LIA translation, no need to do additional work on LIA representation
        if (printLog >= 3)
        {
          std::cout << "LIA Solution!" << std::endl;
          outs() << "=============\n";
          for (auto const &entry : solution)
          {
            std::cout << *entry.first << " - " << entry.second << '\n';
          }
          outs() << "=============\n";
        }
      }
    }
    else
    {
      outs() << "Synthesize failed\n";
      exit(0);
    }
    for(auto& s: solution)
    {
      s.second = replaceAll(s.second, liaRuleManager.invVars[s.first], current->invVars[s.first]);  
      if (printLog >= 3) outs() << *s.first << " - " << *s.second << '\n';
    }
    // solution contains some invariants that can be used to strengthen the transition relation
    // Translate to BV and check if they are invariants there
    passes::BV2LIAPass::InvariantTranslator invariantTranslator = bv2lia.getInvariantTranslator();
    ExprMap translated = invariantTranslator.translateInvariant(solution);

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

    {
      map<Expr, ExprSet> candidates;
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
      BitHorn bvsolver(*lastBVSystem, printLog);
      bvsolver.setUp();
      bvsolver.setCandidates(candidates);
      if (printLog >= 3)
        std::cout << "Running filterAndSolve\n"
                  << std::endl;
      bool invariantsFound = bvsolver.filterAndSolve(candidates, false); // We do not care if the invariant is safe
      if (printLog >= 3)
        outs() << "filterAndSolve finished" << std::endl;
      if (invariantFound)
      {
        if (printLog >= 3)
        {
          outs() << "Invariant found.\n";
          for (auto const &entry : candidates)
          {
            outs() << *entry.first << " - " << entry.second.size() << ":\n";
            for (auto const &expr : entry.second)
            {
              outs() << *expr << '\n';
            }
            outs() << "\n";
          }
        }
        // BV invariant, let's add it to the transition relations, see if it simplifies anything
        ExprMap bvInvariants;
        for (auto &t : translated)
        {
          bvInvariants.insert(std::make_pair(t.first, t.second));
        }

        if (printLog >= 3)
        {
          std::cout << "BV Solution:\n";
          outs() << "BV Solution Size: " << bvInvariants.size() << '\n';
          for (auto const &entry : bvInvariants)
          {
            std::cout << *entry.first << " --> " << *entry.second << '\n';
          }
        }
        // TEST if it is not safe invariant
        bvsolver.setCandidates(bvInvariants);
        if (bvsolver.checkAllOver(true))
        {
          std::cout << "Success! Safe Invariant found!" << std::endl;
          ExprMap bvInv;
          for(auto& inv: bvInvariants)
          {
            bvInv[inv.first->left()] = inv.second;
          }
          bvsolver.printSolution(bvInv);
          // for (auto const &entry : bvInvariants)
          // {
          //   std::cout << *entry.first << " - " << *entry.second << '\n';
          // }
          exit(0);
        }
        // Not Safe invariant, so strengthen and continue
        if (printLog >= 3)
        {
          outs() << "Invariant not safe.\n";
          outs() << "Strengthening with BV invariants\n";
        }
        lastBVSystem->strengthenWithInvariants(bvInvariants);
        if(printLog >= 2) lastBVSystem->print(true);
        auto bvsolution = lastBVSystem->solve(timeout_milisecs);
        if (!bvsolution.empty())
        {
          std::cout << "BV solution found after strengthening with invariants from LIA\n";
        }
        else
        {
          std::cout << "UNKNOWN" << std::endl;
        }
      }
      exit(0);
    }
  }

  void liaToBv(CHCs& ruleManager, bool horn, int printLog = 0)
  {
    if (printLog >= 1)
    {
      outs() << "LIA 2 BV:\n";
    }
    passes::LIA2BVPass lia2bv(ruleManager, printLog);
    lia2bv(ruleManager);
    
    CHCs *current = lia2bv.getTransformed();
    if(printLog >= 1) current->print(true);
    current->serialize(horn);
    // ruleManager.print(true);
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

    if(ser)
    {
      liaToBv(ruleManager, horn, debug);
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
    solve(smt, false, horn, serTrans, debug);
  }
}

#endif