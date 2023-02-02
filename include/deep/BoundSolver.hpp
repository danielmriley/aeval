#ifndef BOUNDSOLVER_HPP
#define BOUNDSOLVER_HPP

#include "Horn.hpp"
#include "DataLearner.hpp"
#include "DataLearner2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};

  class BoundSolver
  {
  private:

    ExprFactory &m_efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;

    HornRuleExt* tr; // This should be a vector to handle multiple loops.
    HornRuleExt* fc;
    HornRuleExt* qr;

    ExprVector decls;

    HornRuleExt tr_orig;    // for phases

    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
    int invVarsSz;
    int phaseNum = 0;
    bool hasArrays = false;

    string specName = "pre";
    string varName = "_FH_";
    string ghostVar_pref = "_gh_";
    Expr specDecl;
    ExprVector ghostVars;
    ExprVector ghostVarsPr;
    Expr decGhost0;
    Expr decGhost1;
    Expr ghost0Minus1;
    Expr ghost1Minus1;
    Expr ghostAss;
    Expr ghostGuard;
    Expr ghostGuardPr;
    Expr loopGuard;
    Expr loopGuardPr;
    Expr fcBodyInvVars;
    ExprSet bounds;
    ExprSet concrtBounds;
    ExprSet dataGrds;
    ExprVector phases;
    Expr mpzZero;
    vector<pair<Expr, Expr>> phasePairs;
    vector<ExprVector> paths;
    ExprMap stren, grds2gh, fgrds2gh; // associate a guard (phi(vars)) with a precond of gh (f(vars))


    string SYGUS_BIN;
//    int globalIter = 0;
    int strenBound;
    int debug = 0;

    bool hornspec = false;
    bool dg = false;
    bool data2 = false;
    bool doPhases = false;

  public:

    BoundSolver (CHCs& r, int _b, bool _dg, bool d2, bool _dp, int dbg = 0)
      : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b), SYGUS_BIN(""),
        z3(m_efac), smt(z3), dg(_dg), data2(d2), doPhases(_dp), debug(dbg)
    {
      specDecl = mkTerm<string>(specName, m_efac);
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else fc = &a;
      tr_orig = *tr;
      for(auto& dcl: ruleManager.decls) decls.push_back(dcl->left());
      invDecl = tr->srcRelation;
      invVars = tr->srcVars;
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();
      mpzZero = mkMPZ(0, m_efac);
    }

    bool setUpCounters()
    {
      if(debug >= 3) outs() << "setUpCounters\n";
      for (int i = 0; i < 2; i++)
      {
        Expr new_name = mkTerm<string> (ghostVar_pref + to_string(i), m_efac);
        Expr var = bind::intConst(new_name);
        ghostVars.push_back(var);

        new_name = mkTerm<string> (ghostVar_pref + to_string(i) + "'", m_efac);
        var = bind::intConst(new_name);
        ghostVarsPr.push_back(var);
      }

      ghost0Minus1 = mk<MINUS>(ghostVars[0], mkTerm (mpz_class (1), m_efac));
      ghost1Minus1 = mk<MINUS>(ghostVars[1], mkTerm (mpz_class (1), m_efac));
      decGhost0 = mk<EQ>(ghostVarsPr[0], ghost0Minus1);
      decGhost1 = mk<EQ>(ghostVarsPr[1], ghost1Minus1);
      ghostAss = mk<LT>(ghostVars[0], mkTerm (mpz_class (0), m_efac));
      ghostGuard = mk<NEQ>(ghostVars[0], mkTerm (mpz_class (0), m_efac));
      ghostGuardPr = mk<NEQ>(ghostVarsPr[0], mkTerm (mpz_class (0), m_efac));

      return true;
    }

    void replaceRule(HornRuleExt* hr, HornRuleExt* rule)
    {
      rule->srcRelation = hr->srcRelation;
      rule->srcVars = hr->srcVars;
      rule->dstRelation = hr->dstRelation;
      rule->dstVars = hr->dstVars;
      rule->isFact = hr->isFact;
      rule->isInductive = hr->isInductive;
      rule->isQuery = hr->isQuery;
      rule->body = hr->body;
    }

    void replaceRule(HornRuleExt* hr) {
      for(auto& rule: ruleManager.chcs) {
        if(!hr->isInductive && !hr->isQuery && !rule.isInductive && !rule.isQuery) {
          replaceRule(hr,&rule);
        }
        else if(hr->isInductive && rule.isInductive) {
          replaceRule(hr,&rule);
        }
        else if(hr->isQuery && rule.isQuery) {
          replaceRule(hr,&rule);
        }
      }
    }

    void specUpFc()
    {
      HornRuleExt* fc_new = new HornRuleExt();
      fc_new->srcRelation = specDecl;
      fc_new->srcVars.clear();
      fc_new->dstRelation = fc->dstRelation;
      fc_new->dstVars = fc->dstVars;
      fc_new->dstVars.push_back(ghostVarsPr[0]);
      fc_new->isFact = false;
      ExprVector specVars;
      ExprVector specVarsPr;
      for(int i = 0; i < invVars.size(); i++) {
        specVars.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()), m_efac)));
        specVarsPr.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()) + "'", m_efac)));
      }
      fc_new->srcVars = specVars;
      ExprSet fc_body;
      for(int i = 0; i < specVars.size(); i++) {
        fc_body.insert(mk<EQ>(specVars[i], invVarsPr[i]));
      }

      fc_body.insert(replaceAll(fc->body, invVarsPr, specVars));
      fc_body.insert(mk<EQ>(ghostVars[1], ghostVarsPr[0]));

      fc_new->body = conjoin(fc_body, m_efac);
      if(debug >= 3) outs() << "fc_new body: " << fc_new->body << "\n";
      fc_new->srcVars.push_back(ghostVars[1]);
      specVars = fc_new->srcVars;
      ruleManager.invVars[specDecl].clear();
      ruleManager.addDeclAndVars(specDecl,specVars);

      replaceRule(fc_new);

      fcBodyInvVars = fc_new->body;
      ExprSet temp;
      getConj(fcBodyInvVars,temp);
      bool replaced;
      for(auto e = temp.begin(); e != temp.end(); ) {
        replaced = false;
        for(auto& i: fc_new->dstVars) {
          if(contains(*e, i)) {
            e = temp.erase(e);
            replaced = true;
          }

        }
        if(!replaced) e++;
      }
      fcBodyInvVars = conjoin(temp, m_efac);

      for (auto & a : ruleManager.chcs)   // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
      tr_orig = *tr;

    }

    void setUpTr() // Needs to be rewritten to handle multiple loops.
    {
      HornRuleExt* tr_new = new HornRuleExt();
      tr_new->srcRelation = tr->srcRelation;
      ruleManager.invVars[invDecl].clear();
      tr_new->srcVars = tr->srcVars;
      tr_new->srcVars.push_back(ghostVars[0]);
      invVars.push_back(ghostVars[0]);
      invVarsPr.push_back(ghostVarsPr[0]);
      tr_new->dstRelation = tr->dstRelation;
      tr_new->dstVars = tr->dstVars;
      tr_new->dstVars.push_back(ghostVarsPr[0]);
      tr_new->isInductive = true;
      ruleManager.addDeclAndVars(invDecl,invVars);


      ExprSet tmp;
      getConj(tr->body, tmp);
      tmp.insert(decGhost0);
      tr_new->body = conjoin(tmp, m_efac);
      replaceRule(tr_new);

      fcBodyInvVars = replaceAll(fcBodyInvVars, fc->srcVars, invVars);
      if(debug >= 4) outs() << "fcBodyInvVars: " << fcBodyInvVars << "\n";

      for (auto & a : ruleManager.chcs)    // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
      tr_orig = *tr;
    }

    void setUpQr()
    {
      qr = new HornRuleExt();
      qr->srcRelation = tr->srcRelation; // Need to pick the rel from the last loop.
      qr->srcVars = tr->srcVars;
      qr->body = mk<AND>(mkNeg(loopGuard), ghostGuard);
      qr->dstRelation = mkTerm<string> ("err", m_efac);
      qr->isQuery = true;
      ruleManager.hasQuery = true;

      ruleManager.addFailDecl(qr->dstRelation);
      ruleManager.addRule(qr);

      for (auto & a : ruleManager.chcs)    // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else fc = &a;
      tr_orig = *tr;
    }

    bool setUpQueryAndSpec()
    {
      setUpCounters();

      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isFact) fc = &a;
        else if (a.isQuery) qr = &a;
      tr_orig = *tr;

      invDecl = tr->srcRelation; // Need to handle multiple loops, so this can't be assigned in this way.
      invVars = tr->srcVars;
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();

      if (tr == NULL)
      {
        outs() << "TR is missing\n";
        exit(0);
      }

      if (fc == NULL)
      {
        outs() << "INIT is missing\n";
        exit(0);
      }
      loopGuard = ruleManager.getPrecondition(tr);
      loopGuardPr = replaceAll(loopGuard, invVars, invVarsPr);
      ruleManager.decls.clear();

      specUpFc();
      setUpTr();
      setUpQr();

      return true;
    }

    bool checkAllOver (bool checkQuery = false, bool weak = true,
        Expr src = NULL, Expr dst = NULL)
     {
       for (auto & hr : ruleManager.chcs)
       {
         if (hr.isQuery && !checkQuery) continue;
         if (!checkCHC(hr, candidates)) return false;
       }
      if (weak)
      {
        if (debug >= 1) outs () << "try weakening\n";

        for (auto & a : candidates)
        {
          ExprSet cannot;
          while (true)
          {
            auto it = a.second.begin();
            for (; it != a.second.end();)
            {
              Expr cand = *it;
              if (find(cannot.begin(), cannot.end(), cand) != cannot.end() ||
                  lexical_cast<string>(cand).find("gh") != std::string::npos)  // hack for now
              {
                ++it;
                continue;
              }

              if (u.implies(src, cand))
              {
                ++it;
                continue;
              }

              if (debug >= 5) outs () << "can remove: " << cand << " for " << a.first << "?\n";
              it = a.second.erase(it);
              auto res = checkAllOver(checkQuery, false, src, dst);
              if (debug >= 5)   outs () << "checkAllOver (nest):  " << res << "\n";
              if (!res)
              {
                cannot.insert(cand);
                break;
              }
            }

            auto res = (it == a.second.end());
            a.second.insert(cannot.begin(), cannot.end());
            if (res) break;
          }
        }
      }
       return true;
     }

    bool isSkippable(Expr model, ExprVector vars, map<Expr, ExprSet>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
        for (auto & b : a.second)
          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      if(debug >= 6) {
        if(hr.isQuery) outs() << "Query\n";
        else if(hr.isInductive) outs() << "Inductive\n";
        else outs() << "Pre\n";

      }
      {
        Expr rel = hr.srcRelation;
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars);
        if(debug >= 6) outs() << "overbody: " << overBody << "\n";
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        Expr neg = disjoin(negged, m_efac);
        if(debug >= 6) outs() << "neg: " << neg << "\n";
        checkList.insert(neg);
      }
      if(debug >= 6) { outs() << "checkList:\n"; pprint(checkList, 2); }
      auto res = bool(!u.isSat(checkList));
      return res;
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist) // if problems look here.
          if (hr->srcRelation == a.first || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    void filterUnsat() // Maybe the rndv3 version can be adapted?
    {
     vector<HornRuleExt*> worklist;
     for (auto & a : candidates)
       if (!u.isSat(a.second)) {
         for (auto & hr : ruleManager.chcs)
           if (hr.dstRelation == a.first && hr.isFact)
             worklist.push_back(&hr);
       }

     multiHoudini(worklist, false);

     for (auto & a : candidates)
     {
       if (!u.isSat(a.second))
       {
         ExprVector tmp;
         ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
         u.splitUnsatSets(a.second, tmp, stub);
         a.second.clear();
         a.second.insert(tmp.begin(), tmp.end());
       }
     }
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) {
        if(debug >= 5) outs() << "No progress\n";
        return false;
      }
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;

        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (isSkippable(model, hr->dstVars, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) { it = candidatesTmp[dstRel].erase(it); res2 = false; }
              else ++it;
            }
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    // adapted from BndExpl:: getAllTraces
    bool getAllPaths (Expr src, Expr dst, int len, ExprVector trace, vector<ExprVector>& traces)
    {
      if (len == 1)
      {
        for (auto a : phasePairs)
        {
          if (a.first == src && a.second == dst)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if(debug >= 1)
                  outs () << "cyclic paths not supported\n";
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(dst);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : phasePairs)
        {
          if (a.first == src)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if(debug >= 1)
                  outs () << "cyclic paths not supported\n";
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(a.second);
            bool  res = getAllPaths(a.second, dst, len-1, newtrace, traces);
            if(!res) return false;
          }
        }
      }

      return true;
    }

    void getCombs(ExprVector& elems, int pos, vector<ExprVector>& res)
    {
      if (pos == 0)
      {
        res = {{elems[0]}, {mkNeg(elems[0])}};
      }
      else
      {
        vector<ExprVector> res2;
        for (auto comb : res)
        {
          comb.push_back(elems[pos]);
          res2.push_back(comb);
          comb.back() = mkNeg(elems[pos]);
          res2.push_back(comb);
        }
        res = res2;
      }
      if (pos + 1 < elems.size())
        getCombs(elems, pos+1, res);
    }

    void pairPhases() {
      Expr init = fcBodyInvVars;
      for(auto& p : phases) {
        if(init != p && u.isSat(init, p)) {
          phasePairs.push_back(std::make_pair(init,p));
        }
      }
      for(int i = 0; i < phases.size(); i++) {
        for(int j = 0; j < phases.size(); j++) {
          if(i == j) continue;
          if(u.isSat(tr->body,phases[i],replaceAll(phases[j],invVars,invVarsPr))) {
            phasePairs.push_back(std::make_pair(phases[i],phases[j]));
          }
        }
      }
      for(auto& p : phases) {
        if(!u.isSat(p, tr->body)) {
          phasePairs.push_back(std::make_pair(p,mk<FALSE>(m_efac)));
        }
      }
    }

    bool sortPhases() {
      ExprSet init;
      for(auto & p : phasePairs) {
        if(p.first == fcBodyInvVars) {
          init.insert(p.first);
        }
      }

      // sanity check:
      if (u.implies(fcBodyInvVars, disjoin(init, m_efac)))
      {
        if (debug >= 3) outs () << "Init cases general enough\n";
      }
      else
        assert(0 && "something is wrong in the phase construction");

      for (auto & in : init)
      {
        int len = paths.size();
        for (int i = 1; i <= phasePairs.size() ; i++) {
          bool res = getAllPaths (in, mk<FALSE>(m_efac), i, {in}, paths);
          if(!res) return false;
        }
        assert (paths.size() > len && "No paths found\n");
      }

      if(debug >=4) {
        for (auto & p : paths)
        {
          outs () << "Found path: ";
          for (auto & pp : p)
            outs () << pp << " -> ";
          outs () << "\n";
        }
      }
      if(debug >= 3 || debug == -1)
        outs() << "# of paths " << paths.size() << "\n";

      return true;
    }

    void collectPhaseGuards(bool weakenPhases = false)
    {
      BndExpl bnd(ruleManager, (debug > 0));
      ExprSet cands;
      vector<int>& cycle = ruleManager.cycles[0];
      HornRuleExt* hr = &ruleManager.chcs[cycle[0]];
      Expr rel = hr->srcRelation;
      int invNum = getVarIndex(invDecl, decls);
      ExprVector& srcVars = tr->srcVars;
      ExprVector& dstVars = tr->dstVars;
      assert(srcVars.size() == dstVars.size());
      ExprSet dstVarsSet;
      for(auto& d: dstVars) dstVarsSet.insert(d);
      cycle.pop_back();
      cycle.push_back(1);
      Expr ssa = bnd.toExpr(cycle);

      ssa = replaceAll(ssa, bnd.bindVars.back(), dstVars);
      ssa = rewriteSelectStore(ssa);
      retrieveDeltas(ssa, srcVars, dstVars, cands);

      ExprVector vars2keep, prjcts, prjcts1, prjcts2;
      ExprSet prjctsTmp;
      bool hasArray = false;
      for (int i = 0; i < srcVars.size(); i++) {
        if (containsOp<ARRAY_TY>(srcVars[i]))
        {
          hasArray = true;
          vars2keep.push_back(dstVars[i]);
        }
        else
        {
          vars2keep.push_back(srcVars[i]);
        }
      }

      u.flatten(ssa, prjcts1, false, vars2keep, keepQuantifiersRepl);

      if(weakenPhases)
      {
        for (auto p1 = prjcts1.begin(); p1 != prjcts1.end(); )
        {
          bool changed = false;
          for (auto p2 = prjcts1.begin(); p2 != prjcts1.end(); p2++)
          {
            if (*p1 == *p2) { continue; }
            if (u.implies (*p1, *p2))
            {
              if(debug >= 4) outs () << "  to remove " << *p1 << "\n";
              changed = true;
            }
          }
          if(changed) { p1 = prjcts1.erase(p1); }
          else { p1++; }
        }
      }

      for (auto p : prjcts1)
      {
        if (hasArray)
        {
          p = ufo::eliminateQuantifiers(p, dstVarsSet);
          p = weakenForVars(p, dstVars);
        }
        else
        {
          p = weakenForVars(p, dstVars);
          p = simplifyArithm(normalize(p));
        }
        getConj(p, prjctsTmp);
        if (debug >= 2) outs() << "Generated MBP: " << p << "\n";
      }

      prjcts.insert(prjcts.end(), prjctsTmp.begin(), prjctsTmp.end());
      u.removeRedundantConjunctsVec(prjcts);

      for (auto it = prjcts.begin(); it != prjcts.end();)
      {
        bool toRem = false;
        for (auto it2 = prjcts.begin(); it2 != it; ++it2)
        {
          if (u.isEquiv(*it, mkNeg(*it2)))
          {
            toRem = true;
            break;
          }
        }
        if (toRem)
          it = prjcts.erase(it);
        else
          ++it;
      }

      if (debug >= 2)
      {
        outs() << "Split MBP: \n";
        pprint(prjcts, 3);
      }

      vector<ExprVector> res;
      getCombs(prjcts, 0, res);
      for (auto & r : res)
      {
        phases.push_back(conjoin(r, m_efac));
        if(debug >= 3) {
          outs () << "  comb: ";
          pprint(r);
          outs () << "\n";
        }
      }

      pairPhases();
      if(debug >= 3) {
        outs() << "\n";
        for(auto& v: phasePairs) {
          outs() << "  : "<< v.first << " --> " << v.second << "\n";
        }
        outs() << "\n";
      }
      if (!sortPhases())
      {
        if(!weakenPhases) {
          if(debug >=3) outs() << "Path finding failed. Trying again.\n";
          phasePairs.clear();
          paths.clear();
          phases.clear();
          collectPhaseGuards(true);
        }
        else {
          outs() << "Path finding failed.\n";
          exit(1);
        }
      }
    }

    void parseForGuards() {
      if(debug >= 3) outs() << "Begin parsing for guards\n";
      // get a DNF form if there are disj in the result from G&S.
      ExprVector projections, prjcts, vars2keep;
      Expr pc = ghostVars[0];

      u.flatten(conjoin(candidates[specDecl], m_efac), prjcts, false, vars2keep, [](Expr a, ExprVector& b){return a;});

      for(auto& p : prjcts) {
        projections.push_back(replaceAll(p, fc->srcVars, invVars));
      }
      if(debug >= 3) {
        outs() << "\n   Projections\n=================\n";
        pprint(projections, 3);
        outs() << "=================\n";
      }
      ExprSet t,p,g;
      for(auto e = projections.begin(); e != projections.end() ; e++) {
        t.clear(); p.clear(); g.clear();
        getConj(*e, t);

        ExprSet temp;
        for(auto& a: t) {
          temp.insert(normalize(a));
        }
        t.clear();
        t.swap(temp);
        int c = 0;
        ExprSet toBeRenamed;
        for(auto& ee: t) {
          if(contains(ee,ghostVars[0]) || contains(ee,ghostVars[1])) {
            c++;
            Expr r = replaceAll(ee, fc->srcVars,invVars);

            r = normalize(r, pc);
            if(containsOp<EQ>(r) && r->left() == pc) g.insert(r);
            else toBeRenamed.insert(r);
          }
          else {
            Expr r = replaceAll(ee, fc->srcVars,invVars);
            p.insert(normalize(r));
          }
        }

        Expr join = *g.begin();
        auto i = g.begin(), end = g.end();
        i++;
        for (auto & a : toBeRenamed)
          p.insert(replaceAll(a, pc, join->right()));
        for(;i!=end;i++) {
          join = mk<EQ>(join->right(),(*i)->right());
          join = normalize(join);
          p.insert(join);
        }
        for(auto& d: g) {
          if(isOpX<MPZ>(d->right())) {
            join = d;
            break;
          }
        }

        if (grds2gh[conjoin(p,m_efac)] != NULL)
        {
          assert(0 && "ERROR: guards already assigned\n");
        }
        grds2gh[conjoin(p,m_efac)] = join->right();  // GF: DS
      }
      if(debug >= 3) { outs() << "End parsing for guards\n"; }
    }

    void genCands(ExprSet & tmp, Expr pc)
    {
      Expr v = mkConst(mkTerm<string>("tmp_", m_efac), mk<INT_TY>(m_efac));
      ExprSet newCands;
      for (auto it = tmp.begin(); it != tmp.end(); ++it)
      {
        auto a = *it;
        if (contains(a, pc)) continue;
        if (!isOp<ComparissonOp>(a)) continue;
        a = normalize(a);

        for (auto it2 = std::next(it); it2 != tmp.end(); ++it2)
        {
          auto b = *it2;
          if (a == b) continue;
          if (!isOp<ComparissonOp>(b)) continue;
          b = normalize(b);

          Expr n = mk<AND>(reBuildCmp(a, mk<MINUS>(a->left(), a->right()), v),
                           reBuildCmp(b, mk<MINUS>(b->left(), b->right()), v));
          newCands.insert(eliminateQuantifier(n, v));
        }
      }
      tmp = newCands;
    }

    void bubbleSort(ExprVector& v) {
      // Bubble sort because it's easy....
      for(int i = 0; i < v.size(); i++) {
        for(int j = i + 1; j < v.size(); j++) {
          if(v[i]->left()->arity() > v[j]->left()->arity()) {
            Expr e = v[i];
            v[i] = v[j];
            v[j] = e;
          }
        }
      }
    }

    void sortBounds(ExprVector& bounds) {
      ExprVector holdMPZ, holdOther;

      for(int i = 0; i < bounds.size(); i++) {
        Expr e = normalize(bounds[i]);
        if(isOpX<MPZ>(e->right()) && e->right() != mpzZero) {
          holdMPZ.push_back(e);
        }
        else {
          holdOther.push_back(e);
        }
      }
      bubbleSort(holdOther);
      bubbleSort(holdMPZ);
      bounds.clear();
      for(auto& v : holdOther) bounds.push_back(normalize(v, ghostVars[0]));
      for(auto& v : holdMPZ) bounds.push_back(normalize(v, ghostVars[0]));
    }

    void filterNonGhExp(ExprSet& candSet)
    {
      for(auto i = candSet.begin(); i != candSet.end(); ) {
        if(!contains(*i, ghostVars[0])) {
          if(dg) dataGrds.insert(*i);
          i = candSet.erase(i);
        }
        else i++;
      }
    }

    boost::tribool dataForBoundPhase(Expr src, Expr dst,
                                     map<Expr, ExprSet>& candMap, Expr block) {
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;
      Expr pc = ghostVars[0];
      assert (grds2gh[dst] != NULL);

      qr->body = mk<AND>(mk<NEG>(src),
                         mk<NEG>(mk<AND>(dst, stren[dst],
                                 mk<EQ>(pc, grds2gh[dst])))); // hack for now
      tr->body = u.removeITE(mk<AND>(src, tr_orig.body));

      dst = mk<AND>(mk<NEG>(src), mk<AND>(dst, stren[dst]), mk<EQ>(pc, grds2gh[dst]));

      src = mk<AND>(block, src);
      if(isOpX<TRUE>(block))
        src = replaceAll(src, invVars, fc->srcVars);
      res = dl2.connectPhase(src, dst, invDecl, block, invs, loopGuard);
      dl2.getDataCands(candMap[invDecl], invDecl);  // GF
      return res;
    }

    boost::tribool exploreBounds(Expr src, Expr dst,
                                 map<Expr, ExprSet>& ghCandMap, Expr block)
    {
      boost::tribool res;

      if(isOpX<FALSE>(block)) return false;
      res = dataForBoundPhase(src, dst, ghCandMap, block);
      if (res != true) return false;
      filterNonGhExp(ghCandMap[invDecl]);
      if(ghCandMap[invDecl].empty()) return false;

      ExprSet temp;
      for(auto i = ghCandMap[invDecl].begin(),
          end = ghCandMap[invDecl].end(); i != end; i++) {
        Expr e = *i;
        e = normalize(e,ghostVars[0]);
        temp.insert(e);
      }
      ghCandMap[invDecl].swap(temp);
      if(debug >= 2) {
        outs() << "filtered cands found: ";
        if(!ghCandMap[invDecl].empty()) outs() << ghCandMap[invDecl].size() << "\n";
        else outs() << "  none.\n";
      }
      // break odd/even

      return res;
    }

    Result_t elba(ExprSet& third, Expr src, Expr dst)
    {
      if(debug >= 3) outs() << "\n  ===================\n  ||    E L B A    ||  \n  ===================\n\n";

      filterUnsat();
      Expr pc = ghostVars[0];
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }

      auto candidatesTmp = candidates;
      multiHoudini(worklist);
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      Expr learnedLemmasInv = conjoin(candidates[invDecl], m_efac);
      candidates = candidatesTmp;
      for (auto & a : candidatesTmp[invDecl])
      {
        if (!isOp<ComparissonOp>(a)) continue;  // GF
        if (isOpX<EQ>(a)) continue;
        if (contains(a, pc)) continue;
        ExprVector vars, varsPr;
        for (int i = 0; i < tr->dstVars.size(); i++)
        {
          if (!contains(a, tr->srcVars[i])) continue;
          vars.push_back(tr->srcVars[i]);
          varsPr.push_back(tr->dstVars[i]);
        }
        if (vars.size() > 2) continue;

        auto b = replaceAll(
                  keepQuantifiers(mk<AND>(a, learnedLemmasInv, tr->body), varsPr),
                  varsPr, vars);
        getConj(mk<AND>(a, b), candidates[invDecl]);
      }

      candidatesTmp = candidates;
      multiHoudini(worklist);
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;


      candidates = candidatesTmp;
      for (auto & c : third)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }

      multiHoudini(worklist);
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;


      ExprSet cnjs, cnjsUpd;
      getConj(stren[dst], cnjs);
      for (auto s : cnjs)
      {
        s = simplifyArithm(u.removeITE(u.simplifiedAnd(
          mkNeg(keepQuantifiers(mkNeg(mk<IMPL>(tr->body,
                    replaceAll(s, tr->srcVars, tr->dstVars))),
                      tr->srcVars)),
          replaceAll(conjoin(candidates[specDecl], m_efac),
                      fc->srcVars, tr->srcVars))));

        getConj(s, cnjsUpd);
      }
      for (auto & c : cnjsUpd)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }
      multiHoudini(worklist);
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    ExprSet exploredBounds;

    boost::tribool boundSolveRec(Expr src, Expr dst, Expr block) {
      map<Expr,ExprSet> bounds;
      dataGrds.clear();

      if(!u.isSat(fcBodyInvVars,loopGuard)) {
        if(debug >= 3) outs() << "PROGRAM WILL NEVER ENTER LOOP\n";
        return true;
      }
      if(debug >= 3) {
        outs() << "  EXPLOREBOUNDS:  " << block << "\n";
        outs() << "=================\n";
      }

      if (isOpX<FALSE>(dst))
      {
        grds2gh[src] = mkMPZ(0, m_efac);
        return true;
      }

      boost::tribool res = exploreBounds(src, dst, bounds, block);
      if (res == false)
      {
        grds2gh[src] = grds2gh[dst];
        return true;
      }

      ExprSet grds, grdsDst;
      getConj(dst, grdsDst);
      genCands(grdsDst, ghostVars[0]);
      getConj(src, grds);

      if(dg) {
        for(auto& e: dataGrds) {

          ExprSet vars;
          filter (e, bind::IsConst (), inserter (vars, vars.begin()));

          if(isOpX<EQ>(e) && !hasMPZ(e) && vars.size() > 1)
          {
            grds.insert(e);
            if(debug >= 3)
              outs() << "Adding guard from data: " << e << "\n";
          }
        }
      }
      if(debug >= 2) for(auto& e: grds) outs() << "  grd: " << e << "\n";

      if(bounds[invDecl].size() == 0) res = false;

      ExprVector boundsV;
      for(auto& e: bounds[invDecl])
        if(!isOpX<MULT>(e->left()))
          boundsV.push_back(e);
      sortBounds(boundsV);

      if(debug >= 2) {  //GF
        outs() << "\nBounds found this iteration\n";
        for(auto& e: boundsV) {
          outs() << "  " << e << "\n";
        }
      }

      bool rerun = false;
      for(auto b = boundsV.begin(), end = boundsV.end(); b != end && res; b++) {
        candidates.clear();

        // if(!isOpX<PLUS>((*b)->right())) b++;
        // if(b == boundsV.end()) b--;

        if(rerun) {
          if(debug >= 3) outs() << "RERUN\n=====\n";
          b--;
          for(auto& e: fgrds2gh) {
            candidates[invDecl].insert(e.first);
          }
        }
        else {
          // auto fres = exploredBounds.find(*b);
          // if(fres != exploredBounds.end()) {
          //   continue;
          // }
          // exploredBounds.insert(*b);
          for(auto& e: grds) {
            candidates[specDecl].insert(replaceAll(e, tr->srcVars, fc->srcVars));
            candidates[invDecl].insert(e);
          }
        }
        candidates[specDecl].insert(replaceAll(*b, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(*b);

        ExprSet factCands;
        getConj(keepQuantifiers(fc->body, fc->srcVars), factCands);
        for (auto & c : factCands)
        {
          candidates[specDecl].insert(c);
          candidates[invDecl].insert(replaceAll(c, fc->srcVars, tr->srcVars));
        }

        if(debug >= 2) outs() << "\n- - - b: " << *b << "\n\n";

        Result_t res_t = elba(grdsDst,
          mk<AND>(src, replaceAll(src, tr->srcVars, fc->srcVars)), dst);

        if(debug >= 2) {
          outs() << "==================\n";
          printCandsEx();
          outs() << "==================\n";
        }

        if(res_t == Result_t::UNKNOWN) {
          candidates.clear();
          if(!rerun) {
            rerun = true;
          }
          else {
            rerun = false;
          }
          if(debug >= 2) outs() << "=====> unknown\n\n";
          if(std::next(b) == end) {
            if(phaseNum < phases.size())
              boundSolveRec(src, dst, mk<TRUE>(m_efac));
          }
          continue;
        }

        // If you're here then G&S returned UNSAT
        // Yes, I'm here.
        if(debug >= 2) outs() << "=====> unsat\n\n";
        rerun = false;

        parseForGuards(); // Associates guards (pre(Vars)) with Expr gh = f()
                                 // They are stored in grds2gh map.

        if(debug >= 2) {
          outs() << "\n    Guards\n==============\n";
          for(auto& g: grds2gh) {
            outs() << " : " << g.first << "\n";
          }
          outs() << "==============\n";
        }

        // end of parsing guards.
        ExprSet grds2;
        for(auto& g: grds2gh) {
          if (u.implies(g.first, src))
            grds2.insert(g.first);
        }
        Expr grd = disjoin(grds2,m_efac);
        if(debug >= 4) outs() << "grd: " << grd << "\n";
        if(u.isSat(mkNeg(grd), src)) {
          if(boundSolveRec(src, dst, mkNeg(grd))) {
            return true;
          }
        }
        else
        {
          return true;
        }
      }
      return false;
    }

    void boundSolve(Expr src, Expr dst)
    {
      if(debug >= 2) outs () << "boundSolve: " << src << " -> " << dst << "\n";
      Expr block = mk<TRUE>(m_efac);
      if(boundSolveRec(src, dst, block)) { /* Success! */ }
      else {
        outs() << "unknown\n";
        exit(0);
      }
    }

    void pathsSolve()
    {
      ExprSet finals;
      if(debug >= 2) outs() << "\n===== PATH SOLVE =====\n";
      for (auto & p : paths)
      {
        if(debug >=2) {
          outs () << "   - - - - - next path - - - - -\n";
          for (auto & pp : p)
            outs () << pp << " -> ";
          outs () << "\n";
          outs () << "   - - - - - - - - - - - - - - -\n";
        }

        assert(p.size() > 1);
        Expr res;
        int i;
        for (i = p.size() - 2; i >= 0; i--)
        {
          if (p[i] == fcBodyInvVars) break; // hack for now
          boundSolve(p[i], p[i+1]);

          res = NULL;
          ExprSet pre;
          for(auto& g: grds2gh)
          {
            if (u.implies(g.first, p[i]))
            {
              pre.insert(g.first);
              if (res == NULL) res = g.second;
              else res = mk<ITE>(g.first, g.second, res);   // GF
            }
          }
          stren[p[i]] = simplifyBool(distribDisjoin(pre, m_efac));
          if (i != 0) grds2gh[p[i]] = res;
        }
        finals.insert(mk<IMPL>(stren[p[i + 1]], mk<EQ>(ghostVars[0], res)));
        grds2gh.clear();
        stren.clear();
      }
      outs () << "FINAL:\n";
      // for(auto& e: finals) {
      //   u.print(e,outs());
      //   outs() << "\n";
      // }
      pprint(finals, 5);
    }

    void printCandsEx(bool ppr = true) {
      for(auto& a: candidates) {
        outs() << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          outs() << "(" << *b << " " << u.varType(b) << ")";
        }
        outs() << ") Bool\n";

        if(ppr) pprint(a.second, 3);
        else u.print(conjoin(a.second,m_efac));
        outs() << "\n\n";
      }
    }

    void printPhases() {
      outs() << "Phases\n======\n";
      for(auto& p: phases) outs() << p << "\n";
    }
  };

  inline void findBounds(string smt, int inv, int stren, bool maximal, const vector<string> & relsOrder, bool useGAS,
                          bool usesygus, bool useUC, bool newenc, bool fixCRels, string syguspath, bool dg,
                          bool data2, bool doPhases, int debug = 0)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BoundSolver spec(ruleManager, stren, dg, data2, doPhases, debug);
    if(!ruleManager.hasQuery) {
      if(debug >= 4) ruleManager.print(true);
      if(debug >= 4 && ruleManager.decls.size() > 1) {
        outs() << "Multiple loops\n";
      }
      else if(debug >= 4) {
        outs() << "Single loop\n";
      }
      spec.setUpQueryAndSpec(); // Needs to accomodate many loops.
      if(debug >= 2) ruleManager.print(true);
    }
    else {
      outs() << "Unsupported format\n";
      return;
    }

    spec.collectPhaseGuards();
    if(debug >= 2) spec.printPhases();
    // for(auto r: ruleManager.decls) {
    //   // run for each decl, constructing new TR for each inv each time.
    // }
    spec.pathsSolve();
  }
}

#endif
