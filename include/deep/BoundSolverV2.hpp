#ifndef BOUND_SOLVER_V2_HPP
#define BOUND_SOLVER_V2_HPP

#include "BoundSolver.hpp" // Include BoundSolver.hpp

namespace ufo {
  class BoundSolverV2 : public BoundSolver { // Inherit from BoundSolver
  private:
    ExprMap bounds;
    Expr fcBodyOrig;
    int n; // parameter to control the number of trace iterations.
    int limit;

    int to = 100;
    int freqs = 1;
    int aggp = 1;
    int mut = 1;
    int dat = 1;
    int doProp = 0;
    bool doDisj = true;
    bool mbpEqs = false;
    bool dAllMbp = true;
    bool dAddProp = false;
    bool dAddDat = true;
    bool dStrenMbp = false;
    bool dFwd = false;
    bool dRec = false;
    bool dGenerous = false;

  public:
    // Constructor
    BoundSolverV2(CHCs &r, int _b, bool _dg, bool d2, bool _dp, int _limit, int dbg)
        : BoundSolver(r,_b,_dg,d2,_dp,dbg), limit(_limit), n(_limit)
    {
      // TODO: Initialize any additional member variables specific to BoundSolverV2
      for(auto& chc: r.chcs) 
      {
        if(chc.isFact)
        {
          fcBodyOrig = chc.body;
          if(debug >= 6) outs() << "fcBodyOrig: " << fcBodyOrig << "\n";
        }
      }
    }

    void copyRule(HornRuleExt* dst, HornRuleExt* src)
    {
      dst->srcRelation = src->srcRelation;
      dst->dstRelation = src->dstRelation;
      dst->srcVars = src->srcVars;
      dst->dstVars = src->dstVars;
      dst->body = src->body;
      dst->isFact = src->isFact;
      dst->isQuery = src->isQuery;
      dst->isInductive = src->isInductive;
    }

    void prepareRuleManager(CHCs& rm, vector<HornRuleExt*>& rules)
    {
      rm.addFailDecl(ruleManager.failDecl);

      for (auto &r : rules)
      {
        rm.addRule(r);
      }
      rm.findCycles();

      rm.dwtoCHCs = rm.wtoCHCs;
      for (auto it = rm.dwtoCHCs.begin(); it != rm.dwtoCHCs.end();)
        if ((*it)->isQuery) it = rm.dwtoCHCs.erase(it);
          else ++it;

      if(debug >= 4) rm.print(true);
    }

    void prepareRulesWithPrecond(Expr elim, Expr preCond, CHCs& rm)
    {
      HornRuleExt* fcWithPrecond = new HornRuleExt();
      copyRule(fcWithPrecond, fc);
      fcWithPrecond->isFact = true;
      fcWithPrecond->srcRelation = mk<TRUE>(m_efac);
      Expr fcPreCond = replaceAll(elim, tr->srcVars, fc->srcVars);
      fcWithPrecond->body = replaceAll(mk<AND>(fcPreCond, normalize(preCond)), fcWithPrecond->srcVars, tr->dstVars);
      fcWithPrecond->srcVars.clear();

      ExprVector qrBody;
      getConj(qr->body, qrBody);
      for (auto c = qrBody.begin(); c != qrBody.end(); )
      {
        if (contains(*c, ghostVars[0])) c = qrBody.erase(c);
        else ++c;
      }
      qrBody.push_back(mkNeg(ghostGuard));
      HornRuleExt* qrForFH = new HornRuleExt();
      copyRule(qrForFH, qr);
      qrForFH->body = conjoin(qrBody, m_efac);

      vector<HornRuleExt*> rules;
      rules.push_back(fcWithPrecond);
      rules.push_back(tr);
      rules.push_back(qrForFH);
      prepareRuleManager(rm, rules);
    }

    boost::tribool checkSafety(Expr elim, Expr preCond)
    {

      if(debug >= 2) outs() << "\n\nCheck Safety\n============\n";
      if(debug >= 4)
      {
        outs() << "  elim: " << elim << "\n";
        outs() << "  preCond: " << preCond << "\n";
      }
      // add precondition to be checked to the ruleManager.
      CHCs rm(m_efac, z3, debug);

      prepareRulesWithPrecond(elim, preCond, rm);

      BndExpl bnd(rm, to, debug);
      RndLearnerV4 ds(m_efac, z3, rm, to, freqs, aggp, mut, dat,
                      doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
                      dFwd, dRec, dGenerous, (debug >= 6 ? 2 : 0));

      map<Expr, ExprSet> cands;
      for (auto &cyc : rm.cycles)
      {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++)
        {
          Expr dcl = rm.chcs[cyc.second[i][0]].srcRelation;
          if (ds.initializedDecl(dcl))
            continue;
          ds.initializeDecl(dcl);
          Expr pref = bnd.compactPrefix(rel, i);
          ExprSet tmp;
          getConj(pref, tmp);
          for (auto &t : tmp)
            if (hasOnlyVars(t, rm.invVars[dcl]))
              cands[dcl].insert(t);
          if (mut > 0)
            ds.mutateHeuristicEq(cands[dcl], cands[dcl], dcl, true);
          ds.initializeAux(cands[dcl], bnd, rel, i, pref);
        }
      }
      if (dat > 0)
        ds.getDataCandidates(cands);
      for (auto &dcl : rm.wtoDecls)
      {
        for (int i = 0; i < doProp; i++)
          for (auto &a : cands[dcl])
            ds.propagate(dcl, a, true);
        ds.addCandidates(dcl, cands[dcl]);
        ds.prepareSeeds(dcl, cands[dcl]);
      }
      for (auto &dcl : rm.decls)
      {
        ds.addCandidates(dcl, cands[dcl]);
      }
      if(ds.bootstrap())
      { 
        return true;
      }
      ds.calculateStatistics();
      ds.deferredPriorities();
      std::srand(std::time(0));
      return ds.synthesize(to);
    }

    void removeCommonExpr(ExprVector &d, ExprVector& toDisj, Expr& cm)
    {
      if (d.size() <= 1)
      {
        toDisj = d;
        cm = mk<TRUE>(m_efac);
        return;
      }

      ExprSet comm;
      vector<ExprSet> dsjs;
      dsjs.push_back(ExprSet());
      auto it = d.begin();
      getConj(*it, dsjs.back());
      comm = dsjs.back();
      for (it = std::next(it); it != d.end(); ++it)
      {
        ExprSet updComm, tmp;
        dsjs.push_back(ExprSet());
        getConj(*it, dsjs.back());
        tmp = dsjs.back();
        distribDisjoin(comm, tmp, updComm);
        comm = updComm;
      }

      for (auto a : dsjs)
      {
        minusSets(a, comm);
        toDisj.push_back(normalize(conjoin(a, m_efac)));
      }
      
      cm = conjoin(comm, m_efac);
    }

    void splitExprs(ExprVector& BigPhi, map<Expr,ExprVector>& infMap)
    {
      for (auto &v : invVars)
      {
        for(auto& c: BigPhi)
        {
          ExprSet tmp;
          getConj(c, tmp);
          for(auto& t: tmp)
          {
            if (contains(t, v))
            {
              infMap[v].push_back(t);
            }
          }
        }
      }
    }

    void filterBigPhi(ExprVector& BigPhi)
    {
      ExprVector temp;
      for (auto &c : BigPhi)
      {
        c = normalize(c, true);
        if (debug >= 4)
          outs() << "  c: " << c << "\n";
        ExprSet conjs;
        getConj(c, conjs);
        ExprVector vars;
        Expr toChange;
        Expr conj;
        for (auto &t : conjs)
        {
          if (t->left()->arity() == 1)
          {
            toChange = t->right();
            conj = t;
            filter(t, IsConst(), inserter(vars, vars.begin()));
          }
        }
        for (auto &t : conjs)
        {
          if (!vars.empty() && t->left()->arity() > 1 && contains(t, vars[0]))
          {
            ExprSet tmp;
            getConj(t, tmp);
            for (auto &tt : tmp)
            {
              if (contains(tt, vars[0]))
              {
                Expr ttt = tt;
                ttt = simplifyArithm(replaceAll(ttt, vars[0], toChange));
                ttt = ineqReverter(ttt);
                temp.push_back(normalize(mk<AND>(ttt, conj)));
              }
            }
          }
        }
      }
      if(!temp.empty()) BigPhi = temp;
    }

    ExprSet inferWithData(ExprVector BigPhi)
    {
      if(debug >= 3) outs() << "\n\nInfer With Data\n==============\n";
      filterBigPhi(BigPhi);
      if (debug >= 4)
      {
        outs() << "  Filtered BigPhi size: " << BigPhi.size() << "\n";
        for (auto &c : BigPhi)
        {
          outs() << "  Filtered From BigPhi: " << c << "\n";
        }
      }
      DataLearner2 dl2(ruleManager, z3, debug);

      dl2.makeModel(invDecl, BigPhi);
      if(debug >= 3) dl2.printModel(invDecl);
      ExprSet cands;
      dl2.getDataCands(cands, invDecl);

      for (auto c = cands.begin(); c != cands.end();)
      {
        if (debug >= 4)
          outs() << "  cands: " << *c << "\n";
        if (!u.isSat(*c, tr->body))
        {
          if(debug >= 2) outs() << "  Removed: " << *c << "\n";
          c = cands.erase(c);
        }
        else
        {
          ++c;
        }
      }

      return cands;
    }

    ExprSet infer(ExprVector &BigPhi1)
    {
      // for >3 vars then do case analysis.
      // 
      if(debug >= 3) outs() << "\n\nInfer\n=====\n";
      // Break equalities into inequalities.
      // Find weakest.
      // Check that the previous expr is an overapproximation.
      // Process them in order, run simplifyArithm on each one.
      ExprSet inferredRet;
      map<Expr, ExprVector> infMap;
      ExprVector BigPhi;

      Expr common; // Sometimes common will be needed. For ABC_ex01 it is not.
      if(BigPhi1.empty()) return inferredRet;
      removeCommonExpr(BigPhi1, BigPhi, common);

      // Do data learning on BigPhi.
      ExprSet inferredFromData;
      inferredFromData = inferWithData(BigPhi); // infer2
      
      // filter BigPhi with what's been learned from data.
      // ExprVector smallphi = BigPhi;
      // Expr fromData = conjoin(inferredFromData, m_efac);
      // for(auto it = smallphi.begin(); it != smallphi.end(); )
      // {
      //   if(!u.isSat(*it, fromData))
      //   {
      //     if(debug >= 3) outs() << "  Removed: " << *it << "\n";
      //     it = smallphi.erase(it);
      //   }
      //   else
      //   {
      //     ++it;
      //   }
      // }

      // BigPhi = smallphi;

      splitExprs(BigPhi, infMap);

      for(auto ev: infMap)
      {
        ExprSet inferred;
        for(int i = 0; i < ev.second.size(); i++)
        {
          Expr c = ev.second[i];
          c = simplifyArithm(c);
          c = u.removeRedundantConjuncts(c);
          if(debug >= 4) outs() << "  c: " << c << "\n";
          ExprVector inferSeeds;
          if(isOpX<EQ>(c))
          {
            inferSeeds = {mk<GEQ>(c->left(), c->right()), 
                          mk<LEQ>(c->left(), c->right())};
          }
          else
          {
            inferSeeds = {c};
          }

          if(i == 0)
          {
            inferred.insert(inferSeeds.begin(), inferSeeds.end());
          }
          else
          {
            for(auto itr = inferred.begin(); itr != inferred.end(); )
            {
              bool toBreak = false;
              if(!u.implies(c, *itr) || u.implies(*itr, c))
              {
                itr = inferred.erase(itr);
                toBreak = true;
              }
              if(toBreak) break;
              itr++;              
            }
          }

          if(debug >= 4)
          {
            outs() << "Current inferred:\n";
            pprint(inferred, 2);
            outs() << "\n";
          }
          
        }
        inferredRet.insert(inferred.begin(), inferred.end());
      }

      if(debug >= 2)
      {
        for (auto &i : inferredRet)
        {
          outs() << "Inferred: " << i << "\n";
        }
        for(auto& i: inferredFromData)
        {
          outs() << "Inferred from data: " << i << "\n";
        }
        outs() << "Common: " << common << "\n";
      }
      if (common != mk<TRUE>(m_efac))
        inferredRet.insert(common);

      // inferredRet.insert(conjoin(dataGrds, m_efac));
      inferredRet.insert(inferredFromData.begin(), inferredFromData.end());
      return inferredRet;
    }

    Expr branchPreCond = mk<TRUE>(m_efac);
    // Public member functions
    boost::tribool invFromData(Expr src, Expr dst, Expr block, 
                               map<Expr, ExprSet>& candMap, int n) {
      
      if(debug >= 3) outs() << "\n\nInvFromData\n===========\n";
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;
      src = replaceAll(src, invVarsPr, invVars);

      src = simplifyArithm(src);
      dst = simplifyArithm(dst);
      block = simplifyArithm(block);

      if(debug >= 4) 
      {
        outs() << "  src: " << src << "\n";
        outs() << "  dst: " << dst << "\n";
        outs() << "  block: " << block << "\n";
        outs() << "  n: " << n << "\n";
      }

      if(debug >= 3) ruleManager.print(true);

      // Replace this to reuse the SSA that is built previously.
      res = dl2.connectPhase(src, dst, n, invDecl, block, invs, loopGuard);
      if (res == true)
      {
        dl2.getDataCands(candMap[invDecl], invDecl);
      }
      dataGrds.clear();
      filterNonGhExp(candMap[invDecl]);
      u.removeRedundantConjuncts(dataGrds);
      if(debug >= 3) 
      {
        outs() << "dataGuards: \n";
        for (auto &d : dataGrds)
        {
          outs() << d << "\n";
        }
      }

      branchPreCond = conjoin(dataGrds, m_efac);
      branchPreCond = simplifyArithm(branchPreCond);
      if (debug >= 3)
      {
        outs() << "  branchPreCond: " << branchPreCond << "\n";
      }
      // block = branchPreCond;
      if (debug >= 2)
      {
        for (auto &e : candMap[invDecl])
        {
          outs() << "  invs from data: " << e << "\n";
        }
      }
      return res;
    }

    Expr weakenAndSplit(ExprVector& BigPhi, Expr preCond) 
    {
      // Break equalities into inequalities.
      // Find weakest.
      // Check that the previous expr is an overapproximation.
      // Process them in order, run simplifyArithm on each one.
      if(debug >= 2) outs() << "\n\nWeaken & Split\n==============\n";
      if(debug >= 4)
      {
        outs() << "  BigPhi size: " << BigPhi.size() << "\n";
        for(auto& c: BigPhi)
        {
          outs() << "  From BigPhi: " << c << "\n";
        }
      }
      ExprSet inferred = infer(BigPhi);
      // Expr c = conjoin(inferred, m_efac);
      Expr c = mk<TRUE>(m_efac);
      for(auto& i: inferred) {
        c = mk<AND>(c, i);
        if(debug >= 4) outs() << "  c: " << c << "\n";
        boost::tribool safe = checkSafety(c, preCond);
        if(debug >= 4) 
        {
          if(!safe) outs() << "\n\n********\n*UNSAFE*\n********\n\n";
        }
        if(safe) return c;
      }
      return mk<TRUE>(m_efac);
    }

    Expr abduction(Expr& phi, Expr& f, Expr& preCond, 
                int k, vector<ExprVector>& vars, vector<int>& trace,
                BndExpl& bnd, CHCs& rm)
    {
      trace.push_back(2); // Need to add the query to the trace.

      if(debug >= 4) outs() << "\nAbduction\n=========\n";

      ExprVector ssa;
      bnd.getSSA(trace, ssa);
      phi = conjoin(ssa, m_efac);
      vars = bnd.getBindVars();
      for (auto v = vars.begin(); v != vars.end(); )
      {
        if (v->size() == 0) { v = vars.erase(v); }
        else { ++v; }
      }

      if(debug >= 3) 
      {
        outs() << "  k: " << k << "  vars size: " << vars[vars.size() - 1].size();
        outs() << "  invVars.size(): " << rm.invVars[invDecl].size() << "\n\n";
      }

      Expr ff = normalize(f, ghostVars[0]);
      if (debug >= 3)
      {
        outs() << "  ff: ";
        pprint(ff, 2);
      }
      Expr fg = mk<EQ>(ff->right(), ghostValue);
      if(debug >= 3) outs() << "  gh value: " << fg << "\n";
      
      for (int i = 1; i < k; i++)
      {
        fg = replaceAll(fg, vars[vars.size() - i - 1], vars[vars.size() - i]);
      }
      fg = replaceAll(fg, rm.invVars[invDecl], vars[vars.size() - 1]);
      if(debug >= 5) outs() << "  gh value (vars replaced): " << fg << "\n";

      phi = mk<AND>(phi, fg);
      if(debug >= 4)
      {
        outs() << "  phi: ";
        pprint(phi,2);
      }

      ff = replaceAll(ff, tr->srcVars, fc->srcVars);
      preCond = ff;

      Expr elim;
      elim = eliminateQuantifiers(phi, vars[vars.size() - 1]);
      for (int i = 1; i < k; i++)
      {
        elim = eliminateQuantifiers(elim, vars[vars.size() - i - 1]);
      }

      return elim;
    }

    Expr makePretty(Expr elim, int k, vector<ExprVector>& vars, CHCs& rm)
    {
      Expr e = elim;
      for (int i = 1; i < k; i++)
      {
        e = replaceAll(e, vars[vars.size() - i - 1], vars[vars.size() - i]);
      }

      e = replaceAll(e, vars[0], rm.invVars[invDecl]);
      return e;
    }

    Expr getPre(Expr p, Expr f, int n)
    {
      // p holds the conjunction of the negated previous preconditions.
      // f is the data invariant.
      // n is the number of iterations.
      // returns the precondition for the next iteration.

      if(debug >= 2) outs() << "\n\nGet Pre\n=======\n";

      ExprSet Phi;
      CHCs rm(m_efac, z3, debug);

      vector<HornRuleExt*> rules;
      rules.push_back(&fc_nogh);
      rules.push_back(&tr_nogh);
      rules.push_back(&qr_nogh);
      prepareRuleManager(rm, rules);

      for(auto& hr: rm.chcs)
      {
        if(hr.isFact)
        {
          hr.body = mk<AND>(hr.body, replaceAll(p, invVars, invVarsPr));
          if(debug >= 4) outs() << "  hr.body: " << hr.body << "\n";
        }
      }

      BndExpl bnd(rm, (debug > 0));
      ExprVector BigPhi;
      Expr preCond;

      for(int k = 1; k <= n; k++) {
        vector<int> trace;
        buildTrace(trace, k);

        Expr phi = bnd.toExpr(trace);

        if (!u.isSat(phi))
        {
          Expr res = mk<TRUE>(m_efac);
          if(debug >= 4) outs() << "  phi is UNSAT\n";
          if(BigPhi.size() < 1) return res;
        }

        vector<ExprVector> vars;
        Expr elim = simplifyArithm(abduction(phi, f, preCond, k, vars, trace, bnd, rm));

        // value of y = 1, y = 2, y = 4... make an example like this.
        // needs to handle many variables.

        if (debug >= 4)
        {
          outs() << "  phi: ";
          pprint(phi, 2);
        }
        if (debug >= 3)
        {
          outs() << "  Result from Abduction: ";
          pprint(elim, 2);
        }
        
        if (u.implies(elim, phi))
        {
          if(debug >= 4) outs() << "  ERROR with abduction\n";
          continue;
        }

        elim = simplifyArithm(makePretty(elim, k, vars, rm));

        ExprVector prjcts, prjcts2;
        u.flatten(elim, prjcts2, false, invVars, keepQuantifiersRepl);

        for(auto& p: prjcts2)
        {
          prjcts.push_back(simplifyArithm(p));
        }

        for(auto p: prjcts)
        {
          if(debug >= 5) outs() << "  Projection: " << p << "\n";
          // if(debug >= 4) outs() << "  isSat? " << p << " && " << branchPreCond << "\n";
          // if(u.isSat(p, branchPreCond))
          // {
            if (debug >= 3)
            {
              outs() << "  ADDED TO BIGPHI: " << normalize(p) << "\n";
            }
            BigPhi.push_back(normalize(p));
          // }
        }

        if(debug >= 5) outs() << "  Ghost Value: " << ghostValue << "\n";
        // if(debug >= 3)
        // {
        //   outs() << "  ADDED TO BIGPHI: "; 
        //   pprint(elim, 2);

        // } 
        // BigPhi.push_back(elim);
      }
      Expr c = weakenAndSplit(BigPhi, preCond);

      return c;
    }

    Expr constructPhi(Expr& p)
    {
      p = mk<TRUE>(m_efac);
      for (auto &b : bounds)
      {
        Expr psi = b.first;
        psi = mk<AND>(p, mkNeg(psi));
        
        p = mk<AND>(p, psi);
      }

      p = simplifyArithm(p);

      Expr phi = mk<AND>(p, replaceAll(fc_nogh.body, invVarsPr, invVars), tr_nogh.body);        

      return phi;
    }

    void buildTrace(vector<int>& trace, int i, bool addQuery = false)
    {
      trace.push_back(0); // We know we have a single loop system.
      for (int k = 0; k < i; k++) trace.push_back(1);
      if (addQuery) trace.push_back(2);

      if(debug >= 4) 
      {
        outs() << "  Trace information: size: ";
        outs() << trace.size() << "\n";
        for (auto &t : trace)
          outs() << t << "  ";
        outs() << "\n";
      }
    }

    void solve()
    {
      // Implements Alg 1 and Alg 2 from the paper "Exact Loop Bound Analysis"
      
      if(debug) outs() << "\n\nSolve\n=====\n\n";

      Expr prevPsi;
      // use exprset including fc->body and tr->body 
      // and the negation of the bound guard
      while (true)
      {
        if(n > 100 * limit) return;

        Expr p;
        Expr phi = constructPhi(p);
        if(debug >= 2) 
        {
          outs() << "  phi: ";
          pprint(phi, 2);

        }

        if (!u.isSat(phi))
        {
          if(debug >= 3) outs() << "  phi is UNSAT\n";
          bounds[simplifyArithm(p)] = mkMPZ(0, m_efac);
          return;
        }
        if(debug >= 4) outs() << "  phi is SAT\n";

        // rewrite to be more efficient.
        boost::tribool res;
        map<Expr, ExprSet> forms;
        Expr model;
        vector<int> m;
        for(int i = 0; i < n; i++)
        {
          vector<int> trace;
          BndExpl bnd(ruleManager, (debug > 0));

          buildTrace(trace, i+1, true);

          Expr ssa;
          ssa = mk<AND>(p, bnd.toExpr(trace));
          ssa = replaceAll(ssa, fc->srcVars, invVars);
          if(debug >= 4) {
            outs() << "SSA: ";
            pprint(ssa, 2);
          }
          if(u.isSat(ssa))
          {
            m.push_back(i);
            // update to use models for data learning.
            model = u.getModel();
            if (debug >= 3) outs() << "  Model: " << model << "\n";
            // if(i > 5) break;
          }
          else if(debug >= 4) { outs() << "  ====  SSA is UNSAT\n"; }
        }

        if(m.empty()) // this is a check to see if we have a nonterminating case.
        {
          ExprSet f;
          f.insert(mk<EQ>(ghostVars[0], mkMPZ(-1, m_efac)));
          forms[invDecl] = f;
          bounds[p] = *f.begin();
        }
        else
        {
          // get forms from data.
          // TODO: Make parametric so that different algorithms can be called.
          res = invFromData(fc->body, qr->body, p, forms, m.back());
        }

        if(res == true)
        {
          ExprSet invs;
          Expr psi;

          ExprVector formsVec;
          for(auto& s: forms[invDecl])
          {
            formsVec.push_back(s);
          }

          sortBounds(formsVec);

          if(debug >= 3)
          {
            outs() << "  ==> Sorted invs from data:\n";
            pprint(formsVec, 4);
          }

          for (auto &f : formsVec)
          {
            if(debug >= 3) outs() << "Trying next bound: " << f << "\n";
            bool toContinue = false;
            for(auto& b: bounds)
            {
              if(b.second == f)
              {
                if(debug >= 4) outs() << "  Bound already found\n";
                toContinue = true;
              }
            }
            if(toContinue) continue;

            psi = getPre(p, f, m.back());
            psi = simplifyArithm(psi);
            if(psi != mk<TRUE>(m_efac))
            {
              if(debug >= 2) {
                outs() << "\n---->  Adding bound:\n";
                pprint(psi);
                outs() << " => ";
                outs() << normalize(f, ghostVars[0]) << " 😎\n\n";
              }
              bounds[psi] = normalize(f, ghostVars[0]);
              break;
            }
          }
        }
        else
        {
          n++;
          if(debug >= 2) outs() << "  UNKNOWN\n";
          if(debug >= 3) outs() << "  n: " << n << "\n";
        }
        m.clear();
      }
    }

    void printResults()
    {
      if(!bounds.empty()) outs() << "\nSuccess! Found bounds:\n";
      int i = 0;
      for (auto &b : bounds)
      {
        if(!u.isSat(mkNeg(b.first), replaceAll(fc_nogh.body, invVarsPr, invVars)))
        {
          outs() << b.second << "\n";
          return;
        }
        else
        {
          if(i < bounds.size() - 1)
            outs() << "  ite " << b.first << ", " << b.second;
          else
            outs() << ", " << b.second << "\n";
        }
        i++;
      }
    }
  }; // End class BoundSolverV2

  // TODO: Rewrite the infer function according to the notes above.
  // TODO: Test implementation over more benchmarks.

  inline void learnBoundsV2(string smt, int inv, int stren, bool dg,
                                  bool data2, bool doPhases, int limit, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);

    ruleManager.parse(smt, false);

    BoundSolverV2 bs(ruleManager, inv, dg, data2, doPhases, limit, debug);
    bs.removeQuery();
    bs.setUpQueryAndSpec(mk<TRUE>(m_efac), mk<TRUE>(m_efac));
    // bs.collectPhaseGuards();

    bs.solve();
    // Print the results.
    bs.printResults();
  }
}

#endif // BOUND_SOLVER_V2_HPP
