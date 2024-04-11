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

    bool doGJ = false;
    bool doConnect = false;

  public:
    // Constructor
    BoundSolverV2(CHCs &r, int _b, bool _dg, bool d2, bool _dp, int _limit, bool gj, bool dc, int dbg)
        : BoundSolver(r,_b,_dg,d2,_dp,dbg), limit(_limit), n(_limit), doGJ(gj), doConnect(dc)
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

    Expr setGhostGuard(Expr value)
    {
      return mk<EQ>(ghostVars[0],value);
    }

    void prepareRulesWithPrecond(Expr elim, Expr preCond, CHCs& rm)
    {
      HornRuleExt* fcWithPrecond = new HornRuleExt();
      copyRule(fcWithPrecond, fc);
      fcWithPrecond->isFact = true;
      fcWithPrecond->srcRelation = mk<TRUE>(m_efac);
      Expr fcPreCond = replaceAll(elim, tr->srcVars, fc->srcVars);
      Expr body = replaceAll(fcWithPrecond->body, fcWithPrecond->srcVars, tr->dstVars);
      body = u.removeRedundantConjuncts(body);
      fcPreCond = replaceAll(mk<AND>(fcPreCond, normalize(preCond), body), fcWithPrecond->srcVars, tr->dstVars);
      // fcPreCond = u.removeRedundantConjuncts(fcPreCond);
      if (debug >= 3) outs() << "Original fcBody: " << fcWithPrecond->body << "\n";
      fcWithPrecond->body = fcPreCond;
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
      // TODO: Come up with a more error proof map. One that considers operators too.
      if(debug >= 5) outs() << "\nSplit Exprs\n===========\n";

      for(auto& cc: BigPhi)
      {
        Expr c = normalize(cc, true);
        if(debug >= 4) outs() << "Splitting: " << c << "\n";
        ExprVector lhs;
        getConj(c, lhs);
        for(int i = 0; i < lhs.size(); i++)
        {
          Expr lhsi = lhs[i]->left();
          infMap[lhsi].push_back(lhs[i]);
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

    Expr getLinComb(Expr eq, Expr inEq, double eqConst, double inEqConst)
    {
      if (debug >= 5)
      {
        outs() << "Processing linear combination\n";
        outs() << "eq: " << *eq << "\n";
        outs() << "inEq: " << *inEq << "\n";
        outs() << "eqConst: " << eqConst << "\n";
        outs() << "inEqConst: " << inEqConst << "\n";
      }

      Expr e = mk<TRUE>(m_efac);
      if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst > eqConst)
      {
        e = mk<GT>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst < eqConst)
      {
        e = mk<LT>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst < eqConst)
      {
        e = mk<GEQ>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst > eqConst)
      {
        e = mk<LEQ>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst >= eqConst)
      {
        e = mk<GEQ>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst <= eqConst)
      {
        e = mk<LEQ>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<GEQ>(inEq) || isOpX<GT>(inEq)) && inEqConst <= eqConst)
      {
        e = mk<GT>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if ((isOpX<LEQ>(inEq) || isOpX<LT>(inEq)) && inEqConst >= eqConst)
      {
        e = mk<LT>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      else if (isOpX<EQ>(inEq) && inEqConst == eqConst)
      {
        e = mk<EQ>(inEq->left(), eq->left());
        e = normalize(e);
        if (debug >= 5)
          outs() << "Adding: " << *e << "\n";
      }
      return e;
    }

    void linCombIneq(Expr srcRel, ExprVector &forms, map<Expr, ExprSet>& dc)
    {
      if (debug >= 5)
        outs() << "Processing linear combination of inequalities\n";
      ExprSet res;
      for (auto &f : forms)
      {
        Expr const1;
        ExprVector conjs;
        getConj(f, conjs);
        if (conjs.size() < 2)
          continue;
        Expr eq = mk<TRUE>(m_efac);
        Expr inEq = mk<TRUE>(m_efac);
        for (auto &c : conjs)
        {
          // get the value of the constant.
          if (debug >= 5)
            outs() << "Processing inEq/Eq: " << *c << "\n";
          if (isOpX<EQ>(c))
          {
            if (eq != mk<TRUE>(m_efac))
              inEq = c;
            else
              eq = c;
          }
          else if (!isOpX<NEQ>(c)) // Not handling NEQs for now.
          {
            if (inEq != mk<TRUE>(m_efac))
              eq = c;
            else
              inEq = c;
          }
        }
        if (debug >= 5)
        {
          outs() << "eq: " << *eq << "\n";
          outs() << "inEq: " << *inEq << "\n";
        }

        if(eq == mk<TRUE>(m_efac) || inEq == mk<TRUE>(m_efac)) continue;
        double eqConst = lexical_cast<double>(eq->right());
        double inEqConst = lexical_cast<double>(inEq->right());

        if (eq->left() == inEq->left())
        {
          if (res.empty())
            res.insert(inEq);
          else
          {
            Expr e = *res.rbegin();
            if (u.implies(e, inEq))
            {
              res.erase(e);
              res.insert(inEq);
            }
          }
        }
        else
        {
          res.insert(getLinComb(eq, inEq, eqConst, inEqConst));
        }
      }
      if (debug >= 5)
      {
        outs() << "Adding to data candidates\n";
        for (auto &r : res)
        {
          outs() << "  " << *r << "\n";
        }
      }
      dc[srcRel].insert(res.begin(), res.end());
    }

    bool trySimplifying(ExprVector &conjs)
    {
      ExprSet similar;
      bool eraseE = false;
      bool simplified = false;
      for (auto itr = conjs.begin(); itr != conjs.end();)
      {
        Expr e = (*itr)->left();
        for (auto jtr = conjs.begin(); jtr != conjs.end();)
        {
          if (itr == jtr)
          {
            jtr++;
            continue;
          }
          if (e == (*jtr)->left())
          {
            eraseE = true;
            simplified = true;
            jtr = conjs.erase(jtr);
          }
          else
            jtr++;
        }
        if (eraseE)
        {
          eraseE = false;
          itr = conjs.erase(itr);
        }
        else
          itr++;
      }

      if (debug > 4)
      {
        outs() << "\nSimplified:\n";
        for (auto &c : conjs)
        {
          outs() << "  " << *c << "\n";
        }
      }

      return simplified;
    }

    void makeModel(Expr srcRel, ExprVector &forms1, map<Expr, ExprSet>& dc)
    {
      ExprVector vars;
      filter(forms1[0], IsConst(), inserter(vars, vars.begin()));
      // Expects normalized exprs.

      ExprVector forms;
      for (auto it = forms1.begin(); it != forms1.end(); it++)
      {
        if (debug > 0)
          outs() << "Processing: " << *it << "\n";
        ExprVector conjs;
        getConj(*it, conjs);
        if (conjs.size() > 2)
        {
          bool keepGoing = trySimplifying(conjs);
          if (!keepGoing)
            return;
          if (debug > 4)
            outs() << "Keep going after simplifying: " << *it << "\n";
        }

        forms.push_back(conjoin(conjs, m_efac));
      }

      linCombIneq(srcRel, forms, dc);

      for (auto &it : dc[srcRel])
      {
        if (debug > 0)
          outs() << "Data candidate: " << simplifyArithm(it) << "\n";
      }
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
      map<Expr, ExprSet> dc;

      makeModel(invDecl, BigPhi, dc);

      for (auto c = dc[invDecl].begin(); c != dc[invDecl].end();)
      {
        if (debug >= 4)
          outs() << "  cands: " << *c << "\n";
        if (!u.isSat(*c, tr->body))
        {
          if(debug >= 2) outs() << "  Removed: " << *c << "\n";
          c = dc[invDecl].erase(c);
        }
        else
        {
          ++c;
        }
      }

      return dc[invDecl];
    }

    void infer(ExprVector& ev, ExprSet& inferred)
    {
      if (debug >= 4)
        outs() << "...Inferring...\n";
      for (int i = 0; i < ev.size(); i++)
      {
        Expr c = ev[i];
        c = simplifyArithm(c);
        c = u.removeRedundantConjuncts(c);
        if (debug >= 4)
          outs() << "  c: " << c << "\n";
        ExprVector inferSeeds;
        if (isOpX<EQ>(c))
        {
          inferSeeds = {mk<GEQ>(c->left(), c->right()),
                        mk<LEQ>(c->left(), c->right())};
        }
        else
        {
          inferSeeds = {c};
        }

        if (i == 0)
        {
          inferred.insert(inferSeeds.begin(), inferSeeds.end());
        }
        else
        {
          for (auto itr = inferred.begin(); itr != inferred.end();)
          {
            bool toBreak = false;
            if (!u.implies(c, *itr) || u.implies(*itr, c))
            {
              if (debug >= 4)
                outs() << "  Erasing: " << *itr << "\n";
              itr = inferred.erase(itr);
              toBreak = true;
              if (inferred.empty())
                inferred.insert(c);
            }
            if (toBreak)
              break;
            itr++;
          }
        }

        if (debug >= 4)
        {
          outs() << "Current inferred:\n";
          pprint(inferred, 2);
          outs() << "\n";
        }
      }
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

      splitExprs(BigPhi, infMap);
      if (debug >= 4)
      {
        for(auto& m: infMap)
        {
          for(auto& mm : m.second)
          {
            outs() << "  From infMap: " << mm << "\n";
          }
          outs() << "\n";
        }
      }

      for(auto ev: infMap)
      {
        ExprSet inferred;
        infer(ev.second, inferred);
        
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

      res = dl2.connectPhase(src, dst, n, invDecl, block, invs, loopGuard, doGJ, doConnect);
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

      ExprVector rowsExpr = dl2.exprForRows(invDecl);

      for(auto& r: rowsExpr)
      {
        if(debug >= 3) outs() << "  rowsExpr: " << r << "\n";
        for(auto itr = candMap[invDecl].begin(); itr != candMap[invDecl].end();)
        {
          if(!u.isSat(r, *itr))
          {
            if(debug >= 3) outs() << "  Removed: " << *itr << "\n";
            itr = candMap[invDecl].erase(itr);
          }
          else
          {
            ++itr;
          }
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

    Expr weakenAndSplit(ExprVector& BigPhi, Expr bound) 
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
          outs() << "  From BigPhi: " << c << std::endl;;
        }
      }

      ExprSet inferred = infer(BigPhi);
      // u.removeRedundantConjuncts(inferred);
      Expr c = conjoin(inferred, m_efac);
      if(debug >= 4) outs() << "  c: " << c << "\n";
      boost::tribool safe = checkSafety(c, bound);

      if(debug >= 4) 
      {
        if(!safe) outs() << "\n\n********\n*UNSAFE*\n********\n\n";
        else outs() << "\n\n******\n*SAFE*\n******\n\n";
      }

      if(!safe) return mk<TRUE>(m_efac);
      if(debug >= 4) outs() << "  Result from checkSafety: " << c << " => " << replaceAll(bound, fc->srcVars, tr->srcVars) << "\n";
      return c;
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
      Expr lg = replaceAll(loopGuard, rm.invVars[invDecl], vars[vars.size() - 1]);
      if(debug >= 5) outs() << "  gh value (vars replaced): " << fg << "\n";

      phi = mk<AND>(phi, mk<AND>(fg,mkNeg(lg)));
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

    boost::tribool toKeep(Expr p)
    {
      ExprVector vars;
      filter(p, IsConst(), inserter(vars, vars.begin()));
      ExprVector conjs;
      getConj(p, conjs);
      u.isSat(p);
      Expr model = u.getModel();
      outs() << "Model: " << model << "\n";
      ExprSet models;
      getConj(model, models);
      ExprSet negModels;
      for(auto m = models.begin(); m != models.end(); m++)
      {
        negModels.insert(mkNeg(*m));
        outs() << "Model: " << *m << "\n";
      }
      Expr m = mk<AND>(conjoin(negModels, m_efac), p);
      outs() << "Model: " << m << "\n"; 
      boost::tribool res = u.isSat(m);
      if(res) outs() << "SAT\n";
      else outs() << "UNSAT\n";

      return  res;
    }

    vector<ExprVector> abds;
    vector<ExprVector> allCombs;
    Expr getPre(Expr p, Expr f, int n)
    {
      // p holds the conjunction of the negated previous preconditions.
      // f is the data invariant.
      // n is the number of iterations.
      // returns the precondition for the next iteration.

      if(debug >= 2) outs() << "\n\nGet Pre\n=======\n";

      if(debug >= 5)
      {
        outs() << "  p: ";
        pprint(p, 2);
        outs() << "  f: ";
        pprint(f, 2);
        outs() << "  n: " << n << "\n";
      }

      ExprSet Phi;
      CHCs rm(m_efac, z3, debug);

      vector<HornRuleExt*> rules;
      rules.push_back(&fc_nogh);
      rules.push_back(&tr_nogh);
      rules.push_back(&qr_nogh);
      prepareRuleManager(rm, rules);

      // for(auto& hr: rm.chcs)
      // {
      //   if(hr.isFact)
      //   {
      //     hr.body = mk<AND>(hr.body, replaceAll(p, invVars, invVarsPr));
      //     if(debug >= 4) outs() << "  hr.body: " << hr.body << "\n";
      //   }
      // }

      BndExpl bnd(rm, (debug > 0));
      ExprVector BigPhi;
      Expr bound;

      abds.clear();
      allCombs.clear();
      for(int k = 1; k <= n; k++) 
      {
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
        Expr elim = simplifyArithm(abduction(phi, f, bound, k, vars, trace, bnd, rm));

        // value of y = 1, y = 2, y = 4... make an example like this.
        // needs to handle many variables.

        // if (debug >= 4)
        // {
        //   outs() << "  phi: ";
        //   pprint(phi, 2);
        // }
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

        // filter the projections somehow. We only want ones relevant to the current search.

        for(auto& p: prjcts2)
        {
          if(debug >= 4) outs() << "  Checking Projection: " << simplifyArithm(p) << "\n";
          // TODO: Filter using models.
          if(!toKeep(p))
            prjcts.push_back(simplifyArithm(p));
        }

        abds.push_back(prjcts);

        // for(int i = 0; i < abds.size(); i++)
        // {
        //   for(int j = 0; j < abds[i].size(); j++)
        //   {
        //     if(debug >= 4) outs() << "  Abduction " << i << ": " << abds[i][j] << "\n\n";
        //   }
        // }

        // for(auto p: prjcts)
        // {
        //   if(debug >= 5) outs() << "  Projection: " << p << "\n";
        //   // TODO: Check the projections iteratively as combinations.
        //   // Run through the rest of
        //   if (debug >= 3)
        //   {
        //     outs() << "  ADDED TO BIGPHI: " << simplifyArithm(normalize(p, true)) << "\n";
        //   }
        //   BigPhi.push_back(p);
        // }

        // if(debug >= 5) outs() << "  Ghost Value: " << ghostValue << "\n";
      }

      if(abds.size() < 1) return mk<TRUE>(m_efac);
      // abds.erase(abds.begin());

      for(int i = 0; i < abds.size(); i++)
      {
        for(int j = 0; j < abds[i].size(); j++)
        {
          if(debug >= 4) outs() << "  AAbduction " << i << ": " << abds[i][j] << "\n";
        }
      }
      getAllCombs(allCombs, abds, 0);
      if(debug >= 4)
      {
        outs() << "  All Combs size: " << allCombs.size() << "\n";
        int i = 0;
        for(auto& c: allCombs)
        {
          for(auto& cc: c)
          {
            outs() << "Comb " << i << ": " << cc << "\n";
          }
          i++;
        }
      }
      Expr c = mk<TRUE>(m_efac);

      for(int i = 0; i < allCombs.size(); i++)
      {
        ExprVector current;
        for(int j = 0; j < allCombs[i].size(); j++)
        {
          current.push_back(allCombs[i][j]);
        }

        if(debug >= 3) 
        {
          outs() << "  current projs:\n";
          pprint(current);
          outs() << "\n\n";
        }
        Expr c = weakenAndSplit(current, bound);
        if(debug >= 3) outs() << "  Result from W&S: " << c << "\n";
        if(c != mk<TRUE>(m_efac)) return c;

      }

      return c;
    }

    void getAllCombs(vector<ExprVector>& allCombs, vector<ExprVector>& abds, int i)
    {
      if(abds.empty()) return;  
      if(debug >= 4)
      {
        outs() << "  All Combs size: " << allCombs.size() << "\n";
        int i = 0;
        for(auto& c: allCombs)
        {
          for(auto& cc: c)
          {
            outs() << "Comb " << i << ": " << cc << "\n";
          }
          i++;
        }
      }      

      outs() << "i: " << i;
      int j = abds[i].size();
      outs() << "  j: " << j << "\n";

      if(i == 0)
      {
        for(int d = 0; d < j; d++)
          allCombs.push_back({abds[i][d]});
        outs() << "allCombs.size() 0 " << allCombs.size() << "\n";
      }
      else
      {
        vector<ExprVector> temp;

        for(int l = 0; l < j; l++)
        {
          for(int k = 0; k < allCombs.size(); k++)
          {
            temp.push_back(allCombs[k]);
          }
        }

        int jPrev = abds[i-1].size();
        int k = 0;
        for(int l = 0; l < temp.size(); l++)
        {
          outs() << "j: " << j << "  jPrev: " << jPrev << "  l: " << l << "  k: " << k << "\n";
          if(l != 0 && l % jPrev == 0) k++;
          if(k >= abds[i].size()) break;
          temp[l].push_back(abds[i][k]);
        }
        
        allCombs = temp;
      } 


      if(i + 1 >= abds.size()) return;
      getAllCombs(allCombs, abds, i + 1);
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
          p = simplifyArithm(p);
          if (p != mk<FALSE>(m_efac))
            bounds[p] = mkMPZ(0, m_efac);
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
            m.push_back(i+1);
            // update to use models for data learning.
            model = u.getModel();
            if (debug >= 5)
            {
              outs() << "  i: " << m.back() << "\n";
              outs() << "  Model: ";
              pprint(model, 2);
            } 

            // if(i > 5) break;
          }
          else if(debug >= 4) { outs() << "  ====  SSA is UNSAT\n"; }
        }

        ghostGuard = setGhostGuard(mkMPZ(0, m_efac));
        qr->body = mk<AND>(mkNeg(loopGuard), ghostGuard);

        bool nonterm = false;
        if(m.empty()) // this is a check to see if we have a nonterminating case.
        {
          // ExprSet f;
          // f.insert(mk<EQ>(ghostVars[0], mkMPZ(-1, m_efac)));
          // forms[invDecl] = f;
          // bounds[p] = *f.begin();
          ghostGuard = setGhostGuard(mkMPZ(-1,m_efac));
          qr->body = mk<AND>(loopGuard, ghostGuard);
          m.push_back(1);
          nonterm = true;
        }
        // else
        // {
          // get forms from data.
          // TODO: Make parametric so that different algorithms can be called.
          if(debug >= 4)
          {
            outs() << "  m: ";
            for(auto& i: m) outs() << i << " ";
            outs() << "\n";
          }
          res = invFromData(fc->body, qr->body, p, forms, m.back());
          // if(nonterm) exit(0);
          // }

          if (res == true)
          {
            ExprSet invs;
            Expr psi;

            ExprVector formsVec;
            for (auto &s : forms[invDecl])
            {
              formsVec.push_back(s);
            }

            sortBounds(formsVec);

            if (debug >= 3)
            {
              outs() << "  ==> Sorted invs from data:\n";
              pprint(formsVec, 4);
            }

            for (auto &f : formsVec)
            {
              if (debug >= 3)
                outs() << "Trying next bound: " << f << "\n";
              bool toContinue = false;
              for (auto &b : bounds)
              {
                if (b.second == f)
                {
                  if (debug >= 4)
                    outs() << "  Bound already found\n";
                  toContinue = true;
                }
              }
              if (toContinue)
                continue;

              psi = getPre(p, f, m.back());
              psi = simplifyArithm(psi);
              if(debug >= 4) outs() << "  psi after getPre: " << psi << "\n";
              if (psi != mk<TRUE>(m_efac) && psi != mk<FALSE>(m_efac))
              {
                if (debug >= 2)
                {
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
      for (auto b = bounds.begin(); b != bounds.end(); b++)
      {
        if(!u.isSat(mkNeg(b->first), replaceAll(fc_nogh.body, invVarsPr, invVars)))
        {
          outs() << b->second;
          break;
        }
        else
        {
          if(b != bounds.begin())
          {
            outs() << ", ";
          }
          if(b == --bounds.end())
          {
            outs() << b->second;
          }
          else
          {
            outs() << "  ite " << b->first << ", " << b->second;
          }
        }
        i++;
      }
      outs() << "\n";
    }
  }; // End class BoundSolverV2

  // TODO: Rewrite the infer function according to the notes above.
  // TODO: Test implementation over more benchmarks.

  inline void learnBoundsV2(string smt, int inv, int stren, bool dg,
                                  bool data2, bool doPhases, int limit, bool gj, bool dc, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);

    ruleManager.parse(smt, false);

    // TODO: Add preprocessing to replace constants with variables.

    BoundSolverV2 bs(ruleManager, inv, dg, data2, doPhases, limit, gj, dc, debug);
    bs.removeQuery();
    bs.setUpQueryAndSpec(mk<TRUE>(m_efac), mk<TRUE>(m_efac));
    // bs.collectPhaseGuards();

    bs.solve();
    // Print the results.
    bs.printResults();
  }
}

#endif // BOUND_SOLVER_V2_HPP
