#ifndef BOUND_SOLVER_V2_HPP
#define BOUND_SOLVER_V2_HPP

#include "BoundSolver.hpp" // Include BoundSolver.hpp

namespace ufo {
  class BoundSolverV2 : public BoundSolver { // Inherit from BoundSolver
  private:
    ExprMap bounds;
    Expr fcBodyOrig;
    int n; // parameter to control the number of trace iterations.

    int to = 1000;
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
    BoundSolverV2(CHCs &r, int _b, bool _dg, bool d2, bool _dp, int limit, int dbg)
        : BoundSolver(r,_b,_dg,d2,_dp,dbg), n(limit)
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

    // Public member functions
    boost::tribool invFromData(Expr src, Expr dst, Expr block, map<Expr, ExprSet>& candMap, int n) {
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;

      outs() << "src: " << src << "\n";
      outs() << "dst: " << dst << "\n";
      outs() << "block: " << block << "\n";
      outs() << "n: " << n << "\n";

      if(debug >= 3) ruleManager.print(true);

      // Replace this to reuse the SSA that is built previously.
      res = dl2.connectPhase(src, dst, n, invDecl, block, invs, loopGuard);
      if (res == true)
      {
        dl2.getDataCands(candMap[invDecl], invDecl);
      }

      if (debug >= 2)
      {
        for (auto &e : candMap[invDecl])
        {
          outs() << "invs from data: " << e << "\n";
        }
      }
      return res;

    }

    void prepareRuleManager(CHCs& rm, vector<HornRuleExt*>& rules)
    {
      rm.addFailDecl(ruleManager.failDecl);

      for (auto &r : rules)
      {
        rm.addRule(r);
      }
      rm.findCycles();
      rm.wtoCHCs = ruleManager.wtoCHCs;
      rm.dwtoCHCs = ruleManager.dwtoCHCs;
      rm.allCHCs = ruleManager.allCHCs;
      rm.wtoDecls = ruleManager.wtoDecls;
    }

    boost::tribool checkSafety(Expr elim, Expr preCond)
    {
      // add precondition to be checked to the ruleManager.
      CHCs rm(m_efac, z3, debug);

      HornRuleExt* fc_withPrecond = fc;
      fc_withPrecond->isFact = true;
      fc_withPrecond->srcRelation = mk<TRUE>(m_efac);
      Expr fcPreCond = replaceAll(elim, tr->srcVars, fc->srcVars);
      fc_withPrecond->body = replaceAll(mk<AND>(fcPreCond, preCond), fc_withPrecond->srcVars, tr->dstVars);
      fc_withPrecond->srcVars.clear();

      ExprVector qrBody;
      getConj(qr->body, qrBody);
      for (auto c = qrBody.begin(); c != qrBody.end(); )
      {
        if (contains(*c, ghostVars[0])) c = qrBody.erase(c);
        else ++c;
      }
      qrBody.push_back(mkNeg(ghostGuard));
      qr->body = conjoin(qrBody, m_efac);
      vector<HornRuleExt*> rules;

      rules.push_back(fc_withPrecond);
      rules.push_back(tr);
      rules.push_back(qr);
      prepareRuleManager(rm, rules);

      BndExpl bnd(rm, to, debug);
      RndLearnerV4 ds(m_efac, z3, rm, to, freqs, aggp, mut, dat,
                      doDisj, mbpEqs, dAllMbp, dAddProp, dAddDat, dStrenMbp,
                      dFwd, dRec, dGenerous, debug);

      map<Expr, ExprSet> cands;
      rm.print(true);
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
      outs() << "To Calculate Statistics\n";
      ds.calculateStatistics();
      outs() << "To Deferred Priorities\n";
      ds.deferredPriorities();
      std::srand(std::time(0));
      outs() << "To Synthesize\n";
      return ds.synthesize(to);
    }

    Expr inferGT(Expr c, ExprSet vars)
    {
      ExprSet res;
      for(auto& v: vars)
      {
        outs() << "v: " << v << "\n";
        Expr gt = mk<GT>(v, mkMPZ(0, m_efac));
        if(u.implies(c, gt))
        {
          outs() << "gt: " << gt << "\n";
          res.insert(gt);
        }
      }

      return conjoin(res, m_efac);
    }

    Expr inferLT(Expr c, ExprSet vars)
    {
      ExprSet res;
      for (auto &v : vars)
      {
        Expr lt = mk<LT>(v, mkMPZ(0, m_efac));
        if (u.implies(c, lt))
        {
          res.insert(lt);
        }
      }

      return conjoin(res, m_efac);
    }

    Expr infer(Expr c)
    {
      // Break equalities into inequalities.
      // Find weakest.
      // Check that the previous expr is an overapproximation.
      // Process them in order, run simplifyArithm on each one.
      ExprSet disjs;
      getDisj(c, disjs);

      for(auto& d: disjs) {
        outs() << "d: " << d << "\n";
      }

      ExprSet vars;
      filter(c, bind::IsConst(), inserter(vars, vars.begin()));

      Expr res;
      res = inferGT(c, vars);
      res = mk<AND>(res, inferLT(c, vars));

      return res;
    }

    Expr weakenAndSplit(ExprVector& BigPhi, Expr preCond) 
    {
      // Break equalities into inequalities.
      // Find weakest.
      // Check that the previous expr is an overapproximation.
      // Process them in order, run simplifyArithm on each one.
      Expr c = disjoin(BigPhi, m_efac);
      
      outs() << "c: " << c << "\n";
      
      c = simplifyArithm(c);
      c = infer(c);

      outs() << "inferred c: " << c << "\n";

      ExprSet conjs;
      getConj(c, conjs);
      for(auto& c: conjs) {
        outs() << "c: " << c << "\n";
        boost::tribool safe = checkSafety(c, preCond);
        if(safe) outs() << "SAFE\n";
        else outs() << "UNSAFE\n";
        if(safe) return c;
      }
      return mk<TRUE>(m_efac);
    }

    Expr getPre(Expr p, Expr f, int n)
    {
      // p holds the conjunction of the negated previous preconditions.
      // f is the data invariant.
      // Expr phi = fcBodyInvVars;
      ExprSet Phi;
      // Expr g = ;
      CHCs rm(m_efac, z3, debug);
      rm.addRule(&fc_nogh);
      rm.addRule(&tr_nogh);
      rm.addRule(&qr_nogh);
      BndExpl bnd(rm, (debug > 0));
      ExprVector BigPhi;
      Expr preCond;

      for(int k = 1; k <= n; k++) {
        vector<int> trace;
        trace.push_back(0);
        for (int i = 0; i < k; i++)
        {
          trace.push_back(1);
        }
        Expr phi = bnd.toExpr(trace);
        // phi = replaceAll(phi, fc->srcVars, tr->srcVars);

        if (!u.isSat(phi))
        {
          Expr res = mk<TRUE>(m_efac);
          outs() << "phi UNSAT\n";
          return res;
        }

        trace.push_back(2);
        Expr ff = normalize(f, ghostVars[0]);
        outs() << "ff: " << ff << "\n";
        Expr fg = mk<EQ>(ff->right(), ghostValue);
        outs() << "fg: " << fg << "\n";

        ExprVector ssa;
        bnd.getSSA(trace, ssa);
        phi = conjoin(ssa, m_efac);
        vector<ExprVector> vars;
        vars = bnd.getBindVars();
        for (auto v = vars.begin(); v != vars.end(); )
        {
          if (v->size() == 0) { v = vars.erase(v); }
          else { ++v; }
        }
        for(auto& v: vars) 
        {
          outs() << "1\n"; 
          for (auto &vv : v)
          {
            outs() << vv << ", ";
          }
          outs() << "\n";
        }
        outs() << "\n\n";
        outs() << "k: " << k << "  vars size: " << vars[vars.size() - 1].size();
        outs() << "  invVars.size(): " << rm.invVars[invDecl].size() << "\n\n";
        for (int i = 1; i < k; i++)
        {
          fg = replaceAll(fg, vars[vars.size() - i - 1], vars[vars.size() - i]);
        }
        fg = replaceAll(fg, rm.invVars[invDecl], vars[vars.size() - 1]);
        outs() << "fg: " << fg << "\n";

        phi = mk<AND>(phi, fg);
        outs() << "phi: " << phi << "\n";

        // RETRY ABDUCE FROM AEVAL!!!
        // phi = bnd.toExpr(trace);
        ff = replaceAll(ff, tr->srcVars, fc->srcVars);
        preCond = ff;

        // Expr elim = eliminateQuantifiers(phi, vars[vars.size() - 2]);
        Expr elim;
        elim = eliminateQuantifiers(phi, vars[vars.size() - 1]);
        for (int i = 1; i < k; i++)
        {
          elim = eliminateQuantifiers(elim, vars[vars.size() - i - 1]);
        }
        // value of y = 1, y = 2, y = 4... make an example like this.
        // needs to handle many variables.
        if (u.implies(elim, phi))
        {
          outs() << "ERROR with abduction\n";
        }
        outs() << "phi: " << phi << "\n";
        outs() << "ELIM: " << elim << "\n";
        // elim = replaceAll(elim, vars[vars.size() - k], vars[vars.size() - k - 1]);
        for (int i = 1; i < k; i++)
        {
          elim = replaceAll(elim, vars[vars.size() - i - 1], vars[vars.size() - i]);
        }

        outs() << "GV: " << ghostValue << "\n";
        elim = replaceAll(elim, vars[0], rm.invVars[invDecl]);
        outs() << "ADDED TO BIGPHI: " << elim << "\n";
        BigPhi.push_back(elim);
      }
      // Introduce "weakenAndSplit(BigPhi)".
      Expr c = weakenAndSplit(BigPhi, preCond);

      return c;
    }

    void solve()
    {
      // Implements Alg 1 and Alg 2 from the paper "Exact Loop Bound Analysis"
      
      Expr prevPsi;
      // use exprset including fc->body and tr->body and the negation of the bound guard
      while (true)
      {
        Expr p = mk<TRUE>(m_efac);
        for (auto &b : bounds)
        {
          Expr psi = b.first;
          p = mk<AND>(p, mkNeg(psi));
        }

        Expr phi = mk<AND>(p, fc->body, tr->body);
        outs() << "phi: " << phi << "\n";

        if (!u.isSat(phi))
        {
          outs() << "phi is UNSAT\n";
          bounds[simplifyArithm(p)] = mkMPZ(0, m_efac);
          return;
        }
        outs() << "phi is SAT\n";


        // rewrite to be more efficient.
        boost::tribool res;
        map<Expr, ExprSet> forms;
        Expr model;
        int m = -1;
        for(int i = 0; i < n; i++)
        {
          vector<int> trace;
          BndExpl bnd(ruleManager, (debug > 0));

          trace.push_back(0); // We know we have a single loop system.
          for (int k = 0; k < i; k++) trace.push_back(1);
          trace.push_back(2);
          outs() << "Trace information: size: ";
          outs() << trace.size() << "\n";
          for (auto &t : trace)
            outs() << t << "  ";
          outs() << "\n\n";

          Expr ssa;
          ssa = mk<AND>(p, bnd.toExpr(trace));
          if(debug >= 3) {
            outs() << "SSA: ";
            pprint(ssa, 2);
          }
          if(u.isSat(ssa))
          {
            m = i;
            // update models to use for data learning.
            model = u.getModel(ssa);
            outs() << "Model: " << model << "\n";
          }
        }

        if(m == -1) // this is a check to see if we have a nonterminating case.
        {
          ExprSet f;
          f.insert(mkMPZ(-1, m_efac));
          forms[invDecl] = f;
        }
        else
        {
          // get forms from data.
          // Make parametric so that different algorithms can be called.
          res = invFromData(fc->body, qr->body, p, forms, m);
        }

        ExprSet invs;
        Expr psi;

        for (auto &f : forms[invDecl])
        {
          psi = getPre(p, f, n);
          psi = simplifyArithm(psi);
          outs() << "psi: " << psi << "\n";
          if(psi != mk<TRUE>(m_efac))
          {
            bounds[psi] = normalize(f, ghostVars[0]);
          }
        }
      }
    }

    void printResults()
    {
      outs() << "Success! Found bounds:\n";
      int i = 0;
      for (auto &b : bounds)
      {
        if(i < bounds.size() - 1)
          outs() << "  ite " << b.first << ", " << b.second;
        else
          outs() << ", " << b.second << "\n";
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

    bs.solve();
    // Print the results.
    bs.printResults();
  }
}

#endif // BOUND_SOLVER_V2_HPP
