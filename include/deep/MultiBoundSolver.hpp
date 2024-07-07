#ifndef MULTIBOUNDSOLVER_HPP
#define MULTIBOUNDSOLVER_HPP

#include "BoundSolverV2.hpp"

namespace ufo {
  class MultiBoundSolver {
  private:

    CHCs &ruleManager;
    ExprFactory &m_efac;
    ZSolver<EZ3> smt;
    EZ3 z3;
    SMTUtils u;

    int debug = 0;

    int inv;
    int stren;
    bool dg;
    bool data2;
    bool doPhases;
    int strenBound;
    
    int n; // parameter to control the number of trace iterations.
    int limit;
    int to = 100;
    int freqs = 1;
    int aggp = 1;
    int mut = 1;
    int dat = 1;
    int doProp = 0;
    int mutData = 0;

    // For RndLearner
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
    bool absConsts = false;
    bool dataInfer = false;
    bool imp = false;
    bool mutateInferred = false;
    bool sepOps = false;
    bool checkProj = false;

    vector<pair<Expr, Expr>> graphPairs;
    map<Expr, CHCs *> rms; // One map to rule(Manager) them all.
    map<Expr, bool> nestedLoops;
    vector<ExprVector> primePaths;

    map<Expr, BoundSolverV2 *> elbas;
    map<Expr, ExprSet> bounds;

  public:
    // Constructor
    MultiBoundSolver(CHCs &r, int _b, bool _dg, bool d2, bool _dp, int _limit, bool gj,
                     bool dc, bool abConsts, bool iwd, bool _imp, bool mi, bool _sepOps,
                     bool _tk, int md, int dbg)
        : m_efac(r.m_efac), ruleManager(r), u(m_efac), smt(z3), z3(m_efac), debug(dbg),
          strenBound(_b), dg(_dg), data2(d2), doPhases(_dp), limit(_limit), n(_limit),
          doGJ(gj), doConnect(dc), absConsts(abConsts), dataInfer(iwd), imp(_imp),
          mutateInferred(mi), sepOps(_sepOps), checkProj(_tk), mutData(md)
    {
      outs() << "Made it here\n";
      exit(0);
    }

    HornRuleExt *makeNewTr(Expr body, Expr rel, CHCs &ruleManager)
    {
      HornRuleExt *tr_new = new HornRuleExt();

      tr_new->srcRelation = rel;
      tr_new->srcVars = ruleManager.invVars[rel];
      tr_new->dstRelation = rel;
      tr_new->dstVars = ruleManager.invVarsPrime[rel];
      tr_new->isInductive = true;
      tr_new->body = body;

      return tr_new;
    }

    ExprSet filterForChangedVars(ExprSet prevConjs, int debug = 0)
    {
      ExprSet vars;
      for (auto &e : prevConjs)
      {
        if (debug >= 4)
          outs() << "PREV: " << e << "\n";
        if (isOp<NumericOp>(e->right()))
        {
          filter(e, bind::IsConst(), inserter(vars, vars.end()));
        }
      }
      if (debug >= 4)
        for (auto &e : vars)
          outs() << "VAR: " << e << "\n";
      return vars;
    }

    Expr filterForInitExpr(Expr expr, ExprSet &vars, int debug = 0)
    {
      ExprSet tmp;
      ExprSet tmp2;
      getConj(expr, tmp);

      for (auto &v : vars)
      {
        for (auto i = tmp.begin(); i != tmp.end(); i++)
        {
          Expr e = normalize(*i);
          if (debug >= 5)
            outs() << "filterForInitExpr: " << e << "\n";
          if (contains(e->left(), v))
          {
            tmp2.insert(*i);
          }
        }
      }

      if (debug >= 5)
        for (auto &v : tmp2)
          outs() << "Remain: " << v << "\n";

      for (auto i = tmp2.begin(); i != tmp2.end();)
      {
        Expr e = normalize(*i);
        if (isOpX<EQ>(e) && isNumeric(e->right()))
        {
          i++;
        }
        else
        {
          i = tmp2.erase(i);
        }
      }
      tmp.clear();
      for (auto &v : tmp2)
      {
        tmp.insert(v);
      }
      if (debug >= 5)
        for (auto &v : tmp2)
          outs() << "Remain Again: " << v << "\n";
      return conjoin(tmp, expr->getFactory());
    }

    Expr concatLoopBody(int cycleNum1, int cycleNum2, CHCs &ruleManager, Expr prevTr, int debug = 0)
    {
      // Need a double primed var set to differentiate between top and bottom halves of the loop.

      if (debug >= 4)
        outs() << "cyc1: " << cycleNum1 << "  |  cyc2: " << cycleNum2 << "\n";
      ExprSet topBody;
      Expr top = ruleManager.chcs[cycleNum1].body;
      if (debug >= 4)
        outs() << "TOP: " << top << "\n";
      getConj(ruleManager.chcs[cycleNum1].body, topBody);
      Expr botBody = ruleManager.chcs[cycleNum2].body;
      if (debug >= 4)
        outs() << "BOT: " << botBody << "\n";
      Expr preCond2 = ruleManager.getPrecondition(&ruleManager.chcs[cycleNum2]);

      if (debug >= 4)
        outs() << "PreCond2: " << preCond2 << "\n";
      ExprSet bodyConjsBot;
      ExprSet preCondSetBot;
      preCondSetBot.insert(preCond2);
      getConj(botBody, bodyConjsBot);
      minusSets(bodyConjsBot, preCondSetBot);
      bodyConjsBot.insert(preCond2);

      if (debug >= 4)
        for (auto &e : bodyConjsBot)
          outs() << "  |  " << e << "\n";

      botBody = conjoin(bodyConjsBot, ruleManager.m_efac);
      if (debug >= 4)
        outs() << "New BOT: " << botBody << "\n";
      topBody.insert(bodyConjsBot.begin(), bodyConjsBot.end());
      Expr newTr = conjoin(topBody, ruleManager.m_efac);
      if (debug >= 4)
        outs() << "New TR first: " << newTr << "\n";
      ExprSet newTrConj;
      getConj(newTr, newTrConj);

      // Expr prevTr;
      Expr rel = ruleManager.chcs[cycleNum1].dstRelation;
      if (prevTr == NULL)
      {
        for (auto &hr : ruleManager.chcs)
        {
          if (hr.isInductive && hr.srcRelation == rel)
          {
            prevTr = hr.body;
          }
        }
      }
      if (debug >= 4)
        outs() << "Prev Tr: " << prevTr << "\n";
      ExprSet prevConjs;
      getConj(prevTr, prevConjs);
      ExprSet innerLoopVars = filterForChangedVars(prevConjs, debug);
      if (debug >= 5)
        outs() << "newTR before: " << newTr << "\n";
      Expr initInfo = filterForInitExpr(newTr, innerLoopVars, debug);
      // initInfo = replaceAll(initInfo, ruleManager.invVarsPrime[rel], ruleManager.invVars[rel]);
      if (debug >= 5)
        outs() << "initInfo: " << initInfo << "\n";
      newTr = weakenForVars(newTr, innerLoopVars);
      if (debug >= 5)
        outs() << "newTR after: " << newTr << "\n";

      ExprSet conjs;
      getConj(newTr, conjs);
      for (auto e = conjs.begin(); e != conjs.end();)
      {
        if (isOpX<EQ>(*e) && !isOp<NumericOp>((*e)->right()))
        {
          if (debug >= 5)
            outs() << "ERASING: " << *e << "\n";
          e = conjs.erase(e);
        }
        else
          e++;
      }
      // ExprSet vars = filterForChangedVars(conjs);
      conjs.insert(initInfo);
      newTr = conjoin(conjs, ruleManager.m_efac);
      if (debug >= 5)
        outs() << "New TR: " << newTr << "\n";
      if (!ruleManager.u.isSat(newTr))
      {
        outs() << "NewTr is not satisfiable\n";

        exit(1);
      }

      return newTr;
    }

    void checkForNesting(CHCs &ruleManager, ExprVector &loop,
                         map<Expr, bool> &nestedLoops, int debug = 0)
    {
      // Look for nesting and add the loops to the ExprVector.
      int sz = loop.size();
      if (debug >= 3)
      {
        outs() << "\nPrime path: ";
        for (int i = 0; i < loop.size(); i++)
        {
          if (i > 0)
            outs() << " -> ";
          outs() << loop[i];
        }
        outs() << "\n";
      }
      for (auto l = loop.begin(); l != loop.end();)
      {
        if (nestedLoops[*l])
        {
          Expr rel = *l;
          for (auto &hr : ruleManager.chcs)
          {
            if (rel == hr.srcRelation && containsExpr(hr.dstRelation, loop))
            {
              l = loop.insert(++l, hr.dstRelation);
              break;
            }
          }
        }
        else
        {
          l++;
        }
      }
      if (debug >= 2 && loop.size() > sz)
      {
        outs() << "\nPath with nested loops: ";
        for (int i = 0; i < loop.size(); i++)
        {
          if (i > 0)
            outs() << " -> ";
          outs() << loop[i];
        }
        outs() << "\n\n";
      }
    }

    // adapted from BndExpl:: getAllTraces
    bool getPrimePaths(Expr src, Expr dst, int len, ExprVector trace,
                       vector<ExprVector> &traces, vector<pair<Expr, Expr>> &graphPairs, int debug)
    {
      if (len == 1)
      {
        for (auto a : graphPairs)
        {
          if (a.first == src && a.second == dst)
          {
            for (auto &b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1)
                  outs() << "looking for prime paths only\n";
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
        for (auto a : graphPairs)
        {
          if (a.first == src)
          {
            for (auto &b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1)
                  outs() << "looking for prime paths only\n";
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(a.second);
            bool res = getPrimePaths(a.second, dst, len - 1, newtrace, traces, graphPairs, debug);
            if (!res)
              return false;
          }
        }
      }

      return true;
    }

    bool findPrimePaths(Expr first, Expr last, vector<ExprVector> &primePaths,
                        vector<pair<Expr, Expr>> &graphPairs, int debug)
    {
      ExprSet init;
      bool res = false;
      init.insert(first);

      for (auto &in : init)
      {
        int len = primePaths.size();
        for (int i = 1; i <= graphPairs.size(); i++)
        {
          res = getPrimePaths(in, last, i, {in}, primePaths, graphPairs, debug);
          // if (!res) return false;
        }
        if (debug >= 3)
          outs() << "paths size: " << primePaths.size() << "\n";
        assert(primePaths.size() > len && "No paths found\n");
      }

      if (debug >= 2)
      {
        outs() << "\n====== PRIME PATHS ======\n\n";
        for (auto &p : primePaths)
        {
          outs() << "Found path: ";
          for (int i = 0; i < p.size(); i++)
          {
            if (i > 0)
              outs() << " -> ";
            outs() << p[i];
          }
          outs() << "\n";
        }
        outs() << "\n=========================\n";
      }

      return res;
    }

    void setUpElbas(bool ranOnceAlready, Expr prevBound, Expr prevGrd, Expr inv)
    {
      if (ranOnceAlready)
      {
        elbas[inv]->removeQuery(); // Removes the dummy query added for parsing.
        if (nestedLoops[inv])
        { // The ghost decrement should be of the value of the previously found guard.
          elbas[inv]->decrementByNestedBound(prevBound->right());
          elbas[inv]->setUpQr(prevGrd, mk<EQ>(prevBound->left(), mkMPZ(0, prevBound->getFactory())));
        }
        else
        {
          elbas[inv]->setUpQr(prevGrd, prevBound);
        }
      }
      else
      {
        elbas[inv]->removeQuery(); // Removes the dummy query added for parsing.
        if (!nestedLoops[inv])
        {
          elbas[inv]->setUpQueryAndSpec(prevGrd, prevBound);
        }
        if (nestedLoops[inv])
        { // The ghost decrement should be of the value of the previously found guard.
          elbas[inv]->setUpQueryAndSpec(prevGrd, mk<EQ>(prevBound->left(), mkMPZ(0, prevBound->getFactory())));
          elbas[inv]->decrementByNestedBound(prevBound->right());
        }
      }
    }

    void solveElbas()
    {
      // Calculate bounds for each loop.
      if (debug >= 2)
        outs() << "\n====== Calculate Bounds ======\n\n";

      Expr new_name = mkTerm<string>("_gh_" + to_string(0), ruleManager.m_efac);
      Expr var = bind::intConst(new_name);

      Expr ghostGuard = mk<EQ>(var, mkMPZ(0, ruleManager.m_efac));

      if (debug >= 4)
        for (auto &l : ruleManager.loopheads)
          outs() << "Loophead: " << l << "\n";

      for (auto &v : primePaths)
      {
        ExprVector path = v;
        Expr lastLoophead = *path.rbegin();
        bounds[lastLoophead].insert(ghostGuard);

        checkForNesting(ruleManager, path, nestedLoops, debug);

        for (auto l = path.rbegin(); l != path.rend(); l++)
        {
          if (containsExpr(*l, ruleManager.loopheads))
          {
            // *l is not a loophead
            // These are the "branching" or "bridge" CHCs.
            // There should be some analysis that takes the branching
            // condition and adds it to the bound being computed.
            if (debug >= 4)
              outs() << *l << " is NOT inductive\n";
            HornRuleExt *br;
            Expr preCond;
            bool isInit = false;
            for (auto &hr : ruleManager.chcs)
            {
              if (hr.srcRelation == *l && hr.dstRelation == lastLoophead)
              {
                preCond = ruleManager.getPrecondition(&hr);
                if (hr.isFact)
                  isInit = true;
                if (debug >= 4)
                  outs() << "BRIDGE CHC: " << *l << " => " << lastLoophead << "\n";
              }
            }
            if (isInit || nestedLoops[*l] || preCond == NULL)
              continue;
            if (debug >= 4)
              outs() << "PRECOND: " << preCond << "\n";
            ExprSet prevBounds = bounds[lastLoophead];
            ExprSet tmp;
            for (auto &b : prevBounds)
            {
              if (debug >= 4)
                outs() << "b: " << b->left() << "\n";
              tmp.insert(mk<IMPL>(mk<AND>(preCond, b->left()), b->right()));
            }
            bounds[lastLoophead].swap(tmp);
          }
          else
          {
            // *l is a loophead
            if (debug >= 4)
              outs() << *l << " is loophead\n";

            ExprSet prevBounds = bounds[lastLoophead];
            if (l == path.rbegin())
            {
              bounds[lastLoophead].clear();
            }

            lastLoophead = *l;

            bool ranOnceAlready = false;
            elbas[*l] = new BoundSolverV2(*rms[*l], stren, dg, data2, doPhases, limit,
                                          doGJ, doConnect, absConsts, dataInfer, imp, 
                                          mutateInferred, sepOps, checkProj, mut, debug);
            int counter = 0;
            // From here hide the preprocessing.
            for (auto &bnd : prevBounds)
            {
              if (debug >= 4)
                outs() << "Loop " << *l << " Bound " << counter++ << std::endl;
              Expr b = bnd;
              Expr prevGrd, prevBound;
              if (isOpX<IMPL>(b))
              {
                prevGrd = b->left();
                prevBound = b->right();
              }
              else
              {
                prevGrd = mk<TRUE>(ruleManager.m_efac);
                prevBound = b;
              }

              if (debug >= 4)
                outs() << "\n====> NEXT BOUND: " << b << std::endl;

              setUpElbas(ranOnceAlready, prevBound, prevGrd, *l);

              outs() << "\nHERE\n\n";

              // New ELBA algorithm starts here.
              elbas[*l]->solve();
              // bounds[*l].insert(results.begin(), results.end());

              // bool badGuard = elbas[*l]->collectPhaseGuards();
              // if(!badGuard) {
              //   if(debug >= 4) outs() << "Infeasible path" << std::endl;
              //   // Previous guard leads to an infeasible path.
              // }
              // else {
              //   if (debug >= 3) elbas[*l]->printPhases();
              //   ExprSet results = elbas[*l]->pathsSolve();
              //   bounds[*l].insert(results.begin(), results.end());
              // }
              ranOnceAlready = true;
            }
            if (debug >= 2 && !bounds[*l].empty())
            {
              outs() << "\n====================";
              outs() << "====================\n";
              outs() << "BOUND so far " << *l << ": \n";
              pprint(bounds[*l], 5);
              outs() << "\n====================";
              outs() << "====================\n"
                     << std::endl;
            }
          }
        }
      }

      for (auto l = ruleManager.loopheads.rbegin(); l != ruleManager.loopheads.rend(); l++)
      {

        if (!bounds[*l].empty())
        {
          outs() << "\n====================";
          outs() << "====================\n";
          outs() << "FINAL " << *l << ": \n";
          pprint(bounds[*l], 5);
          outs() << "\n====================";
          outs() << "====================\n"
                 << std::endl;
        }
      }
    }

    void setUpRuleManagers()
    {
      Expr firstInv;
      Expr failDecl = ruleManager.failDecl;

      for (auto &hr : ruleManager.chcs)
      {
        if (hr.isFact)
          firstInv = hr.srcRelation;
        if (!hr.isInductive)
        {
          graphPairs.push_back(make_pair(hr.srcRelation, hr.dstRelation));
        }
      }

      if (debug >= 4)
        for (auto &gp : graphPairs)
        {
          outs() << gp.first << " -> " << gp.second << "\n";
        }

      bool foundPrimePaths = findPrimePaths(firstInv, failDecl, primePaths, graphPairs, debug);

      // Parsing is done. Now explore/organize the path information we need.
      // Use the ideas of prime paths/Cut point graph to lay out the top layer of workflow for elba.
      // At a simplified level, elba will traverse the prime paths, and at each node(loop head)
      // it will compute a bound for the loop. This bound is then propagated to the next loop
      // that is visited.
      // The prime paths are traversed from back to front.

            Expr newTr;
      for (auto &l : ruleManager.loopheads)
      {
        vector<vector<int>> cycles = ruleManager.cycles[l];

        for (auto &cc : cycles)
          if (cc.size() > 1)
          {
            nestedLoops[l] = true;
            // EXIT here since we don't support them with the new algorithm.
            // Concatenate the two parts of the outer loop.
            rms[l] = new CHCs(m_efac, z3, debug);
            newTr = concatLoopBody(cc[0], cc[1], ruleManager, newTr, debug);
            int cycleNum = cc[0];
            if (debug >= 3)
              outs() << "CycleNum: " << cycleNum << "\n";

            for (auto &hr : ruleManager.chcs)
            { // Here we only add the fact since the outer TR is not inductive.
              if (debug >= 3)
                outs() << "l: " << l << "\n";
              // This needs to change since there could be some "initialization information" in the outer loop.
              if (cycleNum == 1 && hr.isFact)
              {
                if (debug >= 5)
                  outs() << "Making FC: ";
                if (debug >= 3)
                  outs() << hr.body << "\n";
                rms[l]->addRule(&hr);
              }
              else if (cycleNum > 1 && hr.isFact)
              {
                if (debug >= 5)
                  outs() << "Making TRUE" << std::endl;
                HornRuleExt fc = hr;
                // fc.body = mk<TRUE>(m_efac);
                fc.dstRelation = ruleManager.chcs[cycleNum].srcRelation;
                rms[l]->addRule(&fc);
              }
            }
            // Add concatenated TR
            if (debug >= 5)
              outs() << "Making new TR\n";
            HornRuleExt *tr_new = makeNewTr(newTr, l, ruleManager);
            rms[l]->addRule(tr_new);

            rms[l]->dummyQuery();

            // real QR will be added when "setUpQueryAndSpec" is called.

            if (debug >= 5)
            {
              outs() << "\n==== Printing separated loop ====\n";
              rms[l]->print(true);
            }

            // call findCycles instead of wtoSort.
            rms[l]->findCycles();
            if (debug >= 5)
              outs() << "rms[" << l << "]->cycles.size() = " << rms[l]->cycles.size() << std::endl;
          }
          else
          {
            // Proceed with the single TR for this loophead.
            nestedLoops[l] = false;
            int cycleNum = cc[0];
            if (debug >= 5)
              outs() << "Single cycle : " << cycleNum << ".\n";
            rms[l] = new CHCs(m_efac, z3, debug);

            for (auto &hr : ruleManager.chcs)
            {
              if (cycleNum == 1 && hr.isFact)
              {
                rms[l]->addRule(&hr);
              }
              else if (cycleNum > 1 && hr.isFact)
              {
                HornRuleExt fc = hr;
                // fc.body = mk<TRUE>(m_efac);
                fc.dstRelation = ruleManager.chcs[cycleNum].srcRelation;
                rms[l]->addRule(&fc);
              }
              if (hr.isInductive && hr.srcRelation == l)
              {
                rms[l]->addRule(&hr);
              }
            }
            rms[l]->dummyQuery();

            // real QR will be added when "setUpQueryAndSpec" is called.

            if (debug >= 5)
            {
              outs() << "\n==== Printing separated loop ====\n";
              rms[l]->print(true);
            }
            // call findCycles instead of wtoSort.
            rms[l]->findCycles();
            if (debug >= 5)
              outs() << "rms[" << l << "]->cycles.size() = " << rms[l]->cycles.size() << std::endl;
          }
      }
      // ruleManagers set up with their "single" loops.
    }

    // Solve function. Does precprocessing, then calls solve() from BoundSolverV2.
    void solve() {
      setUpRuleManagers();
      solveElbas();
    }
  };

  inline void learnMultipleBounds(string smt, int inv, int stren, bool dg,
                                  bool data2, bool doPhases, int limit,
                                  bool gj, bool dc, bool ac, bool iwd,
                                  bool imp, bool mi, bool so, bool tk,
                                  int md, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);
    
    ruleManager.parse(smt, false);
    ruleManager.print(true);
    outs() << "Finished printing\n";

    MultiBoundSolver mbs(ruleManager, inv, dg, data2, doPhases, limit, gj,
                         dc, ac, iwd, imp, mi, so, tk, md, debug);

    mbs.solve();
  }
}

#endif // MULTIBOUNDSOLVER_HPP
