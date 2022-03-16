#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "HornNonlin.hpp"
#include "Distribution.hpp"
#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
    private:

    ExprFactory &m_efac;
    SMTUtils u;
    CHCs& ruleManager;
    Expr extraLemmas;

    ExprVector bindVars1;

    int tr_ind; // helper vars
    int pr_ind;
    int k_ind;

    Expr inv;   // 1-inductive proof
    Expr invExpr;
    ExprVector srcVars;
    int invIndex;

    bool debug;

    public:

    map<Expr, ExprSet> concrInvs;

    BndExpl (CHCs& r, bool dbg = false) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac), debug(dbg)
    {
      invExpr = r.invRel;
      srcVars = r.invVars[invExpr];
    }

    BndExpl (CHCs& r, Expr lms, bool dbg = false) :
      m_efac(r.m_efac), ruleManager(r), u(m_efac), extraLemmas(lms), debug(dbg)
    {
      invExpr = r.invRel;
      srcVars = r.invVars[invExpr];
    }

    void guessRandomTrace(vector<int>& trace)
    {
      std::srand(std::time(0));
      Expr curRel = mk<TRUE>(m_efac);

      while (curRel != ruleManager.failDecl)
      {
        int range = ruleManager.incms[curRel].size();
        int chosen = guessUniformly(range);
        int chcId = ruleManager.incms[curRel][chosen];
        curRel = ruleManager.chcs[chcId].dstRelation;
        trace.push_back(chcId);
      }
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace, vector<vector<int>>& traces)
    {
      if (len == 1)
      {
        for (auto a : ruleManager.incms[src])
        {
          if (ruleManager.chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : ruleManager.incms[src])
        {
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(ruleManager.chcs[a].dstRelation, dst, len-1, newtrace, traces);
        }
      }
    }

    Expr compactPrefix (int num)
    {
      vector<int>& pr = ruleManager.prefixes[num];
      if (pr.size() == 0) return mk<TRUE>(m_efac);

      Expr pref = toExpr(pr);

      ExprSet quantified;
      filter (pref, bind::IsConst(), inserter (quantified, quantified.begin ()));
      for (auto & a : bindVars.back()) quantified.erase(a);

      if (!ruleManager.hasArrays && !findNonlin(pref) &&
          !containsOp<IDIV>(pref) && !containsOp<MOD>(pref)) // current limitations
      {
        if (quantified.size() > 0)
        {
          AeValSolver ae(mk<TRUE>(m_efac), pref, quantified);
          ae.solve();
          pref = ae.getValidSubset();
        }
      }
      else
      {
        pref = simpleQE(pref, quantified);
      }

      return replaceAll(pref, bindVars.back(), srcVars);
    }

    vector<ExprVector> bindVars;

    Expr toExpr(vector<int>& trace)
    {
      ExprVector ssa;
      getSSA(trace, ssa);
      return conjoin(ssa, m_efac);
    }

    void getSSA(vector<int>& trace, ExprVector& ssa)
    {
      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = srcVars;
      int bindVar_index = 0;
      int locVar_index = 0;

      for (int s = 0; s < trace.size(); s++)
      {
        auto &step = trace[s];
        bindVars2.clear();
        HornRuleExt& hr = ruleManager.chcs[step];
        Expr body = hr.body;
        if (!hr.isFact && extraLemmas != NULL) body = mk<AND>(extraLemmas, body);

        for (int i = 0; i < srcVars.size(); i++)
        {
          body = replaceAll(body, srcVars[i], bindVars1[i]);
        }

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < srcVars.size(); j++)
          {
            if (hr.dstVars[i] == srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr.dstVars[i],new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__loc_var_" + to_string(locVar_index++), m_efac);
          Expr var = cloneVar(hr.locVars[i], new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }
    }

    boost::tribool exploreTraces(int cur_bnd, int bnd, bool print = false)
    {
      boost::tribool unsat = true;
      int num_traces = 0;

      if (print) outs () << "Exploring traces (up to bound): 1";     // GF: trace of length 1 is always empty
      while (unsat && cur_bnd <= bnd)
      {
        if (print) outs () << ", " << cur_bnd;
        vector<vector<int>> traces;
        vector<int> empttrace;

        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, cur_bnd++, vector<int>(), traces);

        for (auto &a : traces)
        {
          num_traces++;
          unsat = !u.isSat(toExpr(a));
          if (!unsat) break;
        }
      }

      if (print)
        outs () << "\nTotal number of traces explored: " << num_traces << "\n\n"
              << (unsat ? "UNSAT for all traces up to " : "SAT for a trace with ")
              << (cur_bnd - 1) << " steps\n";
      return unsat;
    }

    boost::tribool kIndIter(int bnd1, int bnd2)
    {
      assert (bnd1 <= bnd2);
      assert (bnd2 > 1);
      boost::tribool init = exploreTraces(bnd1, bnd2);
      if (!init)
      {
        outs() << "Base check failed at step " << bnd2 << "\n";
        exit(0);
      }

      k_ind = ruleManager.chcs.size(); // == 3

      for (int i = 0; i < k_ind; i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
      }

      ruleManager.chcs.push_back(HornRuleExt());   // trick for now: a new artificial CHC
      HornRuleExt& hr = ruleManager.chcs[k_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      hr.srcVars = tr.srcVars;
      hr.dstVars = tr.dstVars;
      hr.locVars = tr.locVars;

      hr.body = mk<AND>(tr.body, mkNeg(pr.body));

      if (extraLemmas != NULL) hr.body = mk<AND>(extraLemmas, hr.body);

      for (int i = 0; i < srcVars.size(); i++)
      {
        hr.body = replaceAll(hr.body, srcVars[i], srcVars[i]);
      }

      vector<int> gen_trace;
      for (int i = 1; i < bnd2; i++) gen_trace.push_back(k_ind);
      gen_trace.push_back(pr_ind);
      Expr q = toExpr(gen_trace);
      boost::tribool res = !u.isSat(q);

      if (bnd2 == 2) inv = mkNeg(pr.body);

      // prepare for the next iteration
      ruleManager.chcs.erase (ruleManager.chcs.begin() + k_ind);

      return res;
    }

    Expr getInv() { return inv; }

    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      int fc_ind;
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto & r = ruleManager.chcs[i];
        if (r.isInductive) tr_ind = i;
        if (r.isQuery) pr_ind = i;
        if (r.isFact) fc_ind = i;
      }

      HornRuleExt& fc = ruleManager.chcs[fc_ind];
      HornRuleExt& tr = ruleManager.chcs[tr_ind];
      HornRuleExt& pr = ruleManager.chcs[pr_ind];

      Expr prop = pr.body;
      Expr init = fc.body;
      for (int i = 0; i < srcVars.size(); i++)
      {
        init = replaceAll(init, tr.dstVars[i],  srcVars[i]);
      }

      Expr itp;

      if (k == 0)
      {
        itp = getItp(init, prop);
      }
      else
      {
        vector<int> trace;
        for (int i = 0; i < k; i++) trace.push_back(tr_ind);

        Expr unr = toExpr(trace);
        for (int i = 0; i < srcVars.size(); i++)
        {
          prop = replaceAll(prop, srcVars[i], bindVars.back()[i]);
        }
        itp = getItp(unr, prop);
        if (itp != NULL)
        {
          for (int i = 0; i < srcVars.size(); i++)
          {
            itp = replaceAll(itp, bindVars.back()[i], srcVars[i]);
          }
        }
        else
        {
          itp = getItp(init, mk<AND>(unr, prop));
        }
      }
      return itp;
    }

    //used for multiple loops to unroll inductive clauses k times and collect corresponding models
    bool unrollAndExecuteMultiple(ufo::ZSolver<ufo::EZ3> & m_smt_solver,
				  map<Expr, vector<vector<int> > > & models, int k = 10)
    {
      for (int i = 0; i < ruleManager.cycles.size(); i++)
      {
        auto & loop = ruleManager.cycles[i];
        Expr srcRel = invExpr;
        if (models[srcRel].size() > 0) continue;
        bool toContinue = false;
        for (auto & v : srcVars)
        {
          if (!bind::isIntConst(v))
          {
            toContinue = true;
            break;
          }
        }
        if (toContinue) continue;

        auto & prefix = ruleManager.prefixes[i];
        vector<int> trace;
        ExprSet lastModel;
        int p = prefix.size();

        while (p > 0)
        {
          auto & r = ruleManager.chcs[prefix[--p]];
          if (models[invExpr].size() > 0)
          {
            assert(models[invExpr].back().size() == srcVars.size());
            for (int j = 0; j < srcVars.size(); j ++)
            {
              Expr val = mk<EQ>(srcVars[j], mkTerm (mpz_class (models[invExpr].back()[j]), m_efac));
              lastModel.insert(val);
            }
            break;
          }
        }
        while (p < prefix.size()) trace.push_back(prefix[p++]);
        int l = trace.size() - 1;

        for (int j = 0; j < k; j++)
          for (int m = 0; m < loop.size(); m++)
            trace.push_back(loop[m]);

        for (int i = 0; i < ruleManager.chcs.size(); i++)
        {
          auto & r = ruleManager.chcs[i];
          if (i != loop[0] && !r.isQuery)
          {
            trace.push_back(i);
            break;
          }
        }

        ExprVector ssa;
        getSSA(trace, ssa);
        bindVars.pop_back();

        toContinue = false;
        while (true)
        {
          if (ssa.size() < 2)
          {
            outs () << "Unable to find a suitable unrolling for " << *srcRel << "\n";
            toContinue = true;
            break;
          }

          m_smt_solver.reset();
          m_smt_solver.assertExpr(conjoin(lastModel, m_efac));
          m_smt_solver.assertExpr(conjoin(ssa, m_efac));

          if (m_smt_solver.solve())
          {
            break;
          }
          else
          {
            ssa.pop_back();
            bindVars.pop_back();
          }
        }

        if (toContinue) continue;

        ZSolver<EZ3>::Model m = m_smt_solver.getModel();

        for (; l < bindVars.size(); l = l + loop.size())
        {
          auto & vars = bindVars[l];
          vector<int> model;
//          outs () << "model for " << l << ": ";
          for (auto var : vars) {
            int value;
            if (var != m.eval(var)) {
              stringstream tmpstream;
              tmpstream << m.eval(var);
              tmpstream >> value;
            } else {
              value = guessUniformly(1000)-500;
              cout << "random guess for: " << var << endl; //DEBUG
            }
            model.push_back(value);
//             outs () << *var << " = " << value << ", ";
          }
//          outs () << "\b\b]\n";
          models[srcRel].push_back(model);
        }
      }

      return true;
    }

    void fillVars(Expr srcRel, ExprVector vars, int l, int s, vector<int>& mainInds, vector<int>& arrInds, vector<ExprVector>& versVars, ExprSet& allVars)
    {
      for (int l1 = l; l1 < bindVars.size(); l1 = l1 + s)
      {
        ExprVector vers;
        int ai = 0;

        for (int i = 0; i < vars.size(); i++) {
          int var = mainInds[i];
          Expr bvar;
          if (var >= 0)
          {
            if (ruleManager.hasArrays)
              bvar = bindVars[l1-1][var];
            else
              bvar = bindVars[l1][var];
          }
          else
          {
            bvar = mk<SELECT>(bindVars[l1][arrInds[ai]], bindVars[l1 - 1][-1 * var - 1]);
            allVars.insert(bindVars[l1][arrInds[ai]]);
            ai++;
          }
          vers.push_back(bvar);
        }
        versVars.push_back(vers);
        allVars.insert(vers.begin(), vers.end());
      }
    }

    void getOptimConstr(vector<ExprVector>& versVars, int vs, ExprVector& diseqs)
    {
      for (auto v : versVars)
        for (int i = 0; i < v.size(); i++)
          for (int j = i + 1; j < v.size(); j++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(v[i], v[j]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));

      for (int i = 0; i < vs; i++)
        for (int j = 0; j < versVars.size(); j++)
          for (int k = j + 1; k < versVars.size(); k++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(versVars[j][i], versVars[k][i]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));
    }

    void setGhostCond(ExprVector& ssa, Expr gh_cond, Expr preCond)
    {
      Expr gh_zero = ssa.back();
      Expr ssa_last = gh_zero;
      ssa.pop_back();
      ExprSet g;
      getConj(gh_zero, g);
      ExprVector g2;
      for(auto& c: g) g2.push_back(c);
      gh_zero = g2.back();
      gh_zero = mk<EQ>(gh_zero->left(), mkTerm(mpz_class(0), m_efac));
      g2.push_back(gh_zero);
      gh_zero = conjoin(g2, m_efac);

      preCond = replaceAll(preCond, srcVars, bindVars[bindVars.size() - 1]);
      ssa.push_back(mk<AND>(gh_zero, mkNeg(preCond)));
      ssa.push_back(gh_cond);
      //bindVars.pop_back();

      //pprint(ssa,2);
      //outs() << "\n\n";
    }

    boost::tribool unrollAndExecuteTerm(
          Expr srcRel,
          ExprVector& dtVars,
				  vector<vector<double> >& models,
          Expr gh_cond, Expr invs, Expr preCond,
          int k = 9)
    {
      assert (gh_cond != NULL);
      if(debug) {
        outs() << "Exploring execution of " << srcRel << "\n";
        ruleManager.print();
      }

      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      //outs() << "cycles.size(): " << ruleManager.cycles.size() << "\n";
      for (int cyc = 0; cyc < ruleManager.cycles.size(); cyc++)
      {
        //if(debug) outs() << "cycle: " << cyc << "\n";
        vector<int> mainInds;
        vector<int> arrInds;
        auto & loop = ruleManager.cycles[cyc];
        if (srcRel != ruleManager.chcs[loop[0]].srcRelation) continue;
        if (models.size() > 0) continue;

        ExprVector vars;
        for (int i = 0; i < srcVars.size(); i++)
        {
          Expr var = srcVars[i];
          if (bind::isIntConst(var))
          {
            mainInds.push_back(i);
            vars.push_back(var);
          }/*
          else if (isConst<ARRAY_TY> (var) && ruleManager.hasArrays)
          {
            for (auto it : ruleManager.iterators[srcRel])
            {
              vars.push_back(mk<SELECT>(var, srcVars[it]));
              mainInds.push_back(-1 * it - 1); // to be on the negative side
              arrInds.push_back(i);
            }
          }*/
        }

        if (vars.size() < 2 && cyc == ruleManager.cycles.size() - 1)
          continue; // does not make much sense to run with only one var when it is the last cycle
        dtVars = vars;

        auto & prefix = ruleManager.prefixes[cyc];
        vector<int> trace;
        int l = 0;                        // starting index (before the loop)
        //if (ruleManager.hasArrays) l++; // first iter is usually useless

        if(gh_cond == mk<TRUE>(m_efac)) trace.push_back(0);
        for (int j = 0; j < k; j++)
          for (int m = 0; m < loop.size(); m++)
            trace.push_back(loop[m]);

        int backCHC = -1;
        ExprVector ssa;
        for(auto& t: trace) outs() << t << ", ";
        outs() << "\b\b \n";
        getSSA(trace, ssa);
        int traceSz = trace.size();
  //      pprint( conjoin(ssa, m_efac));
        // compute vars for opt constraint
        vector<ExprVector> versVars;
        ExprSet allVars;
        ExprVector diseqs;
        fillVars(srcRel, vars, l, loop.size(), mainInds, arrInds, versVars, allVars);
        getOptimConstr(versVars, vars.size(), diseqs);

        Expr cntvar = bind::intConst(mkTerm<string> ("_ST_cnt", m_efac));
        allVars.insert(cntvar);
        allVars.insert(bindVars.back().begin(), bindVars.back().end());
        ssa.insert(ssa.begin(), mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

        bool toContinue = false;
        bool noopt = false;
        while (true)
        {
          setGhostCond(ssa, gh_cond, preCond);
          if (bindVars.size() <= 1)
          {
            if (debug) outs () << "Unable to solve the BMC formula for " <<  srcRel << " and gh_cond " << gh_cond <<"\n";
            toContinue = true;
            return false;
          }

          if (u.isSat(conjoin(ssa, m_efac)))
          {
            break;
          }
          else
          {
            if (trace.size() == traceSz)
            {
              trace.pop_back();
              ssa.pop_back();
              ssa.pop_back(); // remove the gh conds
              bindVars.pop_back();
            }
            else
            {
              trace.resize(trace.size()-loop.size());
              ssa.pop_back();
              ssa.resize(ssa.size()-loop.size());
              bindVars.resize(bindVars.size()-loop.size());
            }

          }
        }

        ExprMap allModels;
        u.getOptModel<GT>(allVars, allModels, cntvar);

        ExprSet gh_condVars;
        set<int> gh_condVarsIndex; // Get gh_cond vars here
        filter(gh_cond, bind::IsConst(), inserter(gh_condVars, gh_condVars.begin()));
        for (auto & a : gh_condVars)
          gh_condVarsIndex.insert(getVarIndex(a, srcVars));

        if (debug) outs () << "\nUnroll and execute the cycle for " <<  srcRel << " and cond " << gh_cond <<"\n";
        for (int j = 0; j < versVars.size(); j++)
        {
          if(j >= trace.size()) break;
          vector<double> model;
          if (debug) outs () << "  model for " << j+1 << ":\t[";
          bool toSkip = false;
          SMTUtils u2(m_efac);
          ExprSet equalities;

          for (auto i: gh_condVarsIndex)
          {
            Expr srcVar = srcVars[i];
            Expr bvar = versVars[j][i];
            if (isOpX<SELECT>(bvar)) bvar = bvar->left();
            Expr m = allModels[bvar];
            if (m == NULL) { toSkip = true; break; }
            equalities.insert(mk<EQ>(srcVar, m));
          }
          if (toSkip) continue;
          equalities.insert(gh_cond);

          if (u2.isSat(equalities)) //exclude models that don't satisfy gh_cond
          {
            vector<double> model;

            for (int i = 0; i < vars.size(); i++) {
              Expr bvar = versVars[j][i];
              Expr m = allModels[bvar];
              double value;
              if (m != NULL && isOpX<MPZ>(m))
              {
                if (lexical_cast<cpp_int>(m) > max_double ||
                    lexical_cast<cpp_int>(m) < -max_double)
                {
                  toSkip = true;
                  break;
                }
                value = lexical_cast<double>(m);
              }
              else
              {
                toSkip = true;
                break;
              }
              model.push_back(value);
              if (debug) outs () << *bvar << " = " << *m << ", ";
              if (j == 0)
              {
                if (isOpX<SELECT>(bvar))
                  concrInvs[srcRel].insert(mk<EQ>(vars[i]->left(), allModels[bvar->left()]));
                else
                  concrInvs[srcRel].insert(mk<EQ>(vars[i], m));
              }
            }
            if (!toSkip) models.push_back(model);
          }
          else
          {
            if (debug) outs () << "   <  skipping  >      ";
          }
          if (debug) outs () << "\b\b]\n";
        }
      }

      return true;
    }

    bool unrollAndExecute(const Expr & invRel, ufo::ZSolver<ufo::EZ3> & m_smt_solver, vector<vector<int> > & models, int k = 10, Expr initCondn = nullptr)
    {

      int initIndex;
      int trIndex;
      bool initFound = false;

      for (int i = 0; i < ruleManager.chcs.size(); i++) {
        auto & r = ruleManager.chcs[i];
        if (r.isFact) {
          initIndex = i;
          initFound = true;
        }
        if (r.isInductive && invExpr == invRel && r.dstRelation == invRel) {
          trIndex = i;
        }
      }

      if (!initFound && initCondn == nullptr) {
        cout << "ERR: init not found for given transition (index: " << trIndex << ")" << endl;
        return false;
      }

      Expr init = initCondn == nullptr ? ruleManager.chcs[initIndex].body : initCondn;

      HornRuleExt& tr = ruleManager.chcs[trIndex];

      for (int i = 0; i < srcVars.size(); i++) {
        init = replaceAll(init, tr.dstVars[i], srcVars[i]);
      }


      vector<int> trace;
      for (int i = 0; i < k; i++) {
        trace.push_back(trIndex);
      }

      Expr unrolledTr = toExpr(trace);

      //      cout << init << " && " << unrolledTr << endl;

      m_smt_solver.reset();
      m_smt_solver.assertExpr(init);
      m_smt_solver.assertExpr(unrolledTr);

      if (!m_smt_solver.solve()) {
        cout << init << " && " << unrolledTr << "\nfound to be unsat\n";
        return false;
      }

      ZSolver<EZ3>::Model m = m_smt_solver.getModel();

      for (auto vars : bindVars) {
        vector<int> model;
        for (auto var : vars) {
          int value;
          if (var != m.eval(var)) {
            stringstream tmpstream;
            tmpstream << m.eval(var);
            tmpstream >> value;
          } else {
            value = guessUniformly(1000)-500;
            cout << "random guess for: " << var << endl; //DEBUG
          }
          cout << value << "\t";//DEBUG
          model.push_back(value);
        }
        cout << endl;//DEBUG
        models.push_back(model);
      }

      return true;
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    BndExpl ds(ruleManager);
    ds.exploreTraces(bnd1, bnd2, true);
  };

  inline bool kInduction(CHCs& ruleManager, int bnd)
  {
    if (ruleManager.chcs.size() != 3)
    {
      outs () << "currently not supported\n";
      return false;
    }

    BndExpl ds(ruleManager);

    bool success = false;
    int i;
    for (i = 2; i < bnd; i++)
    {
      if (ds.kIndIter(i, i))
      {
        success = true;
        break;
      }
    }

    outs () << "\n" <<
      (success ? "K-induction succeeded " : "Unknown result ") <<
      "after " << (i-1) << " iterations\n";

    return success;
  };

  inline void kInduction(string smt, int bnd)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    kInduction(ruleManager, bnd);
  };
}

#endif
