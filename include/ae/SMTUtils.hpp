#ifndef SMTUTILS__HPP__
#define SMTUTILS__HPP__
#include <assert.h>

#include "ae/ExprSimpl.hpp"
#include "ufo/Smt/EZ3.hh"

using namespace std;
using namespace boost;
namespace ufo
{

  class SMTUtils {
  private:

    ExprFactory &efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    bool can_get_model;
    ZSolver<EZ3>::Model* m;
    
    public:
    int debug = 0;  // Add debug member

    SMTUtils (ExprFactory& _efac, int _debug = 0) :
      efac(_efac), z3(efac), smt (z3), can_get_model(0), m(NULL), debug(_debug) {}

    SMTUtils (ExprFactory& _efac, unsigned _to, int _debug = 0) :
      efac(_efac), z3(efac), smt (z3, _to), can_get_model(0), m(NULL), debug(_debug) {}
    boost::tribool eval(Expr v, ZSolver<EZ3>::Model* m1)
    {
      Expr ev = m1->eval(v);
      if (m == NULL) return indeterminate;
      if (isOpX<TRUE>(ev)) return true;
      if (isOpX<FALSE>(ev)) return false;
      return indeterminate;
    }

    boost::tribool eval(Expr v)
    {
      getModelPtr();
      if (m == NULL) return indeterminate;
      return eval(v, m);
    }

    ZSolver<EZ3>::Model* getModelPtr()
    {
      if (!can_get_model) return NULL;
      if (m == NULL) m = smt.getModelPtr();
      return m;
    }

    Expr getModel(Expr v)
    {
      getModelPtr();
      if (m == NULL) return NULL;
      return m->eval(v);
    }

    template <typename T> Expr getModel(T& vars)
    {
      getModelPtr();
      if (m == NULL) return NULL;
      ExprVector eqs;
      for (auto & v : vars)
      {
        Expr e = m->eval(v);
        if (e == NULL || containsOp<EXISTS>(e) || containsOp<FORALL>(e))
        {
          continue;
        }
        else if (e != v)
        {
          eqs.push_back(mk<EQ>(v, e));
        }
      }
      return conjoin (eqs, efac);
    }

    Expr lastCand;
    Expr getModel()
    {
      if (!can_get_model)
        return NULL;
      ExprSet allVars;
      filter (lastCand, bind::IsConst (), inserter (allVars, allVars.begin()));
      return getModel(allVars);
    }

    void getModel (ExprSet& vars, ExprMap& e)
    {
      ExprSet mdl;
      getConj(getModel(vars), mdl);
      for (auto & m : mdl) e[m->left()] = m->right();
    }

    template <typename T> void getOptModel (ExprSet& vars, ExprMap& e, Expr v)
    {
      if (!can_get_model) return;
      while (true)
      {
        getModel(vars, e);
        smt.assertExpr(mk<T>(v, e[v]));
        if (m != NULL) { free(m); m = NULL; }
        auto res = smt.solve();
        if (!res || indeterminate(res)) return;
      }
    }

    template <typename T> boost::tribool isSat(T& cnjs, bool reset=true)
    {
      if (m != NULL) { free(m); m = NULL; }
      if (reset) smt.reset();
      if (cnjs.empty())
      {
        lastCand = NULL;
        can_get_model = false;
        return true;
      }
      else
      {
        lastCand = conjoin(cnjs, efac);
        smt.assertExpr(lastCand);
      }
      boost::tribool res = smt.solve ();
      can_get_model = res ? true : false;
      return res;
    }
    
    /**
     * Push the solver state (for incremental solving)
     */
    void push() { smt.push(); }
    
    /**
     * Pop the solver state (for incremental solving)
     */
    void pop(unsigned n = 1) { smt.pop(n); }
    
    /**
     * Assert an expression without resetting
     */
    void assertExpr(Expr e) { smt.assertExpr(e); }
    
    /**
     * Reset the solver
     */
    void reset() { smt.reset(); if (m != NULL) { free(m); m = NULL; } }
    
    /**
     * Solve without adding any new constraints
     */
    boost::tribool solve()
    {
      if (m != NULL) { free(m); m = NULL; }
      boost::tribool res = smt.solve();
      can_get_model = res ? true : false;
      return res;
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, Expr c, Expr d, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      getConj(c, cnjs);
      getConj(d, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, Expr c, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      getConj(c, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, Expr b, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      getConj(b, cnjs);
      return isSat(cnjs, reset);
    }

    /**
     * SMT-check
     */
    boost::tribool isSat(Expr a, bool reset=true)
    {
      ExprSet cnjs;
      getConj(a, cnjs);
      return isSat(cnjs, reset);
    }

    // isSatBMC

    /**
     * Incremental SMT-check
     */
    boost::tribool isSatIncrem(ExprVector& v, int& sz)
    {
      sz = 0;
      while (sz < v.size())
      {
        auto res = isSat(v[sz], sz == 0);
        sz++;
        if (res == false || indeterminate(res)) return res;
      }
      return true;    // sat
    }

    /**
     * SMT-based formula equivalence check
     */
    boost::tribool isEquiv(Expr a, Expr b)
    {
      auto r1 = implies (a, b);
      auto r2 = implies (b, a);
      return r1 && r2;
    }

    /**
     * SMT-based implication check
     */
    boost::tribool implies (Expr a, Expr b)
    {
      if (a == b) return true;
      if (isOpX<TRUE>(b)) return true;
      if (isOpX<FALSE>(a)) return true;
      return ! isSat(a, mkNeg(b));
    }

    /**
     * SMT-based check for a tautology
     */
    boost::tribool isTrue(Expr a){
      if (isOpX<TRUE>(a)) return true;
      return !isSat(mkNeg(a));
    }

    /**
     * SMT-based check for false
     */
    boost::tribool isFalse(Expr a){
      if (isOpX<FALSE>(a)) return true;
      if (isOpX<NEQ>(a) && a->left() == a->right()) return true;
      return !isSat(a);
    }

    /**
     * Check if v has only one sat assignment in phi
     */
    boost::tribool hasOneModel(Expr v, Expr phi) {
      if (isFalse(phi)) return false;

      getModelPtr();
      if (m == NULL) return indeterminate;

      Expr val = m->eval(v);
      if (v == val) return false;

      ExprSet assumptions;
      assumptions.insert(mk<NEQ>(v, val));

      return !isSat(assumptions, false);
    }

    /**
     * Check if phi has one model
     */
    boost::tribool hasOneModel(Expr phi) {
      if (isFalse(phi)) return false;

      getModelPtr();
      if (m == NULL) return indeterminate;

      ExprSet assumptions;
      assumptions.insert(mk<NEG>(getModel()));

      return !isSat(assumptions, false);
    }

    /**
     * ITE-simplifier (prt 2)
     */
    Expr simplifyITE(Expr ex, Expr upLevelCond)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = ex->arg(0);
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (!isSat(cond, upLevelCond)) return br2;

        if (!isSat(mk<NEG>(cond), upLevelCond)) return br1;

        return mk<ITE>(cond,
                       simplifyITE(br1, mk<AND>(upLevelCond, cond)),
                       simplifyITE(br2, mk<AND>(upLevelCond, mk<NEG>(cond))));
      } else {
        return ex;
      }
    }

    /**
     * ITE-simplifier (prt 1)
     */
    Expr simplifyITE(Expr ex)
    {
      if (isOpX<ITE>(ex)){

        Expr cond = simplifyITE(ex->arg(0));
        Expr br1 = ex->arg(1);
        Expr br2 = ex->arg(2);

        if (isOpX<TRUE>(cond)) return br1;
        if (isOpX<FALSE>(cond)) return br2;

        if (br1 == br2) return br1;

        if (isOpX<TRUE>(br1) && isOpX<FALSE>(br2)) return cond;

        if (isOpX<FALSE>(br1) && isOpX<TRUE>(br2)) return mk<NEG>(cond);

        return mk<ITE>(cond,
                       simplifyITE(br1, cond),
                       simplifyITE(br2, mk<NEG>(cond)));

      } else if (isOpX<IMPL>(ex)) {

        return mk<IMPL>(simplifyITE(ex->left()), simplifyITE(ex->right()));
      } else if (isOpX<AND>(ex) || isOpX<OR>(ex)){

        ExprSet args;
        for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it){
          args.insert(simplifyITE(*it));
        }
        return isOpX<AND>(ex) ? conjoin(args, efac) : disjoin (args, efac);
      }
      return ex;
    }

    Expr removeITE(Expr ex)
    {
      ExprVector ites;
      getITEs(ex, ites);
      int sz = ites.size();
      for (auto it = ites.begin(); it != ites.end();)
      {
        Expr tmp;
        if (implies(ex, (*it)->left()))
          tmp = (*it)->right();
        else if (implies(ex, mk<NEG>((*it)->left())))
          tmp = (*it)->last();
        else {++it; continue; }

        ex = replaceAll(ex, *it, tmp);
        it = ites.erase(it);
      }
      if (sz == ites.size()) return ex;
      else return simplifyBool(simplifyArithm(removeITE(ex)));
    }

    Expr simplify(Expr ex)
    {
      return z3_simplify(z3, ex);
    }

    /**
     * Unroll a compact trace representation by evaluating array selections
     * at each index from start to end.
     *
     * @param traceArray - The array expression (e.g., trace variable)
     * @param start - Starting index
     * @param end - Ending index (inclusive)
     * @param out - Output stream (default: outs())
     * @return ExprVector containing the concrete values at each index
     */
    ExprVector unrollTrace(Expr traceArray, int start, int end)
    {
      ExprVector values;

      if (!can_get_model)
      {
        outs() << "Error: No model available. Call isSat() first.\n";
        return values;
      }

      
      for (int i = start; i <= end; i++)
      {
        getModelPtr();
        if (m == NULL)
        {
          outs() << "Error: Could not get model.\n";
          return values;
        }
        // Build (select traceArray i)
        Expr idx = mkTerm<mpz_class>(i, efac);
        Expr selectExpr = mk<SELECT>(traceArray, idx);

        // Evaluate in the model
        Expr value = m->eval(selectExpr, true); // true = completion
        values.push_back(value);

        if (debug > 0)
        {
          outs() << "trace[" << i << "] = " << *value << "\n";
        }
      }

      return values;
    }

    /**
     * Unroll trace and return as a map from index to value
     */
    void unrollTraceToMap(Expr traceArray, int start, int end,
                          std::map<int, Expr> &traceMap)
    {
      if (!can_get_model)
        return;

      getModelPtr();
      if (m == NULL)
        return;

      for (int i = start; i <= end; i++)
      {
        Expr idx = mkTerm<mpz_class>(i, efac);
        Expr selectExpr = mk<SELECT>(traceArray, idx);
        Expr value = m->eval(selectExpr, true);
        traceMap[i] = value;
      }
    }

    /**
     * Unroll multiple variables across a trace
     * Given a map of variable name -> array expression, evaluates each at every step
     */
    void unrollMultipleTraces(std::map<std::string, Expr> &traceArrays,
                              int start, int end,
                              std::map<int, ExprMap> &result)
    {
      if (!can_get_model)
        return;

      getModelPtr();
      if (m == NULL)
        return;

      for (int i = start; i <= end; i++)
      {
        Expr idx = mkTerm<mpz_class>(i, efac);
        ExprMap stepValues;

        if (debug > 0)
          outs() << "Step " << i << ":\n";

        for (auto &[name, traceArray] : traceArrays)
        {
          Expr selectExpr = mk<SELECT>(traceArray, idx);
          Expr value = m->eval(selectExpr, true);

          // Store using the array expr as key
          stepValues[traceArray] = value;

          if (debug > 0)
            outs() << "  " << name << " = " << *value << "\n";
        }

        result[i] = stepValues;
      }
    }

    /**
     * Remove some redundant conjuncts from the set of formulas
     */
    void removeRedundantConjuncts(ExprSet& conjs)
    {
      if (conjs.size() < 2) return;
      ExprSet newCnjs = conjs;

      for (auto & cnj : conjs)
      {
        if (isTrue (cnj))
        {
          newCnjs.erase(cnj);
          continue;
        }

        ExprSet newCnjsTry = newCnjs;
        newCnjsTry.erase(cnj);

        Expr newConj = conjoin(newCnjsTry, efac);
        if (implies (newConj, cnj))
          newCnjs.erase(cnj);

        else {
          // workaround for arrays or complicated expressions
          Expr new_name = mkTerm<string> ("subst", cnj->getFactory());
          Expr new_conj = bind::boolConst(new_name);
          Expr tmp = replaceAll(newConj, cnj, new_conj);
          if (implies (tmp, new_conj)) {
            errs() << "erased\n";
            newCnjs.erase(cnj);
          }
        }
      }
      conjs.clear();
      for (auto & cnj : newCnjs)
        conjs.insert(removeRedundantDisjuncts(cnj));
    }

    /**
     * Remove some redundant conjuncts from the formula
     */
    Expr removeRedundantConjuncts(Expr exp)
    {
      ExprSet conjs;
      getConj(exp, conjs);
      if (conjs.size() < 2) return exp;
      else
      {
        removeRedundantConjuncts(conjs);
        return conjoin(conjs, efac);
      }
    }

    void removeRedundantConjunctsVec(ExprVector& exps)
    {
      ExprVector expsn;
      for (auto e : exps)
      {
        e = removeRedundantConjuncts(e);
        if (!isOpX<TRUE>(e)) expsn.push_back(e);
      }
      exps = expsn;
    }

    /**
     * Remove some redundant disjuncts from the formula
     */
    template <typename Range> void removeRedundantDisjuncts(Range& disjs)
    {
      if (disjs.size() < 2) return;

      for (auto it = disjs.begin(); it != disjs.end(); )
      {
        if (isFalse (*it))
        {
          it = disjs.erase(it);
          continue;
        }

        auto newDisjsTry = disjs;
        for (auto it2 = newDisjsTry.begin(); it2 != newDisjsTry.end(); )
          if (*it == *it2)
            it2 = newDisjsTry.erase(it2);
          else
            ++it2;

        if (implies (*it, disjoin(newDisjsTry, efac)))
        {
           it = disjs.erase(it);
           continue;
        }
        ++it;
      }
    }

    Expr removeRedundantDisjuncts(Expr exp)
    {
      ExprSet disjs;
      getDisj(exp, disjs);
      if (disjs.size() < 2) return exp;
      else
      {
        removeRedundantDisjuncts(disjs);
        return disjoin(disjs, efac);
      }
    }

    // to extend
    Expr simplifiedAnd(Expr a, Expr b)
    {
      ExprVector disjs, vars;
      flatten(a, disjs, false, vars, [](Expr a, ExprVector& b){return a;});
      for (auto it = disjs.begin(); it != disjs.end(); )
      {
        if (!isSat(*it, b)) it = disjs.erase(it);
        else ++it;
      }
      return mk<AND>(distribDisjoin(disjs, efac), b);
    }

    /**
     * Model-based simplification of a formula with 1 (one only) variable
     */
    Expr numericUnderapprox(Expr exp)
    {
      ExprVector cnstr_vars;
      filter (exp, bind::IsConst (), back_inserter (cnstr_vars));
      if (cnstr_vars.size() == 1)
      {
        smt.reset();
        smt.assertExpr (exp);
        if (smt.solve ()) {
          getModelPtr();
          if (m == NULL) return exp;
          return mk<EQ>(cnstr_vars[0], m->eval(cnstr_vars[0]));
        }
      }
      return exp;
    }

    template <typename Range1, typename Range2, typename Range3> bool
      splitUnsatSets(Range1 & src, Range2 & dst1, Range3 & dst2)
    {
      if (isSat(src)) return false;

      for (auto & a : src) dst1.push_back(a);

      for (auto it = dst1.begin(); it != dst1.end(); )
      {
        dst2.push_back(*it);
        it = dst1.erase(it);
        if (isSat(dst1)) break;
      }

      // now dst1 is SAT, try to get more things from dst2 back to dst1

      for (auto it = dst2.begin(); it != dst2.end(); )
      {
        if (!isSat(conjoin(dst1, efac), *it)) { ++it; continue; }
        dst1.push_back(*it);
        it = dst2.erase(it);
      }

      return true;
    }

    void insertUnique(Expr e, ExprSet& v)
    {
      for (auto & a : v)
        if (isEquiv(a, e)) return;
      v.insert(e);
    }

    void getTrueLiterals(Expr ex, ZSolver<EZ3>::Model &m, ExprSet& lits, bool splitEqs = true)
    {
      ExprVector ites;
      getITEs(ex, ites);
      if (ites.empty())
      {
        getLiterals(ex, lits, splitEqs);
        for (auto it = lits.begin(); it != lits.end(); ){
          if (isOpX<TRUE>(m.eval(*it))) ++it;
          else it = lits.erase(it);
        }
      }
      else
      {
        // eliminate ITEs first
        for (auto it = ites.begin(); it != ites.end();)
        {
          if (isOpX<TRUE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->right());
            ex = mk<AND>(ex, (*it)->left());
          }
          else if (isOpX<FALSE>(m((*it)->left())))
          {
            ex = replaceAll(ex, *it, (*it)->last());
            ex = mk<AND>(ex, mkNeg((*it)->left()));
          }
          else
          {
            ex = replaceAll(ex, *it, (*it)->right()); // TODO
            ex = mk<AND>(ex, mk<EQ>((*it)->right(), (*it)->last()));
          }
          it = ites.erase(it);
        }
        return getTrueLiterals(ex, m, lits, splitEqs);
      }
    }

    Expr getTrueLiterals(Expr ex, bool splitEqs = true)
    {
      ExprSet lits;
      getModelPtr();
      if (m == NULL) return NULL;
      getTrueLiterals(ex, *m, lits, splitEqs);
      return conjoin(lits, efac);
    }

    bool flatten(Expr fla, ExprVector& prjcts, bool splitEqs, ExprVector& vars,
                 function<Expr(Expr, ExprVector& vars)> qe) // lazy DNF-ization
    {
      smt.reset();
      Expr tmp = fla;
      while (isSat(tmp, false))
      {
        prjcts.push_back(qe(getTrueLiterals(fla, splitEqs), vars)); // if qe is identity, then it's pure DNF
        if (prjcts.back() == NULL) return false;
        tmp = mk<NEG>(prjcts.back());
      }
      return true;
    }

    Expr getWeakerMBP(Expr mbp, Expr fla, ExprVector& srcVars)
    {
      if (containsOp<ARRAY_TY>(fla)) return mbp;

      ExprSet cnjs;
      getConj(mbp, cnjs);
      if (cnjs.size() == 1) return mbp;

      ExprSet varsSet;
      filter (fla, bind::IsConst (), inserter(varsSet, varsSet.begin()));
      minusSets(varsSet, srcVars);

      ExprVector args;
      Expr efla;
      for (auto & v : varsSet) args.push_back(v->left());
      if (args.empty()) efla = fla;
      else {
        args.push_back(fla);
        efla = mknary<EXISTS>(args);
      }

      bool prog = true;
      while (prog)
      {
        prog = false;
        for (auto it = cnjs.begin(); it != cnjs.end();)
        {
          ExprVector cnjsTmp;
          for (auto & a : cnjs) if (a != *it) cnjsTmp.push_back(a);
          if (implies(conjoin(cnjsTmp, efac), efla))
          {
            prog = true;
            it = cnjs.erase(it);
          }
          else ++it;
        }
      }
      return conjoin(cnjs, efac);
    }

    Expr getImplDecomp(Expr a, Expr b)
    {
      // if a == a1 /\ a2 s.t. b => a1 then return a2
      ExprSet cnjs;
      getConj(a, cnjs);
      for (auto it = cnjs.begin(); it != cnjs.end();)
        if (implies(b, *it)) it = cnjs.erase(it);
        else ++it;
      return conjoin(cnjs, efac);
    }

    Expr quantifierEliminationBV(Expr fla, ExprSet &qVars, bool existential = false)
    {
      if (qVars.empty())
        return fla;

      // Construct the quantified formula for reference
      Expr quantified;
      if (existential)
      {
        quantified = mknary<EXISTS>(qVars.begin(), qVars.end());
        quantified = mk<EXISTS>(quantified, fla);
      }
      else
      {
        quantified = mknary<FORALL>(qVars.begin(), qVars.end());
        quantified = mk<FORALL>(quantified, fla);
      }

      // Handle universal quantifiers via duality: ∀x. fla ≡ ¬∃x. ¬fla
      if (!existential)
      {
        Expr neg_fla = mk<NEG>(fla);
        ExprSet neg_qVars = qVars; // Copy qVars since it’s a reference
        Expr result = quantifierEliminationBV(neg_fla, neg_qVars, true);
        return mk<NEG>(result);
      }

      // For existential quantifiers (∃x. fla):
      // 1. Gather all variables in fla
      ExprSet allVars;
      filter(fla, bind::IsConst(), inserter(allVars, allVars.begin()));

      // 2. Identify free variables (variables not in qVars)
      ExprSet freeVars;
      for (auto &v : allVars)
      {
        if (qVars.find(v) == qVars.end())
        {
          freeVars.insert(v);
        }
      }

      // 3. Check if the formula is satisfiable
      smt.reset();
      smt.assertExpr(fla);
      boost::tribool res = smt.solve();
      if (!res || indeterminate(res))
      {
        // If unsat, return false (or an unsat core if needed)
        return mk<FALSE>(efac);
      }

      // 4. Project out quantified variables using the model
      ExprVector constraints;
      ZSolver<EZ3>::Model *model = getModelPtr();
      if (model == nullptr)
      {
        // If no model is available, return the original formula as a fallback
        return fla;
      }

      for (auto &v : freeVars)
      {
        Expr val = model->eval(v);
        if (val && val != v)
        {
          constraints.push_back(mk<EQ>(v, val));
        }
      }

      // 5. Return the conjunction of constraints over free variables
      if (constraints.empty())
      {
        return mk<TRUE>(efac);
      }
      return conjoin(constraints, efac);
    }

    /**
     * Normalize expressions containing negative bitvector constants
     * to use subtraction operations instead of two's complement representation
     */
    Expr normalizeNegativeBVConstants(Expr e) {
        if (isOpX<BIND>(e) && e->arity() == 2 && 
            isOpX<MPZ>(e->arg(0)) && isOpX<BVSORT>(e->arg(1))) {
            // This is a bitvector numeral
            mpz_class val = getTerm<mpz_class>(e->arg(0));
            if (val < 0) {
                // Convert negative constant to subtraction of positive value
                Expr sort = e->arg(1);
                Expr posVal = mkTerm<mpz_class>(abs(val), e->getFactory());
                Expr posConst = bv::bvnum(posVal, sort);
                Expr zeroConst = bv::bvnum(mkTerm<mpz_class>(0, e->getFactory()), sort);
                return mk<BSUB>(zeroConst, posConst);
            }
            return e;
        } else if (e->arity() == 0) {
            return e;
        } else {
            // Process children recursively
            ExprVector args;
            bool changed = false;
            for (unsigned i = 0; i < e->arity(); i++) {
                Expr newArg = normalizeNegativeBVConstants(e->arg(i));
                args.push_back(newArg);
                if (newArg != e->arg(i)) changed = true;
            }
            
            // If no arguments changed, return the original expression
            if (!changed) return e;
            
            // Create a new expression with the same operator but new arguments
            // Handle binary operations
            if (isOpX<BSUB>(e)) return mk<BSUB>(args[0], args[1]);
            if (isOpX<BSDIV>(e)) return mk<BSDIV>(args[0], args[1]);
            if (isOpX<BUDIV>(e)) return mk<BUDIV>(args[0], args[1]);
            if (isOpX<BSREM>(e)) return mk<BSREM>(args[0], args[1]);
            if (isOpX<BUREM>(e)) return mk<BUREM>(args[0], args[1]);
            if (isOpX<BNEG>(e)) return mk<BNEG>(args[0]);
            if (isOpX<BNOT>(e)) return mk<BNOT>(args[0]);
            if (isOpX<BCONCAT>(e)) return mk<BCONCAT>(args[0], args[1]);
            if (isOpX<BEXTRACT>(e)) return bv::extract(bv::high(e), bv::low(e), args[0]);
            if (isOpX<BSEXT>(e)) return mk<BSEXT>(args[0], e->arg(1));
            if (isOpX<BZEXT>(e)) return mk<BZEXT>(args[0], e->arg(1));
            if (isOpX<BULE>(e)) return mk<BULE>(args[0], args[1]);
            if (isOpX<BUGE>(e)) return mk<BUGE>(args[0], args[1]);
            if (isOpX<BULT>(e)) return mk<BULT>(args[0], args[1]);
            if (isOpX<BUGT>(e)) return mk<BUGT>(args[0], args[1]);
            if (isOpX<BSLE>(e)) return mk<BSLE>(args[0], args[1]);
            if (isOpX<BSGE>(e)) return mk<BSGE>(args[0], args[1]);
            if (isOpX<BSLT>(e)) return mk<BSLT>(args[0], args[1]);
            if (isOpX<BSGT>(e)) return mk<BSGT>(args[0], args[1]);
            
            // Handle nary operations by constructing them pairwise
            if (isOpX<BADD>(e)) {
                if (args.size() == 1) return args[0];
                Expr result = args[0];
                for (unsigned i = 1; i < args.size(); i++) {
                    result = mk<BADD>(result, args[i]);
                }
                return result;
            }
            if (isOpX<BMUL>(e)) {
                if (args.size() == 1) return args[0];
                Expr result = args[0];
                for (unsigned i = 1; i < args.size(); i++) {
                    result = mk<BMUL>(result, args[i]);
                }
                return result;
            }
            if (isOpX<BAND>(e)) {
                if (args.size() == 1) return args[0];
                Expr result = args[0];
                for (unsigned i = 1; i < args.size(); i++) {
                    result = mk<BAND>(result, args[i]);
                }
                return result;
            }
            if (isOpX<BOR>(e)) {
                if (args.size() == 1) return args[0];
                Expr result = args[0];
                for (unsigned i = 1; i < args.size(); i++) {
                    result = mk<BOR>(result, args[i]);
                }
                return result;
            }
            if (isOpX<BXOR>(e)) {
                if (args.size() == 1) return args[0];
                Expr result = args[0];
                for (unsigned i = 1; i < args.size(); i++) {
                    result = mk<BXOR>(result, args[i]);
                }
                return result;
            }
            
            // For non-BV operators
            if (isOpX<AND>(e)) return mknary<AND>(args);
            if (isOpX<OR>(e)) return mknary<OR>(args);
            if (isOpX<NEG>(e)) return mk<NEG>(args[0]);
            if (isOpX<EQ>(e)) return mk<EQ>(args[0], args[1]);
            if (isOpX<NEQ>(e)) return mk<NEQ>(args[0], args[1]);
            if (isOpX<ITE>(e)) return mk<ITE>(args[0], args[1], args[2]);
            
            // If we couldn't handle the operator, return the original expression
            return e;
        }
    }

    void print (Expr e, std::ostream& out = outs())
    {
      if (isOpX<FORALL>(e) || isOpX<EXISTS>(e))
      {
        if (isOpX<FORALL>(e)) out << "(forall (";
        else out << "(exists (";

        for (int i = 0; i < e->arity() - 1; i++)
        {
          Expr var = bind::fapp(e->arg(i));
          out << "(" << z3.toSmtLib(var) << " " << z3.toSmtLib(typeOf(var)) << ")";
          if (i != e->arity() - 2) out << " ";
        }
        out << ") ";
        print (e->last(), out);
        out << ")";
      }
      else if (isOpX<NEG>(e))
      {
        out << "(not ";
        print(e->left(), out);
        out << ")";
      }
      else if (isOpX<AND>(e))
      {
        out << "(and\n ";
        ExprSet cnjs;
        getConj(e, cnjs);
        int i = 0;
        for (auto & c : cnjs)
        {
          i++;
          print(c, out);
          if (i != cnjs.size()) out << "\n ";
        }
        out << ")";
      }
      else if (isOpX<OR>(e))
      {
        out << "(or\n ";
        ExprSet dsjs;
        getDisj(e, dsjs);
        int i = 0;
        for (auto & d : dsjs)
        {
          i++;
          print(d, out);
          if (i != dsjs.size()) out << "\n ";
        }
        out << ")";
      }
      else if (isOpX<IMPL>(e) || isOp<ComparissonOp>(e))
      {
        if (isOpX<IMPL>(e)) out << "(=> ";
        if (isOpX<EQ>(e)) out << "(= ";
        if (isOpX<GEQ>(e)) out << "(>= ";
        if (isOpX<LEQ>(e)) out << "(<= ";
        if (isOpX<LT>(e)) out << "(< ";
        if (isOpX<GT>(e)) out << "(> ";
        if (isOpX<NEQ>(e)) out << "(distinct ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOpX<ITE>(e))
      {
        out << "(ite ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << " ";
        print(e->last(), out);
        out << ")";
      }
      else out << z3.toSmtLib (e);
      // Add more cases to catch BV operations and operands.
    }

    void serialize_formula(Expr form)
    {
      outs() << "(assert ";
      print (form);
      outs() << ")\n";
    }
  };

  /**
   * Horn-based interpolation over particular vars
   */
  inline Expr getItp(Expr A, Expr B, ExprVector& sharedVars)
  {
    ExprFactory &efac = A->getFactory();
    EZ3 z3(efac);

    ExprVector allVars;
    filter (mk<AND>(A,B), bind::IsConst (), back_inserter (allVars));

    ExprVector sharedTypes;

    for (auto &var: sharedVars) {
      sharedTypes.push_back (bind::typeOf (var));
    }
    sharedTypes.push_back (mk<BOOL_TY> (efac));

    // fixed-point object
    ZFixedPoint<EZ3> fp (z3);
    ZParams<EZ3> params (z3);
    params.set (":engine", "pdr");
    params.set (":xform.slice", false);
    params.set (":xform.inline-linear", false);
    params.set (":xform.inline-eager", false);
    fp.set (params);

    Expr errRel = bind::boolConstDecl(mkTerm<string> ("err", efac));
    fp.registerRelation(errRel);
    Expr errApp = bind::fapp (errRel);

    Expr itpRel = bind::fdecl (mkTerm<string> ("itp", efac), sharedTypes);
    fp.registerRelation (itpRel);
    Expr itpApp = bind::fapp (itpRel, sharedVars);

    fp.addRule(allVars, boolop::limp (A, itpApp));
    fp.addRule(allVars, boolop::limp (mk<AND> (B, itpApp), errApp));

    tribool res;
    try {
      res = fp.query(errApp);
    } catch (z3::exception &e){
      char str[3000];
      strncpy(str, e.msg(), 300);
      errs() << "Z3 ex: " << str << "...\n";
      exit(55);
    }

    if (res) return NULL;

    return fp.getCoverDelta(itpApp);
  }

  /**
   * Horn-based interpolation
   */
  inline Expr getItp(Expr A, Expr B)
  {
    ExprVector sharedVars;

    ExprVector aVars;
    filter (A, bind::IsConst (), back_inserter (aVars));

    ExprVector bVars;
    filter (B, bind::IsConst (), back_inserter (bVars));

    // computing shared vars:
    for (auto &var: aVars) {
      if (find(bVars.begin(), bVars.end(), var) != bVars.end())
      {
        sharedVars.push_back(var);
      }
    }

    return getItp(A, B, sharedVars);
  };

}

#endif
