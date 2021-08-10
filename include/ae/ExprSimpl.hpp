#ifndef EXPRSIMPL__HPP__
#define EXPRSIMPL__HPP__
#include <assert.h>

#include "ufo/Smt/EZ3.hh"
#include <fstream>

using namespace std;
using namespace expr::op::bind;
using namespace boost;
using namespace boost::multiprecision;
namespace ufo
{

  template<typename Range> static Expr conjoin(Range& conjs, ExprFactory &efac){
    return
      (conjs.size() == 0) ? mk<TRUE>(efac) :
      (conjs.size() == 1) ? *conjs.begin() :
      mknary<AND>(conjs);
  }

  template<typename Range> static Expr disjoin(Range& disjs, ExprFactory &efac){
    return
      (disjs.size() == 0) ? mk<FALSE>(efac) :
      (disjs.size() == 1) ? *disjs.begin() :
      mknary<OR>(disjs);
  }

  template<typename Range> static Expr mkplus(Range& terms, ExprFactory &efac){
    return
      (terms.size() == 0) ? mkTerm (mpz_class (0), efac) :
      (terms.size() == 1) ? *terms.begin() :
      mknary<PLUS>(terms);
  }

  template<typename Range> static Expr mkmult(Range& terms, ExprFactory &efac){
    return
      (terms.size() == 0) ? mkTerm (mpz_class (1), efac) :
      (terms.size() == 1) ? *terms.begin() :
      mknary<MULT>(terms);
  }

  template<typename Range1, typename Range2> static bool emptyIntersect(Range1& av, Range2& bv){
    for (auto &var1: av){
      for (auto &var2: bv) if (var1 == var2) return false;
    }
    return true;
  }

  template<typename Range> static bool emptyIntersect(Expr a, Range& bv){
    ExprVector av;
    filter (a, IsConst (), inserter(av, av.begin()));
    return emptyIntersect(av, bv);
  }

  inline static bool emptyIntersect(Expr a, Expr b){
    ExprVector bv;
    filter (b, IsConst (), inserter(bv, bv.begin()));
    return emptyIntersect(a, bv);
  }

  template<typename Range> static int intersectSize(Expr a, Range& bv){
    ExprVector av;
    filter (a, bind::IsConst (), inserter(av, av.begin()));
    ExprSet intersect;
    for (auto &var1: av){
      for (auto &var2: bv)
        if (var1 == var2) intersect.insert(var1);
    }
    return intersect.size();
  }

  inline static Expr multVar(Expr var, int coef){
    if (coef == 0)
      return mkTerm (mpz_class (0), var->getFactory());
    if (isOpX<MPZ>(var)) return
      mkTerm (mpz_class (lexical_cast<int>(var) * coef), var->getFactory());
    if (isOpX<MPQ>(var)) return
      mkTerm (mpq_class (lexical_cast<int>(var) * coef), var->getFactory());

    return mk<MULT>(mkTerm (mpz_class (coef), var->getFactory()), var);
  }

  inline static int isMultVar(Expr e, Expr var){
    if (e == var) return 1;
    if (!isOpX<MULT>(e)) return 0;
    if (isOpX<MPZ>(e->right()) && var == e->left()) return lexical_cast<int>(e->right());
    if (isOpX<MPZ>(e->left()) && var == e->right()) return lexical_cast<int>(e->left());
    if (isOpX<MPQ>(e->right()) && var == e->left()) return lexical_cast<int>(e->right());
    if (isOpX<MPQ>(e->left()) && var == e->right()) return lexical_cast<int>(e->left());
    return 0;
  }

  /**
   * Self explanatory
   */
  inline static bool isConstOrItsAdditiveInverse(Expr e, Expr var){
    if (e == var) {
      return true;
    }
    if (isOpX<MULT>(e)){
      if (lexical_cast<string>(e->left()) == "-1" && e->right() == var){
        return true;
      }
    }
    return false;
  }

  static void getAddTerm (Expr a, ExprVector &terms);
  static void getMultOps (Expr a, ExprVector &ops);

   /**
   * Self explanatory
   */
  inline static Expr additiveInverse(Expr e)
  {
    if (isOpX<MULT>(e))
    {
      cpp_int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      ExprVector rem;
      for (auto & a : ops)
      {
        if (isOpX<MPZ>(a))
        {
          coef *= lexical_cast<cpp_int>(a);
        }
        else
        {
          rem.push_back(a);
        }
      }

      Expr num = mkMPZ (-coef, e->getFactory());
      if (rem.empty() || coef == 0) return num;

      Expr remTerm = mkmult(rem, e->getFactory());
      if (coef == -1) return remTerm;

      return mk<MULT>(num, remTerm);
    }
    else if (isOpX<PLUS>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin (), end = e->args_end (); it != end; ++it)
      {
        getAddTerm(additiveInverse(*it), terms);
      }
      return mkplus(terms, e->getFactory());
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(additiveInverse(*e->args_begin ()), terms);
      auto it = e->args_begin () + 1;
      for (auto end = e->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
      return mkplus(terms, e->getFactory());
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isOpX<MPZ>(e))
    {
      return mkMPZ(-lexical_cast<cpp_int>(e), e->getFactory());
    }
    else if (isOpX<MPQ>(e)){
      string val = lexical_cast<string>(e);
      int delim = val.find("/");
      int val1 = stoi(val.substr(0, delim));
      int val2 = stoi(val.substr(delim + 1));
      if (delim < 0) {
        return mkTerm (mpq_class (-val1), e->getFactory());
      } else {
        string inv_val = to_string(-val1) + "/" + to_string(val2);
        return mkTerm (mpq_class (inv_val), e->getFactory());
      }
    }
    else if (isOpX<ITE>(e)){
      return mk<ITE>(e->left(), additiveInverse(e->right()), additiveInverse(e->last()));
    }
//    return mk<MULT>(mkMPZ ((-1), e->getFactory()), e);
    return mk<UN_MINUS>(e);
  }

  inline static void getPlusTerms (Expr a, ExprVector &terms)
  {
    if (isOpX<PLUS>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getPlusTerms(a->arg(i), terms);
      }
    }
    else if (isOpX<MINUS>(a)){
      // assume only two args
      terms.push_back(a->left());
      terms.push_back(additiveInverse(a->right()));
    } else {
      terms.push_back(a);
    }
  }

  // if at the end disjs is empty, then a == true
  inline static void getConj (Expr a, ExprSet &conjs)
  {
    if (isOpX<TRUE>(a)) return;
    if (isOpX<FALSE>(a)){
      conjs.clear();
      conjs.insert(a);
      return;
    } else if (isOpX<AND>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getConj(a->arg(i), conjs);
      }
    } else {
      conjs.insert(a);
    }
  }

  // if at the end disjs is empty, then a == false
  inline static void getDisj (Expr a, ExprSet &disjs)
  {
    if (isOpX<FALSE>(a)) return;
    if (isOpX<TRUE>(a)){
      disjs.clear();
      disjs.insert(a);
      return;
    } else if (isOpX<OR>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getDisj(a->arg(i), disjs);
      }
    } else {
      disjs.insert(a);
    }
  }

  inline static void getITEs (Expr a, ExprVector &ites)
  {
    if (isOpX<ITE>(a)){
      ites.push_back(a);
    } else {
      for (unsigned i = 0; i < a->arity(); i++)
        getITEs(a->arg(i), ites);
    }
  }

  inline static bool isNumeric(Expr a)
  {
    Expr aType = typeOf(a);
    return aType == mk<INT_TY>(a->getFactory()) || aType == mk<REAL_TY>(a->getFactory());
  }

  inline static void getMultOps (Expr a, ExprVector &ops)
  {
    if (isOpX<MULT>(a)){
      for (unsigned i = 0; i < a->arity(); i++){
        getMultOps(a->arg(i), ops);
      }
    } else if (isOpX<UN_MINUS>(a) && isNumeric(a->left())){
      ops.push_back(mkMPZ ((-1), a->getFactory()));
      ops.push_back(a->left());
    } else {
      ops.push_back(a);
    }
  }

  bool isBoolVarOrNegation(Expr exp)
  {
    if (bind::isBoolConst(exp)) return true;
    if (isOpX<NEG>(exp)) return isBoolVarOrNegation(exp->left());
    return false;
  }

  inline static Expr reBuildNegCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term))
    {
      return mk<GT>(lhs, rhs);
    }
    if (isOpX<GEQ>(term))
    {
      return mk<LT>(lhs, rhs);
    }
    if (isOpX<LT>(term))
    {
      return mk<GEQ>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<LEQ>(lhs, rhs);
  }

  // not very pretty method, but..
  inline static bool evaluateCmpConsts(Expr fla, cpp_int a, cpp_int b)
  {
    if (isOpX<EQ>(fla))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(fla))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(fla))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(fla))
    {
      return (a >= b);
    }
    if (isOpX<LT>(fla))
    {
      return (a < b);
    }
    assert(isOpX<GT>(fla));
    return (a > b);
  }

  inline static Expr mkNeg(Expr term)
  {
    if (isOpX<NEG>(term))
    {
      return term->arg(0);
    }
    else if (isOpX<FALSE>(term))
    {
      return mk<TRUE>(term->getFactory());
    }
    else if (isOpX<TRUE>(term))
    {
      return mk<FALSE>(term->getFactory());
    }
    else if (isOpX<AND>(term) || isOpX<OR>(term))
    {
      ExprSet args;
      for (int i = 0; i < term->arity(); i++){
        args.insert(mkNeg(term->arg(i)));
      }
      return isOpX<AND>(term) ? disjoin(args, term->getFactory()) :
      conjoin (args, term->getFactory());
    }
    else if (isOpX<IMPL>(term))
    {
      return mk<AND>(term->left(), mkNeg(term->right()));
    }
    else if (isOpX<IFF>(term))
    {
      return mk<OR>(mk<AND>(term->left(), mkNeg(term->right())),
                    mk<AND>(term->right(), mkNeg(term->left())));
    }
    else if (isOp<ComparissonOp>(term))
    {
      return reBuildNegCmp(term, term->arg(0), term->arg(1));
    }
    return mk<NEG>(term);
  }

  bool isBoolean(Expr a)
  {
    return typeOf(a) == mk<BOOL_TY>(a->getFactory());
  }

  /**
   * Represent Expr as multiplication
   */
  inline static Expr mult(Expr e){
    if (isOpX<MULT>(e)){
      return e;
    } else {
      return mk<MULT>(mkTerm (mpz_class (1), e->getFactory()), e);
    }
  }

  /**
   * Represent Zero as multiplication
   */
  inline static Expr multZero(Expr e, Expr multiplier){
    if (lexical_cast<string>(e) == "0")
      return mk<MULT>(multiplier, e);
    else return e;
  }

  /**
   * Rewrites distributivity rule:
   * a*b + a*c -> a*(b + c)
   * (assume, all common multipliers might be only in the first place)
   */
  inline static Expr exprDistributor(Expr e){
    if (e->arity () == 0) return e;
    Expr multiplier = mult(e->arg(0));
    ExprSet newE;
    newE.insert(multiplier->right());
    multiplier = multiplier->left();

    for (unsigned i = 1; i < e->arity (); i++){
      Expr a = mult(e->arg(i));
      if (isOpX<MULT>(a)){
        if (a->left() == multiplier){
          newE.insert(a->right());
        } else {
          return e;
        }
      } else {
        return e;
      }
    }
    if (isOpX<PLUS>(e)){
      return mk<MULT>(multiplier, mknary<PLUS>(newE));
    }
    return e;
  }

  /**
   * Commutativity in Addition
   */
  inline static Expr exprSorted(Expr e){
    outs() << "beginning of exprSorted: " << e << "\n";
    Expr res = e;
    if (isOpX<PLUS>(e)) {
      ExprVector expClauses;
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it){
        expClauses.push_back(*it);
      }
      // res = mknary<PLUS>(expClauses);
      res = mkplus(expClauses, e->efac());
    }

    if (isOpX<MULT>(e)) {
      if (lexical_cast<string>(e->left())  == "-1"){
        Expr l = e->right();

        if (isOpX<PLUS>(l)) {
          ExprVector expClauses;
          for (auto it = l->args_begin(), end = l->args_end(); it != end; ++it){
            expClauses.push_back(additiveInverse(*it));
          }
          // res = mknary<PLUS>(expClauses);
          res = mkplus(expClauses, e->efac());
        }
      }
    }
    outs() << "end of exprSorted: " << res << endl;

    return res;
  }

  /**
   * Helper used in ineqReverter
   */
  template <typename T> static Expr rewriteHelperN(Expr e){
    assert(e->arity() == 2);
    if (!isOpX<UN_MINUS>(e->left()) &&
        !(isOpX<MULT>(e->left()) &&
          lexical_cast<string>(e->left()->left()) == "-1") ) return e;

    return mk<T>(additiveInverse(e->left()), additiveInverse(exprDistributor(e->right())));
  }

  /**
   *  Helper used in ineqMover
   */
  template <typename T> static Expr rewriteHelperM(Expr e, Expr var){
    outs() << "beginning, rewriteHelperM, e: " << *e << endl;
    Expr l = e->left();
    Expr r = e->right();
    ExprVector orig_lhs, orig_rhs, lhs, rhs;
    ExprVector divVec, idivVec;

    // parse

    bool negLeft = false;
    getAddTerm(l, orig_lhs);
    getAddTerm(r, orig_rhs);
    for (auto & a : orig_lhs)
    {
      // capture un_minus
      if (isOpX<UN_MINUS>(a) && contains(a, var)) {a = a->left(); negLeft = true;}

      if ((isOp<DIV>(a) || isOp<IDIV>(a)) && contains(a->left(), var)){
        if (isOp<DIV>(a)) divVec.push_back(a->right());
        else idivVec.push_back(a->right());
        lhs.push_back(a->left());
      } else if (contains (a, var)) lhs.push_back(a);
      else rhs.push_back(additiveInverse(a));
    }
    for (auto & a : orig_rhs)
    {
      if (isOpX<UN_MINUS>(a) && contains(a, var)) {a = a->left(); negLeft = true;}

      if ((isOp<DIV>(a) || isOp<IDIV>(a)) && contains(a->left(), var)){
        if (isOp<DIV>(a)) divVec.push_back(a->right());
        else idivVec.push_back(a->right());
        lhs.push_back(a->left());
      } if (contains (a, var)) lhs.push_back(additiveInverse(a));
      else rhs.push_back(a);
    }
    outs() << "lhs: " << conjoin(lhs, e->getFactory()) << "\nrhs: " << conjoin(rhs, e->getFactory()) << endl;
    // combine results

    cpp_int coef = 0;
    for (auto it = lhs.begin(); it != lhs.end(); )
    {
      bool found = false;
      if (*it == var) { coef++; found = true; }
      if (isOpX<UN_MINUS>(*it) && (*it)->left() == var) { coef--; found = true; }
      if (isOpX<MULT>(*it) && 2 == (*it)->arity() && isOpX<MPZ>((*it)->left()) && (*it)->right() == var) {
        coef += lexical_cast<cpp_int>((*it)->left());
        found = true;
      }

      if (found) { it = lhs.erase(it); continue; }
      else ++it;
    }

    if (!lhs.empty())
    {
    errs() << "WARNING: COULD NOT NORMALIZE w.r.t. " << *var << ": "
          << *conjoin (lhs, e->getFactory()) << "\n";
      return e;
    }

    r = mkplus(rhs, e->getFactory());

    if (coef == 0){
      l = mkMPZ (0, e->getFactory());
    } else if (coef == 1){
      l = var;
    } else {
      l = mk<MULT>(mkMPZ(coef, e->getFactory()), var);
    }

    for (auto denom : divVec) l = mk<DIV>(l, denom);
    for (auto denom : idivVec) l = mk<IDIV>(l, denom);
    if (negLeft) l = mk<UN_MINUS>(l);

    outs() << "end, rewriteHelperM, e: " << mk<T>(l, r) << endl;
    return mk<T>(l,r);
  }

  /**
   * Helper used in exprMover
   */
  template <typename T> static Expr rewriteHelperE(Expr e, Expr var){
    assert(e->arity() == 2);
    Expr l = e->left();
    Expr r = e->right();
    if (r == var) {
      l = exprSorted(l);
      return mk<T>(r, l);
    }

    if (isOpX<MULT>(r)){
      if (r->left() == var || r->right() == var){
        l = exprSorted(l);
        return mk<T>(r, l);
      }
    }
    return e;
  }

  /**
   *  Merge adjacent inequalities
   *  (a <= b && a >= b) -> (a == b)
   */
  inline static void ineqMerger(ExprSet& expClauses, bool clean = false){
    vector<ExprSet::iterator> tmp;
    ExprSet newClauses;
    for (auto it1 = expClauses.begin(); it1 != expClauses.end(); ++it1){
      if (isOpX<LEQ>(*it1)){
        for (auto it2 = expClauses.begin(); it2 != expClauses.end(); ++it2){
          if (isOpX<GEQ>(*it2)){
            Expr e1l = exprSorted(mk<MINUS>((*it1)->left(), (*it1)->right()));
            Expr e2l = exprSorted(mk<MINUS>((*it2)->left(), (*it2)->right()));
            if ( e1l == e2l ){
              newClauses.insert(mk<EQ>(e1l, mkMPZ(0, e1l->getFactory())));
              if (clean){
                tmp.push_back (it1);
                tmp.push_back (it2);
                break;
              }
            }
          }
        }
      }
    }
    for (auto & it : tmp) expClauses.erase(it);
    expClauses.insert(newClauses.begin(), newClauses.end());
  }

  /**
   *  Merge adjacent inequalities
   *  (a <= b && b <= a) -> (a == b)
   */
  template <typename T> static void ineqMergerSwap(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->left() == e2->right() && e->right() == e2->left()){
              if (clean){
                expClauses.erase(e);
                expClauses.erase(e2);
              }
              expClauses.insert(mk<EQ>(e->left(), e->right()));
            }
          }
        }
      }
    }
  }

  /**
   *  Merge adjacent inequalities
   *  (a <= 0 && -a <= 0) -> (a == 0)
   *  (a >= 0 && -a >= 0) -> (a == 0)
   */
  template <typename T> static void ineqMergerSwapMinus(ExprSet& expClauses, bool clean = false){
    for (auto &e: expClauses){
      if (isOpX<T>(e)){
        for (auto &e2: expClauses){
          if (isOpX<T>(e2)){
            if (e->right() == e2->right() && e2->right() == mkTerm (mpz_class (0), e2->getFactory())){
              Expr l1 = exprSorted(additiveInverse(e->left()));
              Expr l2 = exprSorted(e2->left());
              if (l1 == l2){
                if (clean){
                  expClauses.erase(e);
                  expClauses.erase(e2);
                }
                expClauses.insert(mk<EQ>(e->left(), e->right()));
              }
            }
          }
        }
      }
    }
  }

  /**
   *  Trivial simplifier:
   *  (-1*a <= -1*b) -> (a >= b)
   *  (-1*a >= -1*b) -> (a <= b)
   *  (-1*a == -1*b) -> (a == b)
   */
  inline static Expr ineqReverter(Expr e){
      if (isOpX<LEQ>(e)){
        return rewriteHelperN<GEQ>(e);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperN<LEQ>(e);
      } else if (isOpX<LT>(e)){
        return rewriteHelperN<GT>(e);
      } else if (isOpX<GT>(e)){
        return rewriteHelperN<LT>(e);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperN<EQ>(e);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperN<NEQ>(e);
      }
    return e;
  }

  inline static Expr ineqNegReverter(Expr a){
    if (isOpX<NEG>(a)){
      Expr e = a->arg(0);
      if (isOpX<LEQ>(e)){
        return mk<GT>(e->arg(0), e->arg(1));
      } else if (isOpX<GEQ>(e)){
        return mk<LT>(e->arg(0), e->arg(1));
      } else if (isOpX<LT>(e)){
        return mk<GEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<GT>(e)){
        return mk<LEQ>(e->arg(0), e->arg(1));
      } else if (isOpX<NEQ>(e)){
        return mk<EQ>(e->arg(0), e->arg(1));
      } else if (isOpX<EQ>(e)){
        return mk<NEQ>(e->arg(0), e->arg(1));
      }
    }
    return a;
  }

  /**
   *  Transform the inequalities by the following rules:
   *  (a + .. + var + .. + b <= c ) -> (var <= -1*a + .. + -1*b + c)
   *  (a + .. + -1*var + .. + b <= c) -> (-1*var <= -1*a + .. + -1*b + c )
   *  (a <= b + .. + var + .. + c) -> (-1*var <= (-1)*a + b + .. + c)
   *  (a <= b + .. + (-1)*var + .. + c) -> (var <= (-1)*a + b + .. + c)
   *
   *  same for >=
   */
  inline static Expr ineqMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperM<LEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperM<GEQ>(e, var);
      } else if (isOpX<LT>(e)){
        return rewriteHelperM<LT>(e, var);
      } else if (isOpX<GT>(e)){
        return rewriteHelperM<GT>(e, var);
      } else if (isOpX<EQ>(e)){
        return rewriteHelperM<EQ>(e, var);
      } else if (isOpX<NEQ>(e)){
        return rewriteHelperM<NEQ>(e, var);
      }
    return e;
  }

  /**
   *  Move "var" to the left hand side of expression:
   *  (a <= var) -> (var >= b)
   *  (a >= var) -> (var <= b)
   *  (a == var) -> (var == b)
   */
  inline static Expr exprMover(Expr e, Expr var){
      if (isOpX<LEQ>(e)){
        return rewriteHelperE<GEQ>(e, var);
      } else if (isOpX<GEQ>(e)){
        return rewriteHelperE<LEQ>(e, var);
      } if (isOpX<EQ>(e)){
        return rewriteHelperE<EQ>(e, var);
      } if (isOpX<NEG>(e)){
        return mk<NEG>(exprMover(e->arg(0), var));
      }
    return e;
  }

  static Expr simplifyArithm (Expr exp, bool keepRedundandDisj, bool keepRedundandConj);

  /**
   *
   */
  inline static Expr eqDiffMover(Expr e){
    if(isOpX<EQ>(e)){
      if (isOpX<MINUS>(e->left()) && e->left()->arity() == 2 && lexical_cast<string>(e->right()) == "0"){
        return mk<EQ>(e->left()->left(), e->left()->right());
      }
    }
    return e;
  }

  /**
   * Search for an equality
   */
  inline static bool equalitySearch(ExprSet& expClauses, Expr var){
    for (auto &e: expClauses){
      if (isOpX<EQ>(e)){
        Expr l = e->left();
        Expr r = e->right();
        if (l == var || r == var){
          ExprSet singleton;
          singleton.insert(e);
          expClauses = singleton;
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Move var v to LHS of each expression and simplify
   */
  inline static Expr ineqSimplifier(Expr v, Expr exp, bool merge = false){
    ExprSet substsMap;
    if (isOpX<AND>(exp)){
      ExprSet cnjs;
      getConj(exp, cnjs);
      for (Expr cl : cnjs)
        substsMap.insert(ineqSimplifier(v, cl));

      if (merge) ineqMerger(substsMap, true);
      return conjoin(substsMap, v->getFactory());
    }
    else if (isOp<ComparissonOp>(exp))
    {
      exp = simplifyArithm(exp, false, false);
      exp = ineqMover(exp, v);
      exp = ineqReverter(exp);
    }
    return exp;
  }

  template<typename T>
  struct RW
  {
    std::shared_ptr<T> _r;

    RW (std::shared_ptr<T> r) : _r(r) {}
    RW (T *r) : _r (r) {}


    VisitAction operator() (Expr exp)
    {
      // -- apply the rewriter
      if (exp->arity() == 0)
        // -- do not descend into non-boolean operators
        return VisitAction::skipKids ();

      return VisitAction::changeDoKidsRewrite (exp, _r);

    }
  };

  inline static Expr simplifiedPlus (Expr exp, Expr to_skip){
    ExprVector args;
    Expr ret;
    bool f = false;

    for (ENode::args_iterator it = exp->args_begin(),
         end = exp->args_end(); it != end; ++it){
      if (*it == to_skip) f = true;
      else args.push_back (*it);
    }

    if (f == false)
    {
      args.push_back(additiveInverse(to_skip));
    }

    if (args.size() == 1) {
      ret = args[0];
    }

    else if (args.size() == 2){
      if (isOpX<UN_MINUS>(args[0]) && !isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[1], args[0]->left());
      else if (!isOpX<UN_MINUS>(args[0]) && isOpX<UN_MINUS>(args[1]))
        ret = mk<MINUS>(args[0], args[1]->left());

      else ret = mknary<PLUS>(args);

    } else {
      ret = mknary<PLUS>(args);
    }
    return ret;
  }

  // return a - b
  inline static Expr simplifiedMinus (Expr a, Expr b){
    Expr ret = mk<MINUS>(a, b);

    if (a == b) {
      ret = mkTerm (mpz_class (0), a->getFactory());
    } else

      if (isOpX<PLUS>(a)){
        return simplifiedPlus(a, b);
      } else

        if (isOpX<PLUS>(b)){
          Expr res = simplifiedPlus(b, a);
          return additiveInverse(res);
        } else

          if (isOpX<MINUS>(a)){
            if (a->left() == b) ret = additiveInverse(a->right());
          } else

            if (isOpX<MINUS>(b)){
              if (a == b->right()) ret = additiveInverse(b->left());
            } else

              if (isOpX<UN_MINUS>(b)) {
                if (b->left() == mkTerm (mpz_class (0), a->getFactory())) {
                  ret = a;
                } else {
                  ret = mk<PLUS>(a,b->left());
                }
              } else

                if (mkTerm (mpz_class (-1), a->getFactory()) == b) {
                  ret = mk<PLUS>(a, mkTerm (mpz_class (1), a->getFactory()));
                } else

                  if (b == mkTerm (mpz_class (0), a->getFactory())) {
                    ret = a;
                  } else

                    if (a == mkTerm (mpz_class (0), a->getFactory())){
                      if (isOpX<UN_MINUS>(b)){
                        ret = b->left();
                      }
                      else {
                        ret = additiveInverse(b);
                      }
                    }

    return ret;
  }

  inline static Expr reBuildCmp(Expr term, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(term)){
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(term)){
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<LEQ>(term)){
      return mk<LEQ>(lhs, rhs);
    }
    if (isOpX<GEQ>(term)){
      return mk<GEQ>(lhs, rhs);
    }
    if (isOpX<LT>(term)){
      return mk<LT>(lhs, rhs);
    }
    assert(isOpX<GT>(term));
    return mk<GT>(lhs, rhs);
  }

  inline static bool evaluateCmpConsts(Expr term)
  {
    if (!isOpX<MPZ>(term->left()) || !isOpX<MPZ>(term->right()))
      return false;
    int a = lexical_cast<int>(term->left());
    int b = lexical_cast<int>(term->right());
    if (isOpX<EQ>(term))
    {
      return (a == b);
    }
    if (isOpX<NEQ>(term))
    {
      return (a != b);
    }
    if (isOpX<LEQ>(term))
    {
      return (a <= b);
    }
    if (isOpX<GEQ>(term))
    {
      return (a >= b);
    }
    if (isOpX<LT>(term))
    {
      return (a < b);
    }
    assert(isOpX<GT>(term));
    return (a > b);
  }

  inline static int separateConst(ExprVector& plsOps)
  {
    int c = 0;
    for (auto it = plsOps.begin(); it != plsOps.end(); )
    {
      if (isOpX<MPZ>(*it))
      {
        c += lexical_cast<int>(*it);
        it = plsOps.erase(it);
        continue;
      }
      else ++it;
    }
    return c;
  }

  inline static Expr simplifyPlus (Expr exp)
  {
    ExprVector plsOps;
    getAddTerm (exp, plsOps);
    cpp_int c = separateConst(plsOps);
    std::sort(plsOps.begin(), plsOps.end(), [](Expr& x, Expr& y) {return x < y;});
    // GF: to write some kind of a fold-operator that counts the numbers of occurences
    if (c != 0) plsOps.push_back(mkMPZ(c, exp->getFactory()));
    return mkplus(plsOps, exp->getFactory());
  }

  inline static Expr simplifyMult (Expr e)
  {
    if (isOpX<MULT>(e))
    {
      cpp_int coef = 1;
      ExprVector ops;
      getMultOps (e, ops);

      ExprVector rem;
      for (auto a : ops)
      {
        if (isOpX<MPZ>(a))
          coef *= lexical_cast<cpp_int>(a);
        else
          rem.push_back(a);
      }

      Expr num = mkMPZ (coef, e->getFactory());
      if (rem.empty() || coef == 0) return num;

      Expr remTerm = mkmult(rem, e->getFactory());
      if (coef == 1) return remTerm;

      return mk<MULT>(num, remTerm);
    }
    return e;
  }

  inline static Expr simplifyMod (Expr e)
  {
    if (isOpX<MOD>(e) && isOpX<MPZ>(e->right()))
    {
      cpp_int coef = 1;
      cpp_int divider = lexical_cast<cpp_int>(e->right());
      ExprVector ops;
      getMultOps (e->left(), ops);

      for (auto a : ops)
        if (isOpX<MPZ>(a))
          coef *= lexical_cast<cpp_int>(a);

      if (coef % divider == 0)
        return mkMPZ (0, e->getFactory());
    }
    return e;
  }

  inline static Expr simplifyIte (Expr exp)  // simple version, on the syntactic level
  {
    ExprFactory &efac = exp->getFactory();
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getPlusTerms(exp->right(), plusOpsLeft);
    getPlusTerms(exp->last(), plusOpsRight);

    ExprVector commonTerms;
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      bool found = false;
      for (auto it2 = plusOpsRight.begin(); it2 != plusOpsRight.end(); )
      {
        if (*it1 == *it2)
        {
          if (lexical_cast<string>(*it1) != "0")
            commonTerms.push_back(*it1);
          found = true;
          plusOpsRight.erase(it2);
          break;
        }
        else
        {
          ++it2;
        }
      }
      if (found) it1 = plusOpsLeft.erase(it1);
      else ++it1;
    }

    Expr b1 = mkplus(plusOpsLeft, efac);
    Expr b2 = mkplus(plusOpsRight, efac);
    if (b1 == b2)
    {
      if (lexical_cast<string>(b1) != "0")
        commonTerms.push_back(b1);
    }
    else
    {
      commonTerms.push_back(mk<ITE>(exp->left(), b1, b2));
    }
    return mkplus(commonTerms, efac);
  }

  inline static Expr simplifyCmp (Expr exp)
  {
    ExprFactory &efac = exp->getFactory();
    if (evaluateCmpConsts(exp)) return mk<TRUE>(efac);

    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getPlusTerms(exp->left(), plusOpsLeft);
    getPlusTerms(exp->right(), plusOpsRight);

    int c1 = separateConst(plusOpsLeft);
    int c2 = separateConst(plusOpsRight);

    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      bool found = false;
      for (auto it2 = plusOpsRight.begin(); it2 != plusOpsRight.end(); )
      {
        if (*it1 == *it2)
        {
          found = true;
          plusOpsRight.erase(it2);
          break;
        }
        else
        {
          ++it2;
        }
      }
      if (found) it1 = plusOpsLeft.erase(it1);
      else ++it1;
    }

    plusOpsRight.push_back(mkTerm (mpz_class (c2 - c1), efac));

    return reBuildCmp(exp, mkplus(plusOpsLeft, efac), mkplus(plusOpsRight, efac));
  }

  static Expr simplifyArithmDisjunctions(Expr fla, bool keepRedundandDisj);
  static Expr simplifyArithmConjunctions(Expr fla, bool keepRedundandConj);

  struct SimplifyArithmExpr
  {
    Expr e;
    ExprFactory &efac;
    bool keepRedundandDisj;
    bool keepRedundandConj;

    SimplifyArithmExpr (Expr& _e, bool _d, bool _c) :
      e(_e), efac(_e->getFactory()), keepRedundandDisj(_d), keepRedundandConj(_c) {};

    Expr operator() (Expr exp)
    {
      if (isOpX<PLUS>(exp))
      {
        return simplifyPlus(exp);
      }

      if (isOpX<MINUS>(exp) && exp->arity() == 2)
      {
        return simplifiedMinus(exp->left(), exp->right());
      }

      if (isOpX<MULT>(exp))
      {
        return simplifyMult(exp);
      }

      if (isOpX<MOD>(exp))
      {
        return simplifyMod(exp);
      }

      if (isOpX<UN_MINUS>(exp))
      {
        return additiveInverse(exp->left());
      }

      if (isOpX<MINUS>(exp))
      {
        if (isOpX<UN_MINUS>(exp->right())) return mk<PLUS>(exp->left(), exp->right()->left());
      }

      if (isOp<ComparissonOp>(exp) && isNumeric(exp->right()))
      {
        return simplifyCmp(exp);
      }

      if (isOpX<ITE>(exp) && isNumeric(exp->right()))
      {
        return simplifyIte(exp);
      }

      // if (isOpX<OR>(exp))
      // {
      //   return simplifyArithmDisjunctions(exp, keepRedundandDisj && (e == exp));
      // }

      // if (isOpX<AND>(exp))
      // {
      //   return simplifyArithmConjunctions(exp, keepRedundandConj && (e == exp));
      // }
      return exp;
    }
  };

  inline static Expr simplifyBool (Expr exp);

  struct SimplifyBoolExpr
  {
    ExprFactory &efac;

    SimplifyBoolExpr (ExprFactory& _efac) : efac(_efac){};

    Expr operator() (Expr exp)
    {
      // GF: to enhance

      if (isOpX<IMPL>(exp))
      {
        if (isOpX<TRUE>(exp->right()))
          return mk<TRUE>(efac);

        if (isOpX<FALSE>(exp->right()))
          return mk<NEG>(exp->left());

        return (mk<OR>(
                 mk<NEG>(exp->left()),
                 exp->right()));
      }

      if (isOpX<EQ>(exp)){
        if (isOpX<TRUE>(exp->right())) return exp->left();
        if (isOpX<TRUE>(exp->left())) return exp->right();
        if (isOpX<FALSE>(exp->right())) return mkNeg(exp->left());
        if (isOpX<FALSE>(exp->right())) return mkNeg(exp->right());
      }

      if (isOpX<OR>(exp))
      {
        ExprSet dsjs;
        ExprSet newDsjs;
        getDisj(exp, dsjs);
        for (auto & a : dsjs){
          if (isOpX<TRUE>(a))
          {
            return mk<TRUE>(efac);
          }
          if (isOpX<FALSE>(a))
          {
            continue;
          }
          newDsjs.insert(simplifyBool(a));
        }
        return disjoin (newDsjs, efac);
      }

      if (isOpX<AND>(exp))
      {
        ExprSet cnjs;
        ExprSet newCnjs;
        getConj(exp, cnjs);
        for (auto & a : cnjs){
          if (isOpX<FALSE>(a))
          {
            return mk<FALSE>(efac);
          }
          if (isOpX<TRUE>(a))
          {
            continue;
          }
          newCnjs.insert(simplifyBool(a));
        }
        return conjoin (newCnjs, efac);
      }

      if (isOpX<ITE>(exp)){
        Expr cond = exp->arg(0);
        if (isOpX<TRUE>(cond))
        {
          return exp->arg(1);
        }
        else if (isOpX<FALSE>(cond))
        {
          return exp->arg(2);
        }
        else if (isOpX<TRUE>(exp->arg(1)) && isOpX<FALSE>(exp->arg(2)))
        {
          return cond;
        }
        else if (isOpX<FALSE>(exp->arg(1)) && isOpX<TRUE>(exp->arg(2)))
        {
          return mkNeg(cond);
        }
        else if (exp->arg(1) == exp->arg(2))
        {
          return exp->arg(1);
        }
      }

      if (isOpX<NEG>(exp) &&
        (isOp<ComparissonOp>(exp->left()) ||
        isOpX<TRUE>(exp->left()) || isOpX<FALSE>(exp->left())))
        return mkNeg(exp->left());

      return exp;
    }
  };

  inline static Expr simplifyArithm (Expr exp, bool keepRedundandDisj = false, bool keepRedundandConj = false)
  {
    RW<SimplifyArithmExpr> rw(new
      SimplifyArithmExpr(exp, keepRedundandDisj, keepRedundandConj));
    return dagVisit (rw, exp);
  }

  inline static Expr simplifyBool (Expr exp)
  {
    RW<SimplifyBoolExpr> rw(new SimplifyBoolExpr(exp->getFactory()));
    return dagVisit (rw, exp);
  }

  inline static void simplBoolReplCnjHlp(ExprVector& hardVars, ExprSet& cnjs, ExprVector& facts, ExprVector& repls)
  {
    bool toRestart;
    ExprSet toInsert;

    for (auto it = cnjs.begin(); it != cnjs.end(); )
    {
      if (isOpX<TRUE>(*it))
      {
        it = cnjs.erase(it);
        continue;
      }

      if (isOpX<NEG>(*it))
      {
        Expr negged = mkNeg((*it)->left());
        it = cnjs.erase(it);
        cnjs.insert(negged);
        continue;
      }

      Expr a = replaceAll(*it, facts, repls);

      if (isOpX<IMPL>(a))
      {
        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse) continue;
      }

      if (isOpX<EQ>(a))
      {
        // TODO: this could be symmetric

        Expr lhs = simplifyBool(a->left());
        bool isTrue = isOpX<TRUE>(lhs);
        bool isFalse = isOpX<FALSE>(lhs);

        if (isTrue) a = simplifyBool(a->right());
        else if (isFalse)
        {
          a = simplifyBool(mk<NEG>(a->right()));
        }
      }

      ExprSet splitted;
      getConj(a, splitted);
      toRestart = false;

      for (auto & c : splitted)
      {
        if (bind::isBoolConst(c))
        {
          bool nothard = find(hardVars.begin(), hardVars.end(), c) == hardVars.end();
          if (nothard)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(mk<NEG>(c));
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else if (isOpX<NEG>(c) && bind::isBoolConst(c->left()))
        {
          bool nothardLeft = find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end();
          if (nothardLeft)
          {
            toRestart = true;
            facts.push_back(c);
            repls.push_back(mk<TRUE>(a->getFactory()));
            facts.push_back(c->left());
            repls.push_back(mk<FALSE>(a->getFactory()));
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else if (isOpX<EQ>(c))
        {
          if (bind::isIntConst(c->left())  &&
              find(hardVars.begin(), hardVars.end(), c->left()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->left());
            repls.push_back(c->right());
          }
          else if (bind::isIntConst(c->right())  &&
                   find(hardVars.begin(), hardVars.end(), c->right()) == hardVars.end())
          {
            toRestart = true;
            facts.push_back(c->right());
            repls.push_back(c->left());
          }
          else
          {
            toInsert.insert(c);
          }
        }
        else
        {
          toInsert.insert(c);
        }
      }

      it = cnjs.erase(it);
      if (toRestart) break;
    }

    cnjs.insert(toInsert.begin(), toInsert.end());
    if (toRestart)
    {
      simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);
    }
  }

  // simplification based on boolean replacements
  inline static void simplBoolReplCnj(ExprVector& hardVars, ExprSet& cnjs)
  {
    ExprVector facts;
    ExprVector repls;

    simplBoolReplCnjHlp(hardVars, cnjs, facts, repls);

    for (int i = 0; i < facts.size() ; i++)
      if (!isOpX<NEG>(facts[i]))
        cnjs.insert(mk<EQ>(facts[i], repls[i]));
  }

  template <typename T> static Expr convertIntsToReals (Expr exp);

  template <typename T> struct IntToReal
  {
    IntToReal<T> () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<T>(exp))
      {
        ExprVector args;
        for (int i = 0; i < exp->arity(); i++)
        {
          Expr e = exp->arg(i);
          if (isOpX<MPZ>(e))
            e = mkTerm (mpq_class (lexical_cast<int>(e)), exp->getFactory());
          else {
            e = convertIntsToReals<PLUS>(e);
            e = convertIntsToReals<MINUS>(e);
            e = convertIntsToReals<MULT>(e);
            e = convertIntsToReals<UN_MINUS>(e);
          }
          args.push_back(e);
        }
        return mknary<T>(args);
      }
      return exp;
    }
  };

  template <typename T> static Expr convertIntsToReals (Expr exp)
  {
    RW<IntToReal<T>> rw(new IntToReal<T>());
    return dagVisit (rw, exp);
  }

  inline static ExprSet minusSets(ExprSet& v1, ExprSet& v2){
    ExprSet v3;
    bool res;
    for (auto &var1: v1){
      res = true;
      for (auto &var2: v2){
        if (var1 == var2) { res = false; break;}
      }
      if (res) v3.insert(var1);
    }
    return v3;
  }

  /**
   * To rem
   */
  inline bool containsOnlyOf(Expr a, Expr b)
  {
    ExprVector av;
    filter (a, bind::IsConst (), back_inserter (av));
    if (av.size() == 1) if (av[0] == b) return true;

    return false;
  }

  inline static Expr simplifiedAnd (Expr a, Expr b){
    ExprSet conjs;
    getConj(a, conjs);
    getConj(b, conjs);
    return
    (conjs.size() == 0) ? mk<TRUE>(a->getFactory()) :
    (conjs.size() == 1) ? *(conjs.begin()) :
    mknary<AND>(conjs);
  }

  inline int intersectSize(ExprVector& a, ExprVector& b){
    ExprSet c;
    for (auto &var: a)
      if (find(b.begin(), b.end(), var) != b.end()) c.insert(var);
    return c.size();
  }

  Expr projectITE(Expr ite, Expr var)
  {
    if (isOpX<ITE>(ite))
    {
      return mk<ITE>(ite->arg(0), projectITE(ite->arg(1), var), projectITE(ite->arg(2), var));
    }
    else
    {
      ExprSet cnjs;
      getConj(ite, cnjs);
      for (auto & a : cnjs)
      {
        if (a->left() == var) return a->right();
        else if (a->right() == var) return a->left();
      }

      assert(0);
    }
  }

  struct EqNumMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& eqs;
    Expr& var;

    EqNumMiner (Expr& _var, ExprSet& _eqs): var(_var), eqs(_eqs) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp) && (contains(exp, var)) && exp->right() != exp->left() &&
          isNumeric(exp->left()) && isNumeric(exp->right()))
      {
        eqs.insert(ineqMover(exp, var));
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  struct EqBoolMiner : public std::unary_function<Expr, VisitAction>
  {
    ExprSet& eqs;
    Expr& var;

    EqBoolMiner (Expr& _var, ExprSet& _eqs): var(_var), eqs(_eqs) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<EQ>(exp) && (exp->left() == var || exp->right() == var))
      {
        eqs.insert(exp);
        return VisitAction::skipKids ();
      }
      return VisitAction::doKids ();
    }
  };

  inline void getEqualities (Expr exp, Expr var, ExprSet& eqs)
  {
    if (bind::isIntConst(var) || bind::isRealConst(var))
    {
      EqNumMiner trm (var, eqs);
      dagVisit (trm, exp);
    }
    else
    {
      EqBoolMiner trm (var, eqs);
      dagVisit (trm, exp);
    }
  }

  struct QVMiner : public std::unary_function<Expr, VisitAction>
  {
    map<Expr, ExprVector>& vars;
    QVMiner (map<Expr, ExprVector>& _vars): vars(_vars) {};

    VisitAction operator() (Expr exp)
    {
      if (isOpX<FORALL>(exp) || isOpX<EXISTS>(exp))
      {
        for (int i = 0; i < exp->arity() - 1; i++)
          vars[exp].push_back(bind::fapp(exp->arg(i)));

        reverse(vars[exp].begin(),vars[exp].end());

        for (auto & a : vars)
          if (contains(a.first, exp) && a.first != exp)
            vars[exp].insert(vars[exp].end(), a.second.begin(), a.second.end());
      }
      return VisitAction::doKids ();
    }
  };

  inline void getQVars (Expr exp, map<Expr, ExprVector>& vars)
  {
    QVMiner qvm (vars);
    dagVisit (qvm, exp);
  }

  struct QFregularizer
  {
    ExprVector& vars;
    QFregularizer (ExprVector& _vars): vars(_vars){};
    Expr operator() (Expr exp)
    {
      if (bind::isBVar(exp)) return vars[bind::bvarId(exp)];
      return exp;
    }
  };

  inline static Expr regularizeQF (Expr exp)
  {
    map<Expr, ExprVector> vars;
    getQVars(exp, vars);
    ExprMap replaced;
    for (auto & a : vars)
    {
      Expr sub = replaceAll(a.first, replaced);
      RW<QFregularizer> rw(new QFregularizer(a.second));
      Expr b = dagVisit (rw, sub);
      replaced[a.first] = b;
      exp = replaceAll(exp, sub, b);
    }

    return exp;
  }

  inline static bool isNumericConst(Expr e)
  {
    return isOpX<MPZ>(e) || isOpX<MPQ>(e);
  }

  static Expr rewriteMultAdd (Expr exp);

  inline static void getAddTerm (Expr a, ExprVector &terms) // implementation (mutually recursive)
  {
    if (isOpX<PLUS>(a))
    {
      for (auto it = a->args_begin (), end = a->args_end (); it != end; ++it)
      {
        getAddTerm(*it, terms);
      }
    }
    else if (isOpX<MINUS>(a))
    {
      auto it = a->args_begin ();
      auto end = a->args_end ();
      getAddTerm(*it, terms);
      ++it;
      for (; it != end; ++it)
      {
        getAddTerm(additiveInverse(*it), terms);
      }
    }
    else if (isOpX<UN_MINUS>(a))
    {
      ExprVector tmp;
      getAddTerm(a->left(), tmp);
      for (auto & t : tmp)
      {
        bool toadd = true;
        for (auto it = terms.begin(); it != terms.end(); )
        {
          if (*it == t)
          {
            terms.erase(it);
            toadd = false;
            break;
          }
          else ++it;
        }
        if (toadd) terms.push_back(additiveInverse(t));
      }
    }
    else if (isOpX<MULT>(a))
    {
      Expr tmp = rewriteMultAdd(a);
      if (tmp == a) terms.push_back(a);
      else getAddTerm(tmp, terms);
    }
    else if (lexical_cast<string>(a) != "0")
    {
      bool found = false;
      for (auto it = terms.begin(); it != terms.end(); )
      {
        if (additiveInverse(*it) == a)
        {
          terms.erase(it);
          found = true;
          break;
        }
        else ++it;
      }
      if (!found) terms.push_back(a);
    }
  }

  struct AddMultDistr
  {
    AddMultDistr () {};

    Expr operator() (Expr exp)
    {
      if (isOpX<MULT>(exp) && exp->arity() == 2)
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();

        ExprVector alllhs;
        getAddTerm(lhs, alllhs);

        ExprVector allrhs;
        getAddTerm(rhs, allrhs);

        ExprVector unf;
        for (auto &a : alllhs)
        {
          for (auto &b : allrhs)
          {
            unf.push_back(mk<MULT>(a, b));
          }
        }
        return mkplus(unf, exp->getFactory());
      }

      return exp;
    }
  };

  inline static Expr rewriteMultAdd (Expr exp)
  {
    RW<AddMultDistr> mu(new AddMultDistr());
    return dagVisit (mu, exp);
  }

  inline Expr rewriteDivConstraints(Expr fla)
  {
    // heuristic for the divisibility constraints
    assert (isOp<ComparissonOp>(fla));
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(fla->left(), plusOpsLeft);
    getAddTerm(fla->right(), plusOpsRight);
    Expr lhs = NULL;
    for (auto & a : plusOpsRight) plusOpsLeft.push_back(additiveInverse(a));
    plusOpsRight.clear();
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      if (isOpX<IDIV>(*it1))
      {
        lhs = *it1;
        plusOpsLeft.erase(it1);
        for (auto & a : plusOpsLeft) plusOpsRight.push_back(additiveInverse(a));
        break;
      }
      if (isOpX<UN_MINUS>(*it1) && isOpX<IDIV>((*it1)->left()))
      {
        lhs = (*it1)->left();
        plusOpsLeft.erase(it1);
        for (auto & a : plusOpsLeft) plusOpsRight.push_back(a);
        break;
      }
      ++it1;
    }

    if (lhs == NULL) return fla;
    Expr rhs = mkplus(plusOpsRight, fla->getFactory());

    if (isOpX<EQ>(fla))
      return mk<AND>(mk<GEQ>(lhs->left(), mk<MULT>(lhs->right(), rhs)),
        mk<GT>(mk<PLUS> (mk<MULT>(lhs->right(), rhs), lhs->right()), lhs->left()));
    else if (isOpX<NEQ>(fla))
      return mk<OR>(mk<GT>(mk<MULT>(lhs->right(), rhs), lhs->left()),
        mk<GEQ>(lhs->left(), mk<PLUS> (mk<MULT>(lhs->right(), rhs), lhs->right())));
    return fla;
  }

  inline Expr rewriteModConstraints(Expr fla)
  {

    // heuristic for the divisibility constraints
    assert (isOp<ComparissonOp>(fla));
    ExprVector plusOpsLeft;
    ExprVector plusOpsRight;
    getAddTerm(fla->left(), plusOpsLeft);
    getAddTerm(fla->right(), plusOpsRight);
    Expr lhs = NULL;
    for (auto & a : plusOpsRight) plusOpsLeft.push_back(additiveInverse(a));
    plusOpsRight.clear();
    cpp_int c1, c2;
    for (auto it1 = plusOpsLeft.begin(); it1 != plusOpsLeft.end(); )
    {
      if (isOpX<MOD>(*it1))
      {
        Expr d = simplifyArithm((*it1)->last());
        if (isNumericConst(d))
        {
          lhs = replaceAll(*it1, (*it1)->last(), d);
          c1 = lexical_cast<cpp_int>(d);
          plusOpsLeft.erase(it1);
          for (auto & a : plusOpsLeft) plusOpsRight.push_back(additiveInverse(a));
          plusOpsLeft.clear();
          break;
        }
      }
      ++it1;
    }
    if (!plusOpsLeft.empty() || lhs == NULL) return fla;

    Expr rhs = mkplus(plusOpsRight, fla->getFactory());
    rhs = simplifyArithm(rhs);
    if (isNumericConst(rhs)) c2 = lexical_cast<cpp_int>(rhs);
    else return fla;

    ExprSet dsjs;
    for (auto i = 0; i < c1; i++)
      if (evaluateCmpConsts(fla, i, c2))
        dsjs.insert(mk<EQ>(lhs, mkMPZ(i, fla->getFactory())));

    fla = disjoin(dsjs, fla->getFactory());
    return fla;
  }

  // rewrite just equalities
  template<typename Range> static Expr simpleQE(Expr exp, Range& quantified)
  {
    ExprFactory& efac = exp->getFactory();
    ExprSet cnjsSet;
    getConj(exp, cnjsSet);
    ExprVector cnjs;
    cnjs.insert(cnjs.end(), cnjsSet.begin(), cnjsSet.end());
    for (auto & var : quantified)
    {
      ExprSet eqs;
      Expr store; // todo: extend to ExprSet

      for (unsigned it = 0; it < cnjs.size(); )
      {
        Expr cnj = cnjs[it];
        if (!isOpX<EQ>(cnj) || !contains(cnj, var))
          { it++; continue;}

        Expr normalized = cnj;
        if (isNumeric(var) && isNumeric(cnj->left()))
        {
          normalized = simplifyArithm(
            mk<EQ>(mk<PLUS>(cnj->arg(0), additiveInverse(cnj->arg(1))),
              mkMPZ (0, efac)));
          normalized = ineqSimplifier(var, normalized);
        }
        else if (var == normalized->right())
        {
          normalized = mk<EQ>(normalized->right(), normalized->left());
        }

        // after the normalization, var can be eliminated
        if (!isOpX<EQ>(normalized) || !contains(normalized, var))
          { it++; continue;}

        if (!contains (normalized->right(), var))
        {
          if (var == normalized->left())
          {
            eqs.insert(normalized->right());
            cnjs.erase (cnjs.begin()+it);
            continue;
          }
          else if (isOpX<MULT>(normalized->left()) && isOpX<MPZ>(normalized->left()->left()))
          {
            cnjs.push_back(mk<EQ>(mk<MOD>(normalized->right(), normalized->left()->left()),
                               mkMPZ (0, efac)));
          }
        }

        if (store == NULL && containsOp<STORE>(normalized) && isOpX<EQ>(normalized) &&
            emptyIntersect(normalized->left(), quantified) &&
            isOpX<STORE>(normalized->right()) && var == normalized->right()->left()) {
          // one level of storing (to be extended)
          store = normalized;
        }

//        errs() << "WARNING: COULD NOT NORMALIZE w.r.t. " << *var << ": "
//               << *normalized << "     [[  " << *cnj << "  ]]\n";

        cnjs[it] = normalized;
        it++;
      }

      if (store != NULL) {
        // assume "store" = (A = store(var, x, y))
        for (unsigned it = 0; it < cnjs.size(); it++) {
          ExprVector se;
          filter (cnjs[it], IsSelect (), inserter(se, se.begin()));
          for (auto s : se) {
            if (contains(store, s)) continue;
            if (s->left() == var) {
              Expr cmp = simplifyCmp(mk<EQ>(store->right()->right(), s->right()));
              cnjs[it] = replaceAll(cnjs[it], s, simplifyIte(
                         mk<ITE>(cmp,
                                 store->right()->last(),
                                 mk<SELECT>(store->left(), s->right()))));
            }
          }
        }
      }

      if (eqs.empty()) continue;

      Expr repl = *eqs.begin();
      bool no_qv = emptyIntersect(repl, quantified);
      int min_sz = treeSize(repl);
      int is_const = isOpX<MPZ>(repl);

      // first, search for a non-constant replacement without quantified vars, if possible
      for (auto cnj = std::next(eqs.begin()); cnj != eqs.end(); cnj++) {
        bool no_qv_cur = emptyIntersect(*cnj, quantified);
        int sz_cur = treeSize(*cnj);
        int is_const_cur = isOpX<MPZ>(*cnj);
        if (no_qv < no_qv_cur || (no_qv_cur && is_const) || (sz_cur < min_sz && !is_const_cur)) {
          repl = *cnj;
          min_sz = sz_cur;
          no_qv = no_qv_cur;
          is_const = is_const_cur;
        }
      }

      // second, make sure that all replacements are equal
      for (auto cnj = eqs.begin(); cnj != eqs.end(); cnj++)
        if (*cnj != repl) cnjs.push_back(mk<EQ>(repl, *cnj));

      // finally, replace the remaining cnjs
      for (unsigned it = 0; it < cnjs.size(); it++)
        cnjs[it] = replaceAll(cnjs[it], var, repl);

    }

    return (conjoin(cnjs, exp->getFactory()));
  }


  // similar to simplifyArithmDisjunctions
  inline static Expr simplifyArithmConjunctions(Expr fla, bool keep_redundand = false)
  {
    ExprFactory& efac = fla->getFactory();
    ExprSet cnjs, newCnjs;
    getConj(fla, cnjs);
    if (cnjs.size() == 1) return *cnjs.begin();
    ExprSet lin_coms;

    // search for a var, const*var or whatever exists in any conjunct
    for (auto & d : cnjs) {
      // outs() << "simpAritConj inloop d: " << d << endl; //outTest
      if (!isOp<ComparissonOp>(d) ||
          !isNumeric(d->arg(0))) {
        newCnjs.insert(d);
        // outs() << "continue" << endl; //outTest
        continue;
      }

      Expr tmp = simplifyArithm(
        reBuildCmp(d, mk<PLUS>(d->arg(0), additiveInverse(d->arg(1))),
                   mkMPZ (0, efac)));
      tmp = ineqReverter(tmp);

      if (isOpX<TRUE>(tmp)) continue;
      if (isOpX<FALSE>(tmp)) return tmp;

      newCnjs.insert(tmp);
      lin_coms.insert(tmp->arg(0));
    }
    outs() << "I'm done" << endl;
    if (lin_coms.size() == 0)
    {
      if (!keep_redundand) ineqMerger(cnjs, true);
      return conjoin(cnjs, efac);
    }
    outs() << "done twice" << endl;
    for (auto &lin_com : lin_coms) {
      outs() << "lin_com: " << lin_com << endl;
      cpp_int cur_max_gt;
      cpp_int cur_max_ge;
      cpp_int cur_min_lt;
      cpp_int cur_min_le;

      bool cur_max_gt_bl = false;
      bool cur_max_ge_bl = false;
      bool cur_min_lt_bl = false;
      bool cur_min_le_bl = false;

      set<cpp_int> all_diseqs;

      for (auto it = newCnjs.begin(); it != newCnjs.end(); ) {
        auto d = *it;

        if (!isOp<ComparissonOp>(d) ||
            d->arg(0) != lin_com ||
            !isOpX<MPZ>(d->arg(1))) {
          ++it;
          continue;
        }

        cpp_int c = lexical_cast<cpp_int>(d->arg(1));

        if (isOpX<NEQ>(d))  {
          all_diseqs.insert(c);
        }
        if (isOpX<LEQ>(d)) {
          cur_min_le = cur_min_le_bl ? min(cur_min_le, c) : c;
          cur_min_le_bl = true;
        }
        if (isOpX<GEQ>(d)) {
          cur_max_ge = cur_max_ge_bl ? max(cur_max_ge, c) : c;
          cur_max_ge_bl = true;
        }
        if (isOpX<LT>(d)) {
          cur_min_lt = cur_min_lt_bl ? min(cur_min_lt, c) : c;
          cur_min_lt_bl = true;
        }
        if (isOpX<GT>(d)) {
          cur_max_gt = cur_max_gt_bl ? max(cur_max_gt, c) : c;
          cur_max_gt_bl = true;
        }
        if (isOpX<EQ>(d)) {
          cur_max_ge = cur_max_ge_bl ? max(cur_max_ge, c) : c;
          cur_min_le = cur_min_le_bl ? min(cur_min_le, c) : c;
          cur_max_ge_bl = true;
          cur_min_le_bl = true;
        }
        if (keep_redundand) it++;
        else newCnjs.erase (it++);
      }

      if (cur_min_le_bl)
        while (true) {
          auto tmp = cur_min_le;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_min_le) {
              cur_min_le--;
              if (keep_redundand)
                newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
              it = all_diseqs.erase(it);
            } else if (*it > cur_min_le) { // remove redundand, e.g., (x != 7 /\ x <= 5)
              if (keep_redundand)
                newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (*it, efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_le) break;
        }

      if (cur_min_lt_bl)
        while (true) {
          auto tmp = cur_min_lt;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_min_lt - 1) {
              cur_min_lt--;
              if (keep_redundand)
                newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
              it = all_diseqs.erase(it);
            } else if (*it >= cur_min_lt) {  // remove redundand, e.g., (x != 5 /\ x < 5)
              if (keep_redundand)
                newCnjs.insert(mk<LT>(lin_com, mkMPZ (*it, efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_lt) break;
        }

      if (cur_max_ge_bl)
        while (true) {
          auto tmp = cur_max_ge;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_max_ge) {
              cur_max_ge++;
              if (keep_redundand)
                newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
              it = all_diseqs.erase(it);
            } else if (*it < cur_max_ge) { // remove redundand, e.g., (x != 4 /\ x >= 5)
              if (keep_redundand)
                newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (*it, efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_ge) break;
        }

      if (cur_max_gt_bl)
        while (true) {
          auto tmp = cur_max_gt;
          for (auto it = all_diseqs.begin(); it != all_diseqs.end(); ) {
            if (*it == cur_max_gt + 1) {
              cur_max_gt++;
              if (keep_redundand)
                newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
              it = all_diseqs.erase(it);
            } else if (*it <= cur_max_gt) { // remove redundand, e.g., (x != 5 /\ x > 5)
              if (keep_redundand)
                newCnjs.insert(mk<GT>(lin_com, mkMPZ (*it, efac)));
              it = all_diseqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_gt) break;
        }

      for (auto c : all_diseqs) {
        newCnjs.insert (mk<NEQ>(lin_com, mkMPZ (c, efac)));
      }

      if ((cur_max_gt_bl && cur_min_lt_bl && cur_max_gt >= cur_min_lt - 1) || // e.g., (x > 3 /\ x < 4)
          (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge >= cur_min_lt) ||
          (cur_max_gt_bl && cur_min_le_bl && cur_max_gt >= cur_min_le) ||
          (cur_max_ge_bl && cur_min_le_bl && cur_max_ge >= cur_min_le + 1))
        return mk<FALSE>(efac);

      if (cur_max_ge_bl && cur_min_le_bl && cur_max_ge == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_min_le, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_le_bl && cur_max_gt + 1 == cur_min_le && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_min_le, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_ge_bl && cur_min_lt_bl && cur_max_ge + 1 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_max_ge, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_max_gt_bl && cur_min_lt_bl && cur_max_gt + 2 == cur_min_lt && newCnjs.empty())
      {
        Expr res = mk<EQ>(lin_com, mkMPZ (cur_max_gt + 1, efac));
        if (keep_redundand) newCnjs.insert(res);
        else return res;
      }

      if (cur_min_le_bl && cur_min_lt_bl) {
        if (cur_min_le >= cur_min_lt) {
          newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
        }
        else {
          newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
        }
      }
      else {
        if (cur_min_le_bl) {
          newCnjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_min_le, efac)));
        }
        if (cur_min_lt_bl) {
          newCnjs.insert(mk<LT>(lin_com, mkMPZ (cur_min_lt, efac)));
        }
      }

      if (cur_max_ge_bl && cur_max_gt_bl) {
        if (cur_max_ge <= cur_max_gt) {    // e.g., x > 5 /\ x >= 5
          newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
        }
        else {
          newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
        }
      }
      else {
        if (cur_max_ge_bl) {
          newCnjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_max_ge, efac)));
        }
        if (cur_max_gt_bl) {
          newCnjs.insert(mk<GT>(lin_com, mkMPZ (cur_max_gt, efac)));
        }
      }

    }
    outs() << "After long loop, conj(newCnjs)" << conjoin(newCnjs, efac) << endl;
    if (!keep_redundand) ineqMerger(newCnjs, true);
    return conjoin(newCnjs, efac);
  }

  // symmetric to simplifyArithmConjunctions
  inline static Expr simplifyArithmDisjunctions(Expr fla, bool keep_redundand = false)
  {
    ExprFactory& efac = fla->getFactory();
    ExprSet dsjs, newDsjs;
    getDisj(fla, dsjs);
    if (dsjs.size() == 1) return *dsjs.begin();

    ExprSet lin_coms;

    // search for a var, const*var or whatever exists in any disjunct
    for (auto & d : dsjs) {

      if (!isOp<ComparissonOp>(d) ||
          !isNumeric(d->arg(0))) {
        newDsjs.insert(d);
        continue;
      }

      Expr tmp = simplifyArithm(
          reBuildCmp(d, mk<PLUS>(d->arg(0), additiveInverse(d->arg(1))), mkMPZ (0, efac)));

      if (isOpX<TRUE>(tmp)) return tmp;
      if (isOpX<FALSE>(tmp)) continue;

      tmp = ineqReverter(tmp);
      newDsjs.insert(tmp);
      lin_coms.insert(tmp->arg(0));
    }

    if (lin_coms.size() == 0) return disjoin(dsjs, efac);

    for (auto &lin_com : lin_coms) {

      cpp_int cur_min_gt;
      cpp_int cur_min_ge;
      cpp_int cur_max_lt;
      cpp_int cur_max_le;

      bool cur_min_gt_bl = false;
      bool cur_min_ge_bl = false;
      bool cur_max_lt_bl = false;
      bool cur_max_le_bl = false;

      set<cpp_int> all_eqs;

      for (auto it = newDsjs.begin(); it != newDsjs.end(); ) {
        auto d = *it;

        if (!isOp<ComparissonOp>(d) ||
            d->arg(0) != lin_com ||
            !isOpX<MPZ>(d->arg(1))) {
          ++it;
          continue;
        }

        cpp_int c = lexical_cast<cpp_int>(d->arg(1));

        if (isOpX<EQ>(d))  {
          all_eqs.insert(c);
        }
        if (isOpX<LEQ>(d)) {
          cur_max_le = cur_max_le_bl ? max(cur_max_le, c) : c;
          cur_max_le_bl = true;
        }
        if (isOpX<GEQ>(d)) {
          cur_min_ge = cur_min_ge_bl ? min(cur_min_ge, c) : c;
          cur_min_ge_bl = true;
        }
        if (isOpX<LT>(d))  {
          cur_max_lt = cur_max_lt_bl ? max(cur_max_lt, c) : c;
          cur_max_lt_bl = true;
        }
        if (isOpX<GT>(d))  {
          cur_min_gt = cur_min_gt_bl ? min(cur_min_gt, c) : c;
          cur_min_gt_bl = true;
        }
        if (isOpX<NEQ>(d)) {
          cur_min_gt = cur_min_gt_bl ? min(cur_min_gt, c) : c;
          cur_max_lt = cur_max_lt_bl ? max(cur_max_lt, c) : c;
          cur_min_gt_bl = true;
          cur_max_lt_bl = true;
        }
        if (keep_redundand) it++;
        else newDsjs.erase (it++);
      }

      if (cur_max_le_bl)
        while (true) {
          auto tmp = cur_max_le;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_max_le + 1) {
              cur_max_le++;
              if (keep_redundand)
                newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
              it = all_eqs.erase(it);
            } else if (*it <= cur_max_le) { // remove redundand, e.g., (x = 3 \/ x <= 5)
              if (keep_redundand)
                newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (*it, efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_le) break;
        }

      if (cur_max_lt_bl)
        while (true) {
          auto tmp = cur_max_lt;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_max_lt) {
              cur_max_lt++;
              if (keep_redundand)
                newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
              it = all_eqs.erase(it);
            } else if (*it < cur_max_lt) {  // remove redundand, e.g., (x = 4 \/ x < 5)
              if (keep_redundand)
                newDsjs.insert(mk<LT>(lin_com, mkMPZ (*it, efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_max_lt) break;
        }

      if (cur_min_ge_bl)
        while (true) {
          auto tmp = cur_min_ge;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_min_ge - 1) {
              cur_min_ge--;
              if (keep_redundand)
                newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
              it = all_eqs.erase(it);
            } else if (*it >= cur_min_ge) { // remove redundand, e.g., (x = 9 \/ x >= 5)
              if (keep_redundand)
                newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (*it, efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_ge) break;
        }

      if (cur_min_gt_bl)
        while (true) {
          auto tmp = cur_min_gt;
          for (auto it = all_eqs.begin(); it != all_eqs.end(); ) {
            if (*it == cur_min_gt) {
              cur_min_gt--;
              if (keep_redundand)
                newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
              it = all_eqs.erase(it);
            } else if (*it > cur_min_gt) { // remove redundand, e.g., (x = 6 \/ x > 5)
              if (keep_redundand)
                newDsjs.insert(mk<GT>(lin_com, mkMPZ (*it, efac)));
              it = all_eqs.erase(it);
            }
            else ++it;
          }
          if (tmp == cur_min_gt) break;
        }

      for (auto c : all_eqs) {
        newDsjs.insert (mk<EQ>(lin_com, mkMPZ (c, efac)));
      }

      if ((cur_min_gt_bl && cur_max_lt_bl && cur_min_gt <= cur_max_lt - 1) ||
          (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge <= cur_max_lt) ||
          (cur_min_gt_bl && cur_max_le_bl && cur_min_gt <= cur_max_le) ||
          (cur_min_ge_bl && cur_max_le_bl && cur_min_ge <= cur_max_le + 1))
        return mk<TRUE>(efac);

      if (cur_min_gt_bl && cur_max_lt_bl && cur_min_gt == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_max_lt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_lt_bl && cur_min_ge - 1 == cur_max_lt && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_max_lt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_gt_bl && cur_max_le_bl && cur_min_gt - 1 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_min_gt, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_min_ge_bl && cur_max_le_bl && cur_min_ge - 2 == cur_max_le && newDsjs.empty())
      {
        Expr res = mk<NEQ>(lin_com, mkMPZ (cur_min_ge - 1, efac));
        if (keep_redundand) newDsjs.insert(res);
        else return res;
      }

      if (cur_max_le_bl && cur_max_lt_bl) {
        if (cur_max_le >= cur_max_lt) {
          newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
        }
        else {
          newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
        }
      }
      else {
        if (cur_max_le_bl) {
          newDsjs.insert(mk<LEQ>(lin_com, mkMPZ (cur_max_le, efac)));
        }
        if (cur_max_lt_bl) {
          newDsjs.insert(mk<LT>(lin_com, mkMPZ (cur_max_lt, efac)));
        }
      }

      if (cur_min_ge_bl && cur_min_gt_bl) {
        if (cur_min_ge <= cur_min_gt) {
          newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
        }
        else {
          newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
        }
      }
      else {
        if (cur_min_ge_bl) {
          newDsjs.insert(mk<GEQ>(lin_com, mkMPZ (cur_min_ge, efac)));
        }
        if (cur_min_gt_bl) {
          newDsjs.insert(mk<GT>(lin_com, mkMPZ (cur_min_gt, efac)));
        }
      }
    }

    return disjoin(newDsjs, efac);
  }
  template <typename Z>
  Expr getZ3Expr(Expr e, Z& z3, bool removeFile = true)
  {
    // send Expr to a file and read it back in through Z3.
    outs() << "To send to file\n    " << e << "\n";
    ZSolver<EZ3> solver(z3);
    solver.assertExpr(e);

    std::ofstream file;
    const char* filename = "z3_expr.txt";
    file.open(filename);
    solver.toSmtLib(outs());
    solver.toSmtLib(file);
    file.close();
    Expr res = z3_from_smtlib_file (z3, filename);
    if(removeFile) remove(filename); // delete the temp file.

    return res;
  }

  void getLiterals (Expr exp, ExprSet& lits)
  {
    ExprFactory& efac = exp->getFactory();
    if (isOpX<EQ>(exp) && isNumeric(exp->left()) && !containsOp<MOD>(exp))
    {
      getLiterals(mk<GEQ>(exp->left(), exp->right()), lits);
      getLiterals(mk<LEQ>(exp->left(), exp->right()), lits);
      return;
    }
    else if (isOpX<NEQ>(exp) && isNumeric(exp->left()) && !containsOp<MOD>(exp))
    {
      getLiterals(mk<GT>(exp->left(), exp->right()), lits);
      getLiterals(mk<LT>(exp->left(), exp->right()), lits);
      return;
    }
    else if ((isOpX<EQ>(exp) || isOpX<NEQ>(exp)) && isBoolean(exp->left()))
    {
      getLiterals(exp->left(), lits);
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(exp->right(), lits);
      getLiterals(mkNeg(exp->right()), lits);
      return;
    }
    else if (isOpX<NEG>(exp))
    {
      if (bind::isBoolConst(exp->left()))
        lits.insert(exp);
      else
        getLiterals(mkNeg(exp->left()), lits);
      return;
    }
    else if (isOpX<IMPL>(exp))
    {
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(exp->right(), lits);
      return;
    }
    else if (isOpX<IFF>(exp))
    {
      getLiterals(mkNeg(exp->left()), lits);
      getLiterals(exp->right(), lits);
      getLiterals(mkNeg(exp->right()), lits);
      getLiterals(exp->left(), lits);
      return;
    }
    else if (bind::typeOf(exp) == mk<BOOL_TY>(efac) &&
        !containsOp<AND>(exp) && !containsOp<OR>(exp))
    {
      if (isOp<ComparissonOp>(exp))
      {
        exp = rewriteDivConstraints(exp);
        exp = rewriteModConstraints(exp);
        if (isOpX<AND>(exp) || isOpX<OR>(exp))
          getLiterals(exp, lits);
        else lits.insert(exp);
      }
      else lits.insert(exp);
      return;
    }
    else if (isOpX<AND>(exp) || isOpX<OR>(exp))
    {
      for (int i = 0; i < exp->arity(); i++)
        getLiterals(exp->arg(i), lits);
      return;
    }
    else if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp))
      return;
    outs () << "unable lit: " << *exp << "\n";
    assert(0);
  }
}

#endif
