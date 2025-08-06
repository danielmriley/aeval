#ifndef EXPRSIMPLBV__HPP__
#define EXPRSIMPLBV__HPP__
#include <assert.h>

#include "ExprSimpl.hpp"

using namespace std;
using namespace expr::op::bind;
using namespace expr::op::bv;
using namespace boost;
using namespace boost::multiprecision;

namespace ufo
{
  template <typename Range>
  static Expr eraseLexicogrMinimal(Range &exprs)
  {
    auto cur = exprs.begin();
    for (auto it = std::next(cur); it != exprs.end(); ++it)
      if (lexical_cast<string>(*cur) > lexical_cast<string>(*it))
        cur = it;
    Expr res = *cur;
    exprs.erase(cur);
    return res;
  }

  template <typename Op, typename Range>
  static Expr mkb(Range &terms, Expr neut)
  {
    if (terms.empty())
      return neut;
    if (terms.size() == 1)
      return *terms.begin();
    Expr tmp = mk<Op>(eraseLexicogrMinimal(terms), eraseLexicogrMinimal(terms));
    while (!terms.empty())
      tmp = mk<Op>(tmp, eraseLexicogrMinimal(terms));
    return tmp;
  }

  template <typename Op>
  static void getBVOps(Expr a, ExprVector &ops)
  {
    if (isOpX<Op>(a))
    {
      for (unsigned i = 0; i < a->arity(); i++)
      {
        getBVOps<Op>(a->arg(i), ops);
      }
    }
    else
    {
      ops.push_back(a);
    }
  }

  inline static Expr extractVal(Expr a, Expr k)
  {
    if (!is_bvnum(k))
      return NULL;

    if (isOpX<CONST_ARRAY>(a))
    {
      return a->last();
    }
    else if (isOpX<STORE>(a))
    {
      if (!is_bvnum(a->right()))
        return NULL;
      if (!is_bvnum(a->last()))
        return NULL;
      if (a->right() == k)
        return a->last();
      return extractVal(a->left(), k);
    }
    return NULL;
  }

  inline static Expr evalSelect(Expr e)
  {
    if (isOpX<SELECT>(e))
      return extractVal(e->left(), e->right());
    return NULL;
  }

  inline static bool evalSelectEq(Expr e)
  {
    // sound only in returned true
    if (isOpX<EQ>(e))
    {
      Expr l = evalSelect(e->left());
      Expr r = evalSelect(e->right());
      if (l == NULL)
        l = e->left();
      if (r == NULL)
        r = e->right();
      return (l == r);
    }
    return false;
  }

  inline static Expr simpsext(Expr v, Expr ty)
  {
    if (isOpX<BSEXT>(v))
    {
      assert(width(v->last()) <= width(ty));
      return simpsext(v->left(), ty);
    }
    if (is_bvnum(v))
      return bvnum(v->left(), ty);
    return mk<BSEXT>(v, ty);
  }

  inline static Expr simpzext(Expr v, Expr ty)
  {
    if (isOpX<BZEXT>(v))
    {
      assert(width(v->last()) <= width(ty));
      return simpzext(v->left(), ty);
    }
    if (is_bvnum(v))
      return bvnum(v->left(), ty);
    return mk<BZEXT>(v, ty);
  }

  inline static void getBAddTerm(Expr a, ExprVector &ptrms, ExprVector &ntrms)
  {
    if (isOpX<BSEXT>(a))
    {
      Expr ty = a->last();
      ExprVector p, n;
      getBAddTerm(a->left(), p, n);
      for (auto &t : p)
        ptrms.push_back(simpsext(t, ty));
      for (auto &t : n)
        ntrms.push_back(simpsext(t, ty));
    }
    else if (isOpX<BADD>(a))
    {
      for (auto it = a->args_begin(); it != a->args_end(); ++it)
      {
        getBAddTerm(*it, ptrms, ntrms);
      }
    }
    else if (isOpX<BSUB>(a))
    {
      assert(a->arity() == 2);
      getBAddTerm(a->left(), ptrms, ntrms);
      getBAddTerm(a->right(), ntrms, ptrms);
    }
    else
    {
      ptrms.push_back(a);
    }
  }

  bool isZero(Expr t)
  {
    if (is_bvnum(t))
      if (lexical_cast<cpp_int>(t->left()) == 0)
        return true;
    if (isOpX<BMUL>(t))
    {
      ExprVector ops;
      getBVOps<BMUL>(t, ops);
      for (auto &a : ops)
        if (isZero(a))
          return true;
    }
    else if (isOpX<BEXTRACT>(t))
      return isZero(t->last());
    else if (isOpX<BSEXT>(t) || isOpX<BZEXT>(t))
      return isZero(t->left());
    return false;
  }

  bool isOne(Expr t)
  {
    if (is_bvnum(t))
      if (lexical_cast<cpp_int>(t->left()) == 1)
        return true;
    return false;
  }

  inline cpp_int filterVec(ExprVector &v)
  {
    cpp_int comm = 0;
    int sz = v.size();
    for (auto it = v.begin(); it != v.end();)
    {
      if (is_bvnum(*it))
      {
        comm += lexical_cast<cpp_int>((*it)->left());
        it = v.erase(it);
        continue;
      }
      else if (isZero(*it))
      {
        it = v.erase(it);
        continue;
      }
      ++it;
    }
    return comm;
  }

  inline static void simplifyBTerm(Expr a, ExprVector &ptrms,
                                   ExprVector &ntrms, cpp_int &comm)
  {
    getBAddTerm(a, ptrms, ntrms);
    comm += filterVec(ptrms);
    comm -= filterVec(ntrms);
  }

  template <typename OP>
  static Expr repairBComp(Expr l, Expr r)
  {
    auto &efac = l->getFactory();
    ExprVector ptrms, ntrms;
    cpp_int comm = 0;
    simplifyBTerm(r, ntrms, ptrms, comm);
    comm = -comm;
    simplifyBTerm(l, ptrms, ntrms, comm);

    for (auto it1 = ptrms.begin(); it1 != ptrms.end();)
    {
      bool toCont = false;
      for (auto it2 = ntrms.begin(); it2 != ntrms.end();)
      {
        if (*it1 == *it2)
        {
          it2 = ntrms.erase(it2);
          toCont = true;
          break;
        }
        else
          ++it2;
      }
      if (toCont)
      {
        it1 = ptrms.erase(it1);
        continue;
      }
      else
        ++it1;
    }

    Expr ty = typeOf(l);
    if (ptrms.empty() && ntrms.empty())
    {
      Expr tmp = mk<OP>(l, l);
      if (comm == 0)
      {
        if (isOpX<EQ>(tmp) || isOpX<BULE>(tmp) || isOpX<BUGE>(tmp) ||
            isOpX<BSLE>(tmp) || isOpX<BSGE>(tmp))
          return mk<TRUE>(efac);
        else
          return mk<FALSE>(efac);
      }
      if (isOpX<EQ>(tmp))
        return mk<FALSE>(efac);
    }

    if (comm > 0)
      ptrms.push_back(bvnum(mkMPZ(comm, efac), ty));
    if (comm < 0)
      ntrms.push_back(bvnum(mkMPZ(-comm, efac), ty));
    auto z = bvnum(mkMPZ(0, efac), ty);
    return mk<OP>(mkb<BADD>(ptrms, z), mkb<BADD>(ntrms, z));
  }

  inline static Expr repairBPrio(Expr e, Expr lhs)
  {
    auto &efac = e->getFactory();
    ExprVector ptrms, ntrms;
    cpp_int comm = 0;
    simplifyBTerm(e->right(), ntrms, ptrms, comm);
    comm = -comm;
    simplifyBTerm(e->left(), ptrms, ntrms, comm);

    Expr ty = typeOf(e->left());
    for (auto pit = ptrms.begin(); pit != ptrms.end();)
    {
      if (contains(*pit, lhs))
        pit++;
      else
      {
        ntrms.push_back(mk<BMUL>(bvnum(mkMPZ(-1, efac), ty), *pit));
        pit = ptrms.erase(pit);
      }
    }
    if (ptrms.size() != 1)
      return NULL;

    if (comm != 0)
      ntrms.push_back(bvnum(mkMPZ(-comm, efac), ty));
    auto z = bvnum(mkMPZ(0, efac), ty);
    return reBuildCmp(e, mkb<BADD>(ptrms, z), mkb<BADD>(ntrms, z));
  }

  inline static Expr additiveInverseBV(Expr e);
  inline static Expr rewriteMultAddBV(Expr exp);
  inline static void getMultOpsBV(Expr a, ExprVector &ops);

  void getAddTermBV(Expr a, ExprVector &terms) // implementation (mutually recursive)
  {
    if(is_bvnum(a))
    {
      terms.push_back(a);
    }
    else if(is_bvconst(a))
    {
      terms.push_back(a);
    }
    else if (isOpX<BADD>(a))
    {
      for (auto it = a->args_begin(), end = a->args_end(); it != end; ++it)
      {
        getAddTermBV(*it, terms);
      }
    }
    else if (isOpX<BSUB>(a))
    {
      auto it = a->args_begin();
      auto end = a->args_end();
      getAddTermBV(*it, terms);
      ++it;
      for (; it != end; ++it)
      {
        getAddTermBV(additiveInverseBV(*it), terms);
      }
    }
    // else if (isOpX<UN_MINUS>(a))
    // {
    //   ExprVector tmp;
    //   getAddTermBV(a->left(), tmp);
    //   for (auto &t : tmp)
    //   {
    //     bool toadd = true;
    //     for (auto it = terms.begin(); it != terms.end();)
    //     {
    //       if (*it == t)
    //       {
    //         terms.erase(it);
    //         toadd = false;
    //         break;
    //       }
    //       else
    //         ++it;
    //     }
    //     if (toadd)
    //       terms.push_back(additiveInverse(t));
    //   }
    // }
    else if (isOpX<BMUL>(a))
    {
      Expr tmp = rewriteMultAddBV(a);
      if (tmp == a)
        terms.push_back(a);
      else
        getAddTermBV(tmp, terms);
    }
    else if (lexical_cast<string>(a) != "0")
    {
      outs() << "In the lexical cast branch: " << a << "\n";
      bool found = false;
      for (auto it = terms.begin(); it != terms.end();)
      {
        if (additiveInverseBV(*it) == a)
        {
          terms.erase(it);
          found = true;
          break;
        }
        else
          ++it;
      }
      if (!found)
        terms.push_back(a);
    }
  }

  inline static bool getBVCombCoefs(Expr ex, set<cpp_int> &intCoefs)
  {
    bool res = true;
    if (isOpX<TRUE>(ex))
      return false;
    if (isOpX<OR>(ex))
    {
      for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it)
        res = res && getBVCombCoefs(*it, intCoefs);
    }
    else if (isBVComparison(ex)) // assuming the bv.combination is on the left side
    {
      if (!is_bvconst(ex->right()))
        return false;
      ExprVector addt;
      getAddTermBV(ex->left(), addt);
      for(auto &t: addt) outs() << "Term: " << t << "\n";
      for (auto &t : addt)
      {
        if(is_bvnum(t))
        {
          outs() << "Adding coefficient: " << t << "\n";
          intCoefs.insert(lexical_cast<cpp_int>(toMpz(t)));
        }
        else if (isOpX<BMUL>(t) && t->arity() == 2 &&
            is_bvnum(t->left()))
        {
          outs() << "Adding coefficient: " << t->left() << "\n";
          intCoefs.insert(lexical_cast<cpp_int>(toMpz(t->left())));
        }
        else if (isOpX<BMUL>(t) && t->arity() == 2 &&
                 is_bvnum(t->right()))
        {
          outs() << "Adding coefficient: " << t->right() << "\n";
          intCoefs.insert(lexical_cast<cpp_int>(toMpz(t->right())));
        }
        else
          return false;
      }
    }
    return res;
  }

  inline static Expr additiveInverseBV(Expr e)
  {
    if (isOpX<BMUL>(e))
    {
      cpp_int coef = 1;
      ExprVector ops;
      getMultOpsBV(e, ops);

      ExprVector rem;
      for (auto &a : ops)
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

      Expr num = mkMPZ(-coef, e->getFactory());
      if (rem.empty() || coef == 0)
        return num;

      Expr remTerm = bvmul(rem);
      if (coef == -1)
        return remTerm;

      return mk<BMUL>(num, remTerm);
    }
    else if (isOpX<BADD>(e))
    {
      ExprVector terms;
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it)
      {
        getAddTermBV(additiveInverseBV(*it), terms);
      }
      return bvadd(terms);
    }
    else if (isOpX<MINUS>(e))
    {
      ExprVector terms;
      getAddTerm(additiveInverseBV(*e->args_begin()), terms);
      auto it = e->args_begin() + 1;
      for (auto end = e->args_end(); it != end; ++it)
      {
        getAddTermBV(*it, terms);
      }
      return bvadd(terms);
    }
    else if (isOpX<UN_MINUS>(e))
    {
      return e->left();
    }
    else if (isOpX<MPZ>(e))
    {
      return mkMPZ(-lexical_cast<cpp_int>(e), e->getFactory());
    }
    else if (isOpX<MPQ>(e))
    {
      string val = lexical_cast<string>(e);
      int delim = val.find("/");
      int val1 = stoi(val.substr(0, delim));
      int val2 = stoi(val.substr(delim + 1));
      if (delim < 0)
      {
        return mkTerm(mpq_class(-val1), e->getFactory());
      }
      else
      {
        string inv_val = to_string(-val1) + "/" + to_string(val2);
        return mkTerm(mpq_class(inv_val), e->getFactory());
      }
    }
    else if (isOpX<ITE>(e))
    {
      return mk<ITE>(e->left(), additiveInverseBV(e->right()), additiveInverseBV(e->last()));
    }
    //    return mk<MULT>(mkMPZ ((-1), e->getFactory()), e);
    return mk<UN_MINUS>(e);
  }

  void getMultOpsBV(Expr a, ExprVector &ops)
  {
    if (isOpX<BMUL>(a))
    {
      for (unsigned i = 0; i < a->arity(); i++)
      {
        getMultOps(a->arg(i), ops);
      }
    }
    // else if (isOpX<UN_MINUS>(a) && is_bvnum(a->left()))
    // {
    //   ops.push_back(mkMPZ((-1), a->getFactory()));
    //   ops.push_back(a->left());
    // }
    else
    {
      ops.push_back(a);
    }
  }

  struct AddMultDistrBV
  {
    AddMultDistrBV() {};

    Expr operator()(Expr exp)
    {
      if (isOpX<BMUL>(exp) && exp->arity() == 2)
      {
        Expr lhs = exp->left();
        Expr rhs = exp->right();

        ExprVector alllhs;
        getAddTermBV(lhs, alllhs);

        ExprVector allrhs;
        getAddTermBV(rhs, allrhs);

        ExprVector unf;
        for (auto &a : alllhs)
        {
          for (auto &b : allrhs)
          {
            unf.push_back(mk<BMUL>(a, b));
          }
        }
        return bvadd(unf);
      }

      return exp;
    }
  };

  Expr rewriteMultAddBV(Expr exp)
  {
    RW<AddMultDistrBV> mu(new AddMultDistrBV());
    return dagVisit(mu, exp);
  }

  // template <typename Range>
  // static Expr bvmul(Range &terms, ExprFactory &efac)
  // {
  //   return 
  //     (terms.size() == 0) ? mkMPZ(1, efac) : 
  //     (terms.size() == 1) ? *terms.begin() : 
  //     mknary<BMUL>(terms);
  // }

  // template<typename Range> static Expr bvadd(Range& terms, ExprFactory &efac){
  //   return
  //     (terms.size() == 0) ? mkMPZ (0, efac) :
  //     (terms.size() == 1) ? *terms.begin() :
  //     mknary<BADD>(terms);
  // }

  Expr simpextract(Expr ty, int lo, Expr exp)
  {
    int w = width(ty);
    int w1 = width(typeOf(exp));
    assert(w1 + lo >= w);
    if (w1 == w && lo == 0)
      return exp;

    if (isOpX<BEXTRACT>(exp))
      return simpextract(ty, lo + low(exp), exp->last());

    if (isOpX<BSEXT>(exp) || isOpX<BZEXT>(exp))
    {
      if (width(typeOf(exp->left())) >= w + lo)
      {
        return simpextract(ty, lo, exp->left());
      }
    }

    if (isOpX<BCONCAT>(exp))
    {
      int w1 = width(typeOf(exp->right()));
      int w2 = width(typeOf(exp->left()));

      if (w + lo <= w1)
        return simpextract(ty, lo, exp->right());
      if (lo >= w1 && lo + w <= w1 + w2)
        return simpextract(ty, lo - w1, exp->left());
    }
    if (isOpX<BLSHR>(exp) && is_bvnum(exp->last()))
    {
      int w1 = width(typeOf(exp->left()));
      int sh = lexical_cast<int>(toMpz(exp->last()));
      if (w <= w1 - sh)
        return simpextract(ty, lo + sh, exp->left());
    }
    return bv::extract(lo + w - 1, lo, exp);
  }

  // struct SimplifyBVExpr
  // {
  //   SimplifyBVExpr() {};

  //   // just started here; to extend
  //   Expr operator()(Expr exp)
  //   {
  //     if (isOpX<EQ>(exp))
  //     {
  //       if (is_bvnum(exp->left()) && is_bvnum(exp->right()))
  //       {
  //         if (exp->left() == exp->right())
  //         {
  //           return mk<TRUE>(exp->getFactory());
  //         }
  //         else
  //         {
  //           return mk<FALSE>(exp->getFactory());
  //         }
  //       }
  //     }
  //     if (isOpX<NEQ>(exp))
  //     {
  //       if (is_bvnum(exp->left()) && is_bvnum(exp->right()))
  //       {
  //         if (exp->left() == exp->right())
  //         {
  //           return mk<FALSE>(exp->getFactory());
  //         }
  //         else
  //         {
  //           return mk<TRUE>(exp->getFactory());
  //         }
  //       }
  //     }
  //     if (isOpX<NEG>(exp))
  //     {
  //       return mkNeg(exp->left());
  //     }
  //     if (isOpX<EQ>(exp) || isOpX<NEQ>(exp) ||
  //         isOpX<BULT>(exp) || isOpX<BSLT>(exp) ||
  //         isOpX<BULE>(exp) || isOpX<BSLE>(exp) ||
  //         isOpX<BUGT>(exp) || isOpX<BSGT>(exp) ||
  //         isOpX<BUGE>(exp) || isOpX<BSGE>(exp))
  //     {
  //       Expr l = exp->left(), r = exp->right();
  //       if ((isOpX<BSEXT>(l) && isOpX<BSEXT>(r)) ||
  //           (isOpX<BZEXT>(l)) && isOpX<BZEXT>(r))
  //         if (width(typeOf(l->left())) ==
  //             width(typeOf(r->left())))
  //           return reBuildCmp(exp, l->left(), r->left());
  //     }
  //     if (!is_bvnum(exp) && isZero(exp))
  //     {
  //       return bvnum(mkMPZ(0, exp->getFactory()), typeOf(exp));
  //     }
  //     if (isOpX<BEXTRACT>(exp))
  //     {
  //       return simpextract(typeOf(exp), low(exp), exp->last());
  //     }
  //     else if (isOpX<BSEXT>(exp))
  //     {
  //       return simpsext(exp->left(), exp->last());
  //     }
  //     else if (isOpX<BZEXT>(exp))
  //     {
  //       return simpzext(exp->left(), exp->last());
  //     }
  //     if (isOpX<BADD>(exp) && exp->arity() == 2)
  //     {
  //       ExprVector terms;
  //       // to extend...
  //       for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it)
  //         if (!isZero(*it))
  //           terms.push_back(*it);
  //       auto z = bvnum(mkMPZ(0, exp->getFactory()), typeOf(exp));
  //       return mkb<BADD>(terms, z);
  //     }
  //     if (isOpX<BMUL>(exp) && exp->arity() == 2)
  //     {
  //       ExprVector terms;
  //       // to extend...
  //       for (auto it = exp->args_begin(), end = exp->args_end(); it != end; ++it)
  //         if (!isOne(*it))
  //           terms.push_back(*it);
  //       auto o = bvnum(mkMPZ(1, exp->getFactory()), typeOf(exp));
  //       return mkb<BMUL>(terms, o);
  //     }
  //     return exp;
  //   }
  // };

  // inline static Expr simplifyBV(Expr exp)
  // {
  //   RW<SimplifyBVExpr> rw(new SimplifyBVExpr());
  //   return dagVisit(rw, exp);
  // }

  template <typename OP>
  static Expr rep(Expr exp)
  {
    // `isOpX<OP>(exp)` should hold at most once,
    // so types and widths are computed at most once too
    if (isOpX<OP>(exp) && exp->arity() == 2)
    {
      Expr t1 = typeOf(exp->left());
      Expr t2 = typeOf(exp->right());
      if (isOpX<BVSORT>(t1) && isOpX<BVSORT>(t2))
      {
        int w1 = width(t1);
        int w2 = width(t2);
        if (w1 > w2)
          exp = mk<OP>(exp->left(), sext(exp->right(), w1));
        else if (w2 > w1)
          exp = mk<OP>(sext(exp->left(), w2), exp->right());
      }
    }
    return exp;
  }

  struct TypeRep
  {
    TypeRep() {}
    Expr operator()(Expr exp)
    {
      exp = rep<EQ>(exp);
      exp = rep<NEQ>(exp);
      exp = rep<BULT>(exp);
      exp = rep<BSLT>(exp);
      exp = rep<BULE>(exp);
      exp = rep<BSLE>(exp);
      exp = rep<BUGT>(exp);
      exp = rep<BSGT>(exp);
      exp = rep<BUGE>(exp);
      exp = rep<BSGE>(exp);
      exp = rep<BAND>(exp);
      exp = rep<BOR>(exp);
      exp = rep<BADD>(exp);
      exp = rep<BSUB>(exp);
      exp = rep<BMUL>(exp);
      exp = rep<BUDIV>(exp);
      exp = rep<BSDIV>(exp);
      exp = rep<BUREM>(exp);
      exp = rep<BSREM>(exp);

      if (isOpX<SELECT>(exp) && typeOf(exp->left())->left() != typeOf(exp->right()))
      {
        int w1 = width(typeOf(exp->left())->left());
        int w2 = width(typeOf(exp->right()));
        if (w1 > w2)
          exp = mk<SELECT>(exp->left(), sext(exp->right(), w1));
        else
          assert(0);
      }
      if (isOpX<STORE>(exp) && typeOf(exp->left())->left() != typeOf(exp->right()))
      {
        int w1 = width(typeOf(exp->left())->left());
        int w2 = width(typeOf(exp->right()));
        if (w1 > w2)
          exp = mk<STORE>(exp->left(), sext(exp->right(), w1), exp->last());
        else
          assert(0);
      }
      if (isOpX<STORE>(exp) && typeOf(exp->left())->right() != typeOf(exp->last()))
      {
        int w1 = width(typeOf(exp->left())->left());
        int w2 = width(typeOf(exp->last()));
        if (w1 > w2)
          exp = mk<STORE>(exp->left(), exp->right(), sext(exp->last(), w1));
        else
          assert(0);
      }
      return exp;
    }
  };

  inline static Expr typeRepair(Expr exp)
  {
    RW<TypeRep> rw(new TypeRep());
    return dagVisit(rw, exp);
  }

  // Add new helper method for normalizing BV expressions
  Expr normalizeBVExpr(Expr e)
  {
    if (isOp<BvOp>(e))
    {
      ExprVector args;
      for (auto it = e->args_begin(); it != e->args_end(); ++it)
      {
        args.push_back(normalizeBVExpr(*it));
      }

      // Convert n-ary operations to binary
      if (args.size() > 2)
      {
        if (isOpX<BADD>(e))
        {
          // Build chain of binary additions
          Expr result = args[0];
          for (size_t i = 1; i < args.size(); ++i)
          {
            result = mk<BADD>(result, args[i]);
          }
          return result;
        }
        else if (isOpX<BMUL>(e))
        {
          // Build chain of binary multiplications
          Expr result = args[0];
          for (size_t i = 1; i < args.size(); ++i)
          {
            result = mk<BMUL>(result, args[i]);
          }
          return result;
        }
      }

      // Handle each operation type explicitly
      if (isOpX<BADD>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BADD>(args[0], args[1]);
      }
      else if (isOpX<BMUL>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BMUL>(args[0], args[1]);
      }
      else if (isOpX<BSUB>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BSUB>(args[0], args[1]);
      }
      else if (isOpX<BUDIV>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BUDIV>(args[0], args[1]);
      }
      else if (isOpX<BSDIV>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BSDIV>(args[0], args[1]);
      }
      else if (isOpX<BUREM>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BUREM>(args[0], args[1]);
      }
      else if (isOpX<BSREM>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BSREM>(args[0], args[1]);
      }
      else if (isOpX<BSHL>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BSHL>(args[0], args[1]);
      }
      else if (isOpX<BLSHR>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BLSHR>(args[0], args[1]);
      }
      else if (isOpX<BASHR>(e))
      {
        if (args.size() == 1)
          return args[0];
        return mk<BASHR>(args[0], args[1]);
      }
      else if (isOpX<BNEG>(e))
      {
        return mk<BNEG>(args[0]);
      }
    }
    return e;
  }

  // revisit
  inline static Expr convertToBUGEandBUGT(Expr fla)
  {
    using namespace expr::op::bv;

    if (isOpX<NEG>(fla))
      return mkNeg(convertToBUGEandBUGT(fla->left()));

    // Convert signed comparisons to unsigned equivalents by swapping operands
    if (isOpX<BSLT>(fla))
      return mk<BUGT>(fla->right(), fla->left());
    if (isOpX<BSLE>(fla))
      return mk<BUGE>(fla->right(), fla->left());

    // Convert unsigned LT/LE to GT/GE by swapping operands
    if (isOpX<BULT>(fla))
      return mk<BUGT>(fla->right(), fla->left());
    if (isOpX<BULE>(fla))
      return mk<BUGE>(fla->right(), fla->left());

    if (isOpX<EQ>(fla))
    {
      Expr lhs = fla->left();
      Expr rhs = fla->right();

      // Check if both operands are bit vectors
      if (bv::is_bvnum(lhs) || bv::is_bvnum(rhs) ||
          (typeOf(lhs) && isOpX<BVSORT>(typeOf(lhs))))
      {
        // For bit vectors: x = y becomes (x >= y) && (y >= x)
        return mk<AND>(mk<BUGE>(lhs, rhs), mk<BUGE>(rhs, lhs));
      }
      else if (isBool(lhs))
      {
        // Boolean equality handling (same as original)
        return mk<OR>(mk<AND>(lhs, rhs),
                      mk<AND>(mkNeg(lhs), mkNeg(rhs)));
      }
      else
      {
        return fla;
      }
    }

    if (isOpX<NEQ>(fla))
    {
      Expr lhs = fla->left();
      Expr rhs = fla->right();

      if (bv::is_bvnum(lhs) || bv::is_bvnum(rhs) ||
          (typeOf(lhs) && isOpX<BVSORT>(typeOf(lhs))))
      {
        // For bit vectors: x != y becomes (x > y) || (y > x)
        return mk<OR>(mk<BUGT>(lhs, rhs), mk<BUGT>(rhs, lhs));
      }
      else if (isBool(lhs))
      {
        // Boolean inequality handling (same as original)
        return mk<OR>(mk<AND>(lhs, mkNeg(rhs)),
                      mk<AND>(mkNeg(lhs), rhs));
      }
      else
      {
        return fla;
      }
    }

    if (isOpX<AND>(fla) || isOpX<OR>(fla))
    {
      ExprSet args;
      for (int i = 0; i < fla->arity(); i++)
      {
        args.insert(convertToBUGEandBUGT(fla->arg(i)));
      }

      return isOpX<AND>(fla) ? conjoin(args, fla->getFactory()) : disjoin(args, fla->getFactory());
    }

    return fla;
  }

  // Helper function to check if expression contains bit vector operations
  inline static bool containsBVOps(Expr exp)
  {
    if (isOpX<BULT>(exp) || isOpX<BULE>(exp) || isOpX<BUGT>(exp) ||
        isOpX<BUGE>(exp) || isOpX<BSLT>(exp) || isOpX<BSLE>(exp) ||
        isOpX<BSGT>(exp) || isOpX<BSGE>(exp))
    {
      return true;
    }

    if (isOpX<EQ>(exp) || isOpX<NEQ>(exp))
    {
      Expr lhs = exp->left();
      return bv::is_bvnum(lhs) || (typeOf(lhs) && isOpX<BVSORT>(typeOf(lhs)));
    }

    for (int i = 0; i < exp->arity(); i++)
    {
      if (containsBVOps(exp->arg(i)))
        return true;
    }

    return false;
  }

  // BV unsigned version (analogous to LIA unsigned comparisons, but LIA doesn't distinguish, BV does)
  inline static Expr reBuildCmpBV(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(fla))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<BULE>(fla))
    {
      return mk<BULE>(lhs, rhs);
    }
    if (isOpX<BUGE>(fla))
    {
      return mk<BUGE>(lhs, rhs);
    }
    if (isOpX<BULT>(fla))
    {
      return mk<BULT>(lhs, rhs);
    }
    assert(isOpX<BUGT>(fla));
    return mk<BUGT>(lhs, rhs);
  }

  // BV unsigned version (analogous to LIA signed comparisons)
  inline static Expr reBuildCmpSymBV(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla))
    {
      return mk<EQ>(rhs, lhs);
    }
    if (isOpX<NEQ>(fla))
    {
      return mk<NEQ>(rhs, lhs);
    }
    if (isOpX<BULE>(fla))
    {
      return mk<BUGE>(rhs, lhs);
    }
    if (isOpX<BUGE>(fla))
    {
      return mk<BULE>(rhs, lhs);
    }
    if (isOpX<BULT>(fla))
    {
      return mk<BUGT>(rhs, lhs);
    }
    assert(isOpX<BUGT>(fla));
    return mk<BULT>(rhs, lhs);
  }

  // BV unsigned version (analogous to LIA signed comparisons)
  inline static Expr reBuildNegCmpBV(Expr fla, Expr lhs, Expr rhs)
  {
    if (isOpX<EQ>(fla))
    {
      return mk<NEQ>(lhs, rhs);
    }
    if (isOpX<NEQ>(fla))
    {
      return mk<EQ>(lhs, rhs);
    }
    if (isOpX<BULE>(fla))
    {
      return mk<BUGT>(lhs, rhs);
    }
    if (isOpX<BUGE>(fla))
    {
      return mk<BULT>(lhs, rhs);
    }
    if (isOpX<BULT>(fla))
    {
      return mk<BUGE>(lhs, rhs);
    }
    assert(isOpX<BUGT>(fla));
    return mk<BULE>(lhs, rhs);
  }

  

  // Add new helper class for BV printing
  class BVExprPrinter
  {
  private:
    SMTUtils &u;

  public:
    BVExprPrinter(SMTUtils &_u) : u(_u) {}

    void print(Expr e, std::ofstream &out)
    {
      static int depth = 0;
      auto printDebug = [&](const char* op) {
        if (u.debug >= 5) {
          // Use spaces instead of indent()
          for (int i = 0; i < depth * 2; ++i) outs() << " ";
          outs() << "BVPrinter: " << op << " expression: " << *e << "\n";
        }
      };

      if (!e) {
        printDebug("null");
        out << "true";
        return;
      }

      depth++;

      if (isOp<BADD>(e))
      {
        printDebug("BADD");
        out << "(bvadd ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BMUL>(e))
      {
        printDebug("BMUL"); 
        out << "(bvmul ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BSUB>(e))
      {
        out << "(bvsub ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BUDIV>(e))
      {
        out << "(bvudiv ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BSDIV>(e))
      {
        out << "(bvsdiv ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BUREM>(e))
      {
        out << "(bvurem ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BSREM>(e))
      {
        out << "(bvsrem ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BSHL>(e))
      {
        out << "(bvshl ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BLSHR>(e))
      {
        out << "(bvlshr ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BASHR>(e))
      {
        out << "(bvashr ";
        print(e->left(), out);
        out << " ";
        print(e->right(), out);
        out << ")";
      }
      else if (isOp<BNEG>(e))
      {
        out << "(bvneg ";
        print(e->left(), out);
        out << ")";
      }
      else if (isOpX<AND>(e))
      {
        if (e->arity() < 2) {
          // Handle empty AND or single argument
          if (e->arity() == 0) {
            out << "true";
          } else {
            print(e->arg(0), out);
          }
        } else {
          // Print AND with 2 or more arguments
          out << "(and";
          for (unsigned i = 0; i < e->arity(); i++) {
            out << " ";
            print(e->arg(i), out);
          }
          out << ")";
        }
      }
      else if (isOpX<OR>(e))
      {
        out << "(or";
        for (unsigned i = 0; i < e->arity(); i++) {
          out << " ";
          print(e->arg(i), out);
        }
        out << ")";
      }
      else
      {
        // For non-BV operations or leaf nodes, use standard printing
        printDebug("default");
        u.print(e, out);
      }

      depth--;
    }
  };

  // Helper to normalize AND expressions
  inline Expr normalizeAND(Expr e) {
    if (!isOpX<AND>(e)) return e;
    
    if (e->arity() == 0) return mk<TRUE>(e->getFactory());
    if (e->arity() == 1) return e->arg(0);
    
    return e;
  }
}

#endif