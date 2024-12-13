// Convert from BV to LIA and from LIA to BV.

#ifndef EXPRCONVERSION_HPP
#define EXPRCONVERSION_HPP

#include "deep/Horn.hpp"
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"

namespace ufo
{
  struct ITESimplificationPass
  {
    void operator()(CHCs &in)
    {
      SMTUtils smtutils(in.m_efac);
      ITEVisitor v(smtutils);
      for (auto &chc : in.chcs)
      {
        chc.body = dagVisit(v, chc.body);
      }
    }

    struct ITEVisitor
    {
      SMTUtils &smtutils;

      ITEVisitor(SMTUtils &smtutils) : smtutils{smtutils} {}

      VisitAction operator()(Expr e)
      {
        if (isOpX<ITE>(e))
        {
          ExprVector pos;
          ExprVector neg;
          Expr res = simplifyITE(e, pos, neg);
          return VisitAction::changeTo(res);
        }
        return VisitAction::doKids();
      }

      Expr simplifyITE(Expr ex, ExprVector &trueConditions, ExprVector &falseConditions)
      {
        if (bv::is_bvnum(ex) || bv::is_bvconst(ex))
        {
          return ex;
        }
        //          std::cout << *ex << std::endl;
        auto &fact = ex->getFactory();
        ExprVector substituteWhat;
        ExprVector substituteWith;
        for (Expr e : trueConditions)
        {
          substituteWhat.push_back(e);
          substituteWith.push_back(mk<TRUE>(ex->getFactory()));
        }
        for (Expr e : falseConditions)
        {
          substituteWhat.push_back(e);
          substituteWith.push_back(mk<FALSE>(ex->getFactory()));
        }
        ex = replaceAll(ex, substituteWhat, substituteWith);

        if (isOpX<ITE>(ex))
        {

          Expr cond = simplifyITE(ex->arg(0), trueConditions, falseConditions);
          Expr br1 = ex->arg(1);
          Expr br2 = ex->arg(2);

          Expr ret;
          Expr upLevelCond = conjoin(trueConditions, fact);
          if (!smtutils.isSat(cond, upLevelCond))
          {
            falseConditions.push_back(cond);
            trueConditions.push_back(mkNeg(cond));
            Expr res = simplifyITE(br2, trueConditions, falseConditions);
            falseConditions.pop_back();
            trueConditions.pop_back();
            return res;
          }
          if (!smtutils.isSat(mk<NEG>(cond), upLevelCond))
          {
            trueConditions.push_back(cond);
            falseConditions.push_back(mkNeg(cond));
            Expr res = simplifyITE(br1, trueConditions, falseConditions);
            trueConditions.pop_back();
            falseConditions.pop_back();
            return res;
          }
          trueConditions.push_back(cond);
          falseConditions.push_back(mkNeg(cond));
          Expr n_then = simplifyITE(br1, trueConditions, falseConditions);
          trueConditions.pop_back();
          falseConditions.pop_back();
          falseConditions.push_back(cond);
          trueConditions.push_back(mkNeg(cond));
          Expr n_else = simplifyITE(br2, trueConditions, falseConditions);
          falseConditions.pop_back();
          trueConditions.pop_back();
          return mk<ITE>(cond, n_then, n_else);
        }

        else
        {
          if (ex->arity() == 0)
          {
            return ex;
          }
          ExprVector kids;
          std::transform(ex->args_begin(), ex->args_end(), std::back_inserter(kids),
                         [this, &trueConditions, &falseConditions](Expr e)
                         {
                           return this->simplifyITE(e, trueConditions, falseConditions);
                         });
          Expr res = ex->getFactory().mkNary(ex->op(), kids);
          return res;
        }
      }
    };
  };

  
}

#endif