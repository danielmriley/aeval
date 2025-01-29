// Included in SimplificationPasses.hpp
#ifndef LIATOBV_HPP
#define LIATOBV_HPP

#include "deep/Horn.hpp"
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"

namespace ufo
{
  namespace passes
  {

    unsigned int binaryLog(mpz_class v)
    {
      if(v < 0)
      {
        v *= -1;
      }
      if (v.fits_ulong_p())
      {
        unsigned long v_ul = v.get_ui();
        unsigned int res = 1;
        while (v_ul >>= 1)
        {
          ++res;
        }
        return res;
      }
      // TODO: implement this
      throw std::logic_error("Not implemented yet!");
    }

    class LIA2BVPass
    {

      private:
      std::map<Expr, Expr> variableMap;
      std::map<Expr, Expr> declsMap;
      std::map<Expr, Expr> constMap;

      std::unique_ptr<CHCs> transformed;
      CHCs& liaSystem;

      int bitwidth = 0;
      int debug = 0;

      public:
      LIA2BVPass(CHCs& _r, int _debug = 0) : liaSystem(_r), debug(_debug) {}

      CHCs *getTransformed() { return transformed.get(); }

      void operator()(const CHCs &system)
      {
        transformed.reset(new CHCs{system.m_efac, system.m_z3});
        CHCs &bvSystem = *transformed;
        findBitWitdth(system.chcs);
        bvSystem.failDecl = system.failDecl;
        // Translate the vars and find the upper bound for the var bitwidth.
        for (auto &v : system.invVars)
        {
          if (v.first == mk<TRUE>(v.first->getFactory())) continue;

        }
        if (debug >= 3) outs() << "Translating invVars.\n";
        for (auto &d : system.decls)
        {
          if (d == mk<TRUE>(d->getFactory())) continue;
          if (debug >= 4) outs() << "Decl: " << *d << "\n";

          bvSystem.invVars[d->left()] = translateInvVars(system.invVars.at(d->left()), true);
          bvSystem.invVarsPrime[d->left()] = translateInvVars(system.invVarsPrime.at(d->left()), true);
        }
        // Translate the clauses and find the upper bound for the bitwidth.
        bvSystem.chcs = translateClauses(system.chcs);
        // // Now translate the decls.
        bvSystem.decls = translateDeclarations(system.decls);
      }

      ExprSet translateDeclarations(const ExprSet &originals)
      {
        ExprSet ret;
        for (const auto &decl : originals)
        {
          assert(bind::isFdecl(decl));
          ExprVector types;
          for (int i = 1; i < decl->arity(); ++i)
          {
            Expr arg = decl->arg(i);
            Expr type = isOpX<INT_TY>(arg) ? bv::bvsort(bitwidth, arg->getFactory()) : arg;
            types.push_back(type);
          }
          Expr name = bind::fname(decl);
          Expr translated = bind::fdecl(name, types);
          declsMap[decl] = translated;
          ret.insert(translated);
          if (debug >= 4)
            outs() << "Translated " << *decl << " to " << *translated << "\n";
        }

        return ret;
      }

      void translateConsts(Expr e)
      {
        ExprSet conjs;
        getConj(e, conjs);
        for (auto &c : conjs)
        {
          if(debug >= 3)
          {
            outs() << "Consts translation expr: " << c << "\n";
          }

          if (isOpX<MPZ>(c))
          {
            if (debug >= 4)
              outs() << "Constant: " << c << "\n";
            // constMap[c] = bv::bvConst(c, bitwidth);
            constMap[c] = bv::bvnum(getTerm<mpz_class>(c), bitwidth, c->getFactory());
          }

          for(auto arg = c->args_begin(); arg != c->args_end(); ++arg)
          {
            translateConsts(*arg);
          }
          // Expr lhs = c->left();
          // Expr rhs = c->right();
          // if (lhs != NULL) translateConsts(lhs);
          // if (rhs != NULL) translateConsts(rhs);
        }
      }

      int computeExpressionBitWidth(Expr e)
      {
        int maxBitWidth = 0;
        ExprSet conjs;
        getConj(e, conjs);
        for (auto &c : conjs)
        {
          if (debug >= 4)
          {
            outs() << "Expr: " << c << "\n";
          }
          if (isOpX<MPZ>(c))
          {
            mpz_class val = getTerm<mpz_class>(c);
            int bw = binaryLog(val);
            if (debug >= 4)
            {
              outs() << "BW: " << bw << "\n";
            }
            if (bw > maxBitWidth)
            {
              maxBitWidth = bw;
            }
          }

          Expr lhs = c->left();
          Expr rhs = c->right();
          int lhsbw, rhsbw;
          if (lhs != NULL)
          {
            lhsbw = computeExpressionBitWidth(lhs);
            if (lhsbw > maxBitWidth)
              maxBitWidth = lhsbw;
          }
          if (rhs != NULL)
          {
            rhsbw = computeExpressionBitWidth(rhs);
            if (rhsbw > maxBitWidth)
              maxBitWidth = rhsbw;
          }
        }
        return maxBitWidth;
      }

      void findBitWitdth(const std::vector<HornRuleExt> &origClauses)
      {
        // Find the largest constant in the body of the clauses.
        for (const auto &clause : origClauses)
        {
          Expr body = clause.body;
          int bw = computeExpressionBitWidth(body);
          if (bw > bitwidth) bitwidth = bw;
        }
        if (debug >= 3)
        {
          outs() << "Max bit width found: " << bitwidth << "\n";
        } 
      }

      std::vector<HornRuleExt> translateClauses(const std::vector<HornRuleExt> &origClauses)
      {

        // Now, translate the constants and put them in a map for later.
        for (const auto &clause : origClauses)
        {
          translateConsts(clause.body);
        }

        if (debug >= 3)
        {
          outs() << "Constants translation:\n";
          for (auto const &entry : constMap)
          {
            outs() << *entry.first << " -> " << *entry.second << "\n";
          }
        }

        std::vector<HornRuleExt> translatedClauses;
        for (const auto &clause : origClauses)
        {
          translatedClauses.emplace_back();
          HornRuleExt &translated = translatedClauses.back();
          translated.isQuery = clause.isQuery;
          translated.isFact = clause.isFact;
          translated.isInductive = clause.isInductive;

          // Translate the variables.
          translated.srcVars = translateInvVars(clause.srcVars);
          translated.dstVars = translateInvVars(clause.dstVars);
          translated.locVars = translateInvVars(clause.locVars, true);
          
          if(debug >= 3)
          {
            outs() << "var mapping:\n";
            for(auto const &entry: variableMap)
            {
              outs() << *entry.first << " -> " << *entry.second << "\n";
            }
          }

          // // Translate the body.
          translated.body = translateRecursively(clause.body);
          if(debug >= 4) outs() << "Translated body: " << *translated.body << "\n";
          // Create new src and dst relations with bv type.
          translated.dstRelation = clause.dstRelation;
          translated.srcRelation = clause.srcRelation;
        }

        if(debug >= 3)
        {
          outs() << "Translated clauses:\n";
        }

        return translatedClauses;
      }

      Expr translateRecursively(Expr exp)
      {
        if (debug >= 3) outs() << "Translating: " << *exp << "\n";

        auto isConstant = bind::IsHardIntConst{};
        if(isConstant(exp)) {
          outs() << "Finding const" << std::endl;
          return constMap.at(exp);
        }
        if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<IFF>(exp))
        {
          ExprVector n_args;
          for (auto it = exp->args_begin(); it != exp->args_end(); ++it)
          {
            n_args.push_back(translateRecursively(*it));
          }
          return isOpX<AND>(exp) ? conjoin(n_args, exp->getFactory()) : disjoin(n_args, exp->getFactory());
        }
        if (isOpX<NEG>(exp))
        {
          return mkNeg(translateRecursively(exp->first()));
        }
        if (isOp<ComparissonOp>(exp) || isOp<NumericOp>(exp))
        {
          auto isConstant = bind::IsHardIntConst{};
          // The meat of the translation from BV to LIA.
          ExprVector n_args;
          for(auto it = exp->args_begin(); it != exp->args_end(); ++it) {
            Expr arg = *it;
            outs() << "arg: " << *arg << "\n";
            if(isConstant(arg)) {
              outs() << "adding const to n_args " << arg << "\n";
              n_args.push_back(constMap.at(arg));
            }
            else if(isOpX<UN_MINUS>(arg))
            {
              outs() << "arg->first(): " << *arg->first() << "\n";
              Expr negOne = bv::bvnum(-1, bitwidth, exp->getFactory());
              n_args.push_back(mk<BMUL>(negOne, translateRecursively(arg->first())));
            } 
            else {
              n_args.push_back(translateRecursively(arg));
            }
          }
          if (isOpX<MULT>(exp) && exp->arity() == 2)
          {
            Expr left = exp->left();
            Expr right = exp->right();
            auto isMinusOne = [](Expr e) -> bool
            { return bind::IsHardIntConst{}(e) && getTerm<mpz_class>(e) == -1; };
            if (isMinusOne(left))
            {
              return bv::bvneg(translateRecursively(right));
            }
            if (isMinusOne(right))
            {
              return bv::bvneg(translateRecursively(left));
            }
          }

          Expr res = translateOperation(exp, n_args);
          return res;
        }
        if (bind::isBoolConst(exp))
        {
          return exp;
        }
        if (isOpX<ITE>(exp))
        {
          Expr cond = translateRecursively(exp->arg(0));
          Expr then = translateRecursively(exp->arg(1));
          Expr els = translateRecursively(exp->arg(2));
          return mk<ITE>(cond, then, els);
        }

        Expr bvVar = variableMap[exp];
        if(bvVar != NULL) {
          return bvVar;
        }

        std::cerr << "Unhandled case when translating LIA invariant to BV: " << *exp << std::endl;
        assert(false);
      }

      Expr translateExpr(Expr e)
      {
        return translateRecursively(e);
      }

      Expr translateOperation(Expr e, ExprVector n_args)
      {
        if (n_args.size() > 2)
        {
          ExprVector nn_args(n_args.begin() + 1, n_args.end());
          Expr subExpression = translateOperation(e, nn_args);
          n_args.erase(n_args.begin() + 1, n_args.end());
          n_args.push_back(subExpression);
        }
        if (isOpX<EQ>(e))
        {
          return mknary<EQ>(n_args);
        }

        if (isOpX<NEQ>(e))
        {
          return mknary<NEQ>(n_args);
        }

        // MB: This transformation is meant for translating candidate invariants, that's why we translate with AND: to get both candidates
        if (isOpX<LEQ>(e))
        {
          return mknary<BULE>(n_args);
        }

        if (isOpX<GEQ>(e))
        {
          return mknary<BUGE>(n_args);
        }

        if (isOpX<LT>(e))
        {
          return mknary<BULT>(n_args);
        }

        if (isOpX<GT>(e))
        {
          return mknary<BUGT>(n_args);
        }

        if (isOpX<PLUS>(e))
        {
          return mknary<BADD>(n_args);
        }

        if (isOpX<MINUS>(e))
        {
          return mknary<BSUB>(n_args);
        }

        if (isOpX<MULT>(e))
        {
          return mknary<BMUL>(n_args);
        }

        if (isOpX<IDIV>(e))
        {
          return mknary<BUDIV>(n_args);
        }

        if(isOpX<MOD>(e))
        {
          return mknary<BUREM>(n_args);
        }

        std::cerr << "Case not covered when translating operation from LIA to BV " << *e << std::endl;
        assert(false);
        throw std::logic_error("Case not covered when translating operation from LIA to BV");
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool isInvVars = false)
      {
        // Translate from INT to BV vars.
        ExprVector translatedVars;
        for (const auto &var : origVars)
        {
          if (debug >= 3)
          {
            outs() << "Var: " << *var << "\n";
            outs() << "Var type: " << *var->left() << "\n";
            outs() << "var->left()->left(): " << *var->left()->left() << "\n";
          }
          // translate INT var to BV var.
          Expr bvVar = bv::bvConst(var, bitwidth);
          if (debug >= 3)
          {
            outs() << "BV var: " << *bvVar << "\n";
            outs() << "BV var type: " << *bvVar->left() << "\n";
          }
          translatedVars.push_back(bvVar);
          if (isInvVars)
            variableMap[var] = bvVar;
        }
        return translatedVars;
      }
    };
  }
}

#endif