#ifndef BV2LIA__HPP__
#define BV2LIA__HPP__

#include "deep/Horn.hpp"
#include "ufo/Smt/EZ3.hh"
#include "ufo/ExprBv.hh"

namespace ufo
{
  class Bv2LiaTranslator 
  {
    private:
      ExprFactory &m_efac;
      EZ3 &m_z3;
      unsigned int m_width;
      
      // Maps for tracking translations
      std::map<Expr, Expr> m_var_map;      // Maps BV vars to LIA vars  
      std::map<Expr, Expr> m_decl_map;     // Maps BV decls to LIA decls
      
      // Translation helpers
      Expr translateVar(Expr var)
      {
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
          return it->second;

        if (!bv::is_bvvar(var)) 
          return var;

        Expr name = bind::name(var);
        Expr sort = mk<INT_TY>(m_efac);
        Expr newVar = bind::mkConst(name, sort);
        
        m_var_map[var] = newVar;
        return newVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        
        for (const auto &var : origVars)
        {
          if (!bv::is_bvvar(var))
          {
            translatedVars.push_back(var);
            continue;
          }

          // Create new integer variable using bind::mkConst instead of bind::intVar
          Expr name = bind::name(var);
          Expr sort = mk<INT_TY>(m_efac);
          Expr liaVar = bind::mkConst(name, sort);
          
          translatedVars.push_back(liaVar);
          
          if (cacheVars)
            m_var_map[var] = liaVar;
        }
        return translatedVars;
      }

    public:
      Bv2LiaTranslator(ExprFactory &efac, EZ3 &z3, unsigned width = 32) : 
        m_efac(efac), m_z3(z3), m_width(width) {}

      CHCs translate(CHCs &input)
      {
        CHCs result(m_efac, m_z3);
        
        // 1. Translate declarations and create new variables
        result.decls = translateDeclarations(input.decls);

        // 2. Create new variable maps
        translateVariableMaps(input, result);

        // 3. Translate CHC rules
        result.chcs = translateClauses(input.chcs);

        return result;
      }

      // Add public method to translate individual expressions
      Expr translateExpr(Expr e) 
      {
        // Ensure maps are initialized
        if (m_var_map.empty() && m_decl_map.empty())
        {
          // Create temporary maps if needed
          return translateExprHelper(e);
        }
        return translateExprHelper(e);
      }

    private:
      ExprSet translateDeclarations(const ExprSet &decls)
      {
        ExprSet result;
        for (Expr decl : decls)
        {
          if (decl == NULL) continue;
          
          ExprVector sorts;
          for (unsigned i = 1; i < decl->arity()-1; i++)
          {
            Expr sort = decl->arg(i);
            // Fix: Use isOpX<BVSORT> instead of bv::is_bvsort
            if (isOpX<BVSORT>(sort))
              sorts.push_back(mk<INT_TY>(m_efac));
            else
              sorts.push_back(sort);
          }
          sorts.push_back(mk<BOOL_TY>(m_efac));
          
          Expr newDecl = bind::fdecl(decl->arg(0), sorts);
          m_decl_map[decl] = newDecl;
          result.insert(newDecl);
        }
        return result;
      }

      void translateVariableMaps(const CHCs &input, CHCs &output)
      {
        for (const auto &kv : input.invVars)
        {
          output.invVars[kv.first] = translateInvVars(kv.second, true);
        }

        for (const auto &kv : input.invVarsPrime) 
        {
          output.invVarsPrime[kv.first] = translateInvVars(kv.second, true);
        }
      }

      std::vector<HornRuleExt> translateClauses(const std::vector<HornRuleExt> &rules)
      {
        std::vector<HornRuleExt> result;
        for (const auto &rule : rules)
        {
          HornRuleExt newRule = rule;
          
          if (m_decl_map.count(rule.srcRelation))
            newRule.srcRelation = m_decl_map[rule.srcRelation];
          if (m_decl_map.count(rule.dstRelation))  
            newRule.dstRelation = m_decl_map[rule.dstRelation];

          translateRuleVariables(newRule);
          newRule.body = translateExpr(rule.body);
          
          result.push_back(newRule);
        }
        return result;
      }

      void translateRuleVariables(HornRuleExt &rule)
      {
        rule.srcVars = translateInvVars(rule.srcVars);
        rule.dstVars = translateInvVars(rule.dstVars);
        rule.locVars = translateInvVars(rule.locVars);
      }

      // Rename existing translateExpr to translateExprHelper
      Expr translateExprHelper(Expr e)
      {
        if (!e) return e;

        // Handle variables/constants 
        if (bind::IsConst()(e))
          return translateVar(e);
        
        if (bv::is_bvnum(e))
          return mkTerm(bv::toMpz(e), m_efac);

        // Handle application expressions
        if (isOpX<FAPP>(e))
        {
          ExprVector args;
          // Keep original relation name
          args.push_back(e->arg(0));
          // Translate arguments
          for (unsigned i = 1; i < e->arity(); ++i)
            args.push_back(translateExpr(e->arg(i)));
          return mknary<FAPP>(args);
        }

        // Basic logical operators
        if (isOpX<AND>(e))
        {
          ExprVector args;
          for (unsigned i = 0; i < e->arity(); ++i)
            args.push_back(translateExpr(e->arg(i)));
          return mknary<AND>(args);
        }
        
        // Handle inequality expressions explicitly
        if (isOpX<NEQ>(e))
          return mk<NEQ>(translateExpr(e->left()), translateExpr(e->right()));

        // Handle implications 
        if (isOpX<IMPL>(e))
          return mk<IMPL>(translateExpr(e->left()), translateExpr(e->right()));
        
        // Rest remains the same

        // Boolean operations
        if (isOpX<BAND>(e))
          return mk<AND>(translateExpr(e->left()), translateExpr(e->right())); 
        else if (isOpX<BOR>(e))
          return mk<OR>(translateExpr(e->left()), translateExpr(e->right()));
        
        // Arithmetic operations  
        else if (isOpX<BADD>(e))
          return mk<PLUS>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BSUB>(e))
          return mk<MINUS>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BMUL>(e))
          return mk<MULT>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BUDIV>(e)) 
          return mk<IDIV>(translateExpr(e->left()), translateExpr(e->right())); 
        else if (isOpX<BSDIV>(e))
          return mk<DIV>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BUREM>(e))
          return mk<REM>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BSREM>(e)) 
          return mk<MOD>(translateExpr(e->left()), translateExpr(e->right()));
        
        // Comparisons - note both signed/unsigned translate to same LIA ops
        else if (isOpX<BULE>(e) || isOpX<BSLE>(e))
          return mk<LEQ>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BUGE>(e) || isOpX<BSGE>(e))
          return mk<GEQ>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BULT>(e) || isOpX<BSLT>(e))
          return mk<LT>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<BUGT>(e) || isOpX<BSGT>(e)) 
          return mk<GT>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<EQ>(e))
          return mk<EQ>(translateExpr(e->left()), translateExpr(e->right()));
        
        // Special bitvector operations
        else if (isOpX<BNEG>(e))
          return mk<UN_MINUS>(translateExpr(e->left()));

        // Use ExprVector for n-ary operators and recursive translation
        ExprVector newArgs;
        for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it)
          newArgs.push_back(translateExpr(*it));
        
        // Preserve original operator for unhandled cases
        return mknary<FAPP>(newArgs);
      }
  };
} // namespace ufo

#endif
