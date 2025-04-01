#ifndef LIA2BV__HPP__
#define LIA2BV__HPP__

#include "deep/Horn.hpp"

using namespace std;

namespace ufo
{
  class Lia2BvTranslator 
  {
    private:
      ExprFactory &m_efac;
      EZ3 &m_z3;
      unsigned int m_width;
      
      // Maps for tracking translations
      std::map<Expr, Expr> m_var_map;      // Maps LIA vars to BV vars  
      std::map<Expr, Expr> m_decl_map;     // Maps LIA decls to BV decls
      
      // Translation helpers
      Expr translateVar(Expr var)
      {
        // Replace init-statement in if with traditional lookup
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
          return it->second;

        // Only translate integer variables
        if (!isOpX<INT_TY>(bind::typeOf(var))) 
          return var;

        // Create new BV variable with same name but BV sort
        Expr name = bind::name(var); 
        Expr sort = bv::bvsort(m_width, m_efac);
        Expr newVar = bind::mkConst(name, sort);
        
        m_var_map[var] = newVar;
        return newVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        
        for (const auto &var : origVars) 
        {
          // Skip if not an integer variable
          if (!isOpX<INT_TY>(bind::typeOf(var)))
          {
            translatedVars.push_back(var);
            continue;
          }

          // Create new BV variable
          Expr bvVar = bv::bvConst(var, m_width);
          outs() << "bvVar: " << bvVar << "\n";
          translatedVars.push_back(bvVar);
          
          // Cache the translation if requested
          if (cacheVars)
            m_var_map[var] = bvVar;
        }
        return translatedVars;
      }

    public:
      Lia2BvTranslator(ExprFactory &efac, EZ3 &z3, unsigned width = 4) : 
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

    private:
      ExprSet translateDeclarations(const ExprSet &decls)
      {
        ExprSet result;
        for (Expr decl : decls)
        {
          if (decl == NULL) continue;
          
          // Create new type list with BV sorts instead of INT
          ExprVector sorts;
          for (unsigned i = 1; i < decl->arity()-1; i++)
          {
            Expr sort = decl->arg(i);
            if (isOpX<INT_TY>(sort))
              sorts.push_back(bv::bvsort(m_width, m_efac));
            else
              sorts.push_back(sort);
          }
          sorts.push_back(mk<BOOL_TY>(m_efac)); // Return type
          
          // Create new declaration
          Expr newDecl = bind::fdecl(decl->arg(0), sorts);
          m_decl_map[decl] = newDecl;
          result.insert(newDecl);
        }
        return result;
      }

      void translateVariableMaps(const CHCs &input, CHCs &output)
      {
        // Translate regular variables using translateInvVars
        for (const auto &kv : input.invVars)
        {
          output.invVars[kv.first] = translateInvVars(kv.second, true);
        }

        // Translate prime variables using translateInvVars
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
          
          // Translate source/destination relations
          if (m_decl_map.count(rule.srcRelation))
            newRule.srcRelation = m_decl_map[rule.srcRelation];
          if (m_decl_map.count(rule.dstRelation))  
            newRule.dstRelation = m_decl_map[rule.dstRelation];

          // Translate variables
          translateRuleVariables(newRule);

          // Translate body constraints and fix formatting
          newRule.body = fixFormatting(translateExpr(rule.body));
          
          result.push_back(newRule);
        }
        return result;
      }

      void translateRuleVariables(HornRuleExt &rule)
      {
        // Translate source, destination and local variables using translateInvVars
        rule.srcVars = translateInvVars(rule.srcVars);
        rule.dstVars = translateInvVars(rule.dstVars);  
        rule.locVars = translateInvVars(rule.locVars);
      }

      Expr translateExpr(Expr e)
      {
        if (!e) return e;

        // Handle variables
        if (bind::IsConst()(e))
          return translateVar(e);

        // Handle integer literals 
        if (isOpX<MPZ>(e))
        {
          mpz_class val = getTerm<mpz_class>(e);
          return bv::bvnum(val, m_width, m_efac);
        }

        // Handle operations
        if (isOpX<PLUS>(e))
          return bv::bvadd(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<MINUS>(e))
          return mk<BSUB>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<MULT>(e))
          return mk<BMUL>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<DIV>(e))
          return mk<BSDIV>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<MOD>(e))
          return mk<BSREM>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<UN_MINUS>(e))
          return bv::bvneg(translateExpr(e->left()));
        else if (isOpX<LEQ>(e))
          return bv::bvsle(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<LT>(e))
          return bv::bvslt(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<GEQ>(e))
          return bv::bvsge(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<GT>(e))
          return bv::bvsgt(translateExpr(e->left()), translateExpr(e->right()));
          
        // Keep boolean operations untranslated
        else if (isOp<BoolOp>(e))
        {
          ExprVector args;
          for (unsigned i = 0; i < e->arity(); i++)
            args.push_back(translateExpr(e->arg(i)));
          return e->efac().mkNary(e->op(), args);
        }

        // Any other operation - recursively translate args
        ExprVector args;
        for (unsigned i = 0; i < e->arity(); i++)
          args.push_back(translateExpr(e->arg(i)));
        return e->efac().mkNary(e->op(), args);
      }

      Expr fixFormatting(Expr e)
      {
        // Fix rules that end with NULL
        if (e == NULL) 
        {
          return mk<FALSE>(m_efac);
        }

        // Fix rule formatting
        ExprVector args;
        for (unsigned i = 0; i < e->arity(); i++)
        {
          args.push_back(fixFormatting(e->arg(i)));
        }

        if (args.empty()) return e;
        return e->efac().mkNary(e->op(), args);
      }
  };
}

#endif
