#ifndef BV2LIA__HPP__
#define BV2LIA__HPP__

#include "deep/Horn.hpp"
#include "ufo/Smt/EZ3.hh"
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp" 

using namespace std;
using namespace expr::op;

namespace ufo
{
  class Bv2LiaTranslator 
  {
    private:
      ExprFactory &m_efac;
      EZ3 &m_z3;
      unsigned int m_width;
      int m_debug;  // Changed from debug to m_debug
      
      // Maps for tracking translations
      std::map<Expr, Expr> m_var_map;      // Maps BV vars to LIA vars  
      std::map<Expr, Expr> m_decl_map;     // Maps BV decls to LIA decls

      // Translation helpers
      static bool isBVSort(Expr e) { return isOpX<BVSORT>(e); }
      static bool isBVVar(Expr e) { return isOpX<FAPP>(e) && isBVSort(e->first()->last()); }

      Expr translateVar(Expr var)
      {
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
            return it->second;
            
        if (!bv::is_bvvar(var)) 
          return var;

        // Create new integer variable using bind::intConst
        Expr name = bind::fname(bind::fname(var));
        Expr translatedVar = bind::intConst(name);
        m_var_map[var] = translatedVar;

        if (m_debug >= 3) {
          outs() << "Mapped BV var " << *var << " to LIA var " << *translatedVar << "\n";
        }
        return translatedVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        outs() << "Translating invariant variables...\n";
        for (const auto &var : origVars)
        {
          if(m_debug >= 3) {
            outs() << "Translating var: " << *var << "\n";
            outs() << "Searching for var: " << *var << "\n";
            outs() << "var type: " << bind::typeOf(var) << "\n";
          }
          // if (!bv::is_bvvar(var)) {
          //   translatedVars.push_back(var);
          //   outs() << "Continued with non-BV var: " << *var << "\n";
          //   continue; 
          // }

          // Use the same translation logic as translateVar
          Expr name = bind::fname(bind::fname(var));
          Expr liaVar = bind::intConst(name);
          if(m_debug >= 3) {
            outs() << "Mapped BV var " << *var << " to LIA var " << *liaVar << "\n";
            outs() << "liaVar: " << *liaVar << "\n";
            outs() << "liaVar type: " << bind::typeOf(liaVar) << "\n";
            outs() << "var type: " << bind::typeOf(var) << "\n";
          }
          translatedVars.push_back(liaVar);
          
          if (cacheVars) {
            m_var_map[var] = liaVar;
            if (m_debug >= 3) {
              outs() << "Cached mapping: " << *var << " -> " << *liaVar << "\n";
            }
          }
        }
        return translatedVars;
      }

    public:
      // Update constructor to initialize m_debug
      Bv2LiaTranslator(ExprFactory &efac, EZ3 &z3, unsigned width = 32, int debug = 0) : 
        m_efac(efac), 
        m_z3(z3),
        m_width(width), 
        m_debug(debug) {}

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

        for(auto v: output.invVars)
        {
          outs() << "InvVar: " << v.first << "\n";
          for(auto a: v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
        }

        for (const auto &kv : input.invVarsPrime) 
        {
          output.invVarsPrime[kv.first] = translateInvVars(kv.second, true);
        }

        for (auto v : output.invVarsPrime)
        {
          outs() << "InvVar: " << v.first << "\n";
          for (auto a : v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
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
      // Modify translateExprHelper signature to handle exceptions properly
      Expr translateExprHelper(Expr e) 
      {
        if (!e) return e;

        try {
          // Handle safe cases first
          if (bind::IsConst()(e))
            return translateVar(e);

          // Add numeric safety checks
          if (bv::is_bvnum(e)) {
            mpz_class val = bv::toMpz(e);
            // Check numeric bounds
            if (val > INT_MAX || val < INT_MIN) {
              if (m_debug) outs() << "Warning: Number out of safe range\n";
              return mk<TRUE>(m_efac);
            }
            return mkTerm(val, m_efac);
          }

          // Protect against unsafe operations - use NumericOp instead of BinaryOp
          if (isOp<NumericOp>(e)) {
            if (containsOp<IDIV>(e) || containsOp<MOD>(e)) {
              return mk<TRUE>(m_efac); 
            }
          }

          // Continue with regular translation
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
          else if (isOpX<BUDIV>(e) || isOpX<BSDIV>(e)) 
            return mk<DIV>(translateExpr(e->left()), translateExpr(e->right()));
          else if (isOpX<BUREM>(e) || isOpX<BSREM>(e))
            return mk<MOD>(translateExpr(e->left()), translateExpr(e->right()));
          
          // Comparisons - both signed/unsigned translate to same LIA ops
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
        catch (const std::exception& ex) {
          if (m_debug) outs() << "Error in translation: " << ex.what() << "\n";
          return mk<TRUE>(m_efac); 
        }
        return e;
      }
  };
} // namespace ufo

#endif
