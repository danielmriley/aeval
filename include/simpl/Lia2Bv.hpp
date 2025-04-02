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
      int debug;  // Add debug member
      
      // Maps for tracking translations
      std::map<Expr, Expr> m_var_map;      // Maps LIA vars to BV vars  
      std::map<Expr, Expr> m_decl_map;     // Maps LIA decls to BV decls
      
      // Translation helpers
      Expr translateVar(Expr var)
      {
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
            return it->second;

        if (!isOpX<INT_TY>(bind::typeOf(var)))
            return var;
            
        // Create BV variable using bv::bvConst
        Expr name = bind::fname(bind::fname(var));
        Expr bvVar = bv::bvConst(name, m_width);
        m_var_map[var] = bvVar;
        
        if (debug >= 3) {
            outs() << "Mapped " << *var << " to " << *bvVar << "\n";
        }
        return bvVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        
        for (const auto &var : origVars)
        {
            if (!isOpX<INT_TY>(bind::typeOf(var))) {
                translatedVars.push_back(var);
                continue;
            }

            // Use same translation logic as translateVar
            Expr name = bind::fname(bind::fname(var));
            Expr bvVar = bv::bvConst(name, m_width);
            translatedVars.push_back(bvVar);
            
            if (cacheVars) {
                m_var_map[var] = bvVar;
                if (debug >= 3) {
                    outs() << "Cached mapping: " << *var << " -> " << *bvVar << "\n";
                }
            }
        }
        return translatedVars;
      }

      // Add new helper methods for bitwidth calculation
      unsigned int binaryLog(mpz_class v)
      {
        // Small numbers optimization
        if (v == 0) return 1;
        if (v == 1) return 1;
        
        // Get absolute value for negative numbers
        if (v < 0) v = -v;
        
        // Calculate log2 rounded up
        unsigned int width = 1;
        v = v - 1;
        while (v > 0) {
          v = v >> 1;
          width++;
        }
        return width;
      }

      unsigned int findMinBitWidth(const std::vector<HornRuleExt>& rules)
      {
        unsigned int maxWidth = m_width;

        // Helper to process an expression and update maxWidth
        std::function<void(Expr)> processExpr = [&](Expr e) {
          if (!e) return;
          
          // Check for integer constants
          if (isOpX<MPZ>(e)) {
            unsigned int width = binaryLog(getTerm<mpz_class>(e));
            maxWidth = std::max(maxWidth, width + 1); // +1 for sign bit
          }
          
          // Recursively process all arguments
          for (unsigned i = 0; i < e->arity(); ++i) {
            processExpr(e->arg(i));
          }
        };

        // Process all rules
        for (const auto& rule : rules) {
          processExpr(rule.body);
          for (const auto& v : rule.srcVars) processExpr(v);
          for (const auto& v : rule.dstVars) processExpr(v);
          for (const auto& v : rule.locVars) processExpr(v);
        }

        // Round up to nearest power of 2 greater than 4
        maxWidth = std::max(maxWidth, (unsigned int)4);
        unsigned int pow2 = 4;
        while (pow2 < maxWidth) pow2 *= 2;
        
        return pow2;
      }

    public:
      Lia2BvTranslator(ExprFactory &efac, EZ3 &z3, unsigned width = 4, int _debug = 0) : 
        m_efac(efac), m_z3(z3), m_width(width), debug(_debug) {}

      CHCs translate(CHCs &input)
      {
        // Calculate minimum required bitwidth
        m_width = findMinBitWidth(input.chcs);

        if (debug >= 2) {
          outs() << "Using bit width: " << m_width << "\n";
        }

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
      Expr translateExpr(Expr e, unsigned width = 0)
      {
        // Use provided width or default if not specified
        unsigned w = width > 0 ? width : m_width;
        
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

      // Rename existing translateExpr to translateExprHelper  
      Expr translateExprHelper(Expr e)
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

        // Handle operations - all LIA operations are signed
        if (isOpX<PLUS>(e))
          return bv::bvadd(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<MINUS>(e))
          return mk<BSUB>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<MULT>(e))
          return mk<BMUL>(translateExpr(e->left()), translateExpr(e->right()));
        else if (isOpX<DIV>(e)) {
          // LIA division is always signed integer division
          Expr left = translateExpr(e->left());
          Expr right = translateExpr(e->right());
          // Optionally add check for division by zero
          return mk<BSDIV>(left, right); 
        }
        else if (isOpX<IDIV>(e)) {
          // Floor division in LIA also maps to signed BV division
          Expr left = translateExpr(e->left());
          Expr right = translateExpr(e->right());
          return mk<BSDIV>(left, right);
        }
        else if (isOpX<MOD>(e)) {
          // LIA mod becomes signed remainder
          Expr left = translateExpr(e->left());
          Expr right = translateExpr(e->right());
          return mk<BSREM>(left, right);
        }
        else if (isOpX<UN_MINUS>(e))
          return bv::bvneg(translateExpr(e->left()));
        else if (isOpX<LEQ>(e))
          return bv::bvsle(translateExpr(e->left()), translateExpr(e->right())); // Changed to signed
        else if (isOpX<LT>(e))
          return bv::bvslt(translateExpr(e->left()), translateExpr(e->right())); // Changed to signed
        else if (isOpX<GEQ>(e))
          return bv::bvsge(translateExpr(e->left()), translateExpr(e->right())); // Changed to signed 
        else if (isOpX<GT>(e))
          return bv::bvsgt(translateExpr(e->left()), translateExpr(e->right())); // Changed to signed
          
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
