#ifndef LIA2BV2_HPP
#define LIA2BV2_HPP

#include "deep/Horn.hpp"
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"
#include <optional>

namespace ufo
{
  namespace passes
  {
    class LIA2BV2
    {
    private:
      std::map<Expr, Expr> variableMap;
      std::map<Expr, Expr> declsMap;
      std::map<Expr, Expr> constMap;
      
      std::unique_ptr<CHCs> transformed;
      int bitwidth = 0;
      int debug = 0;
      
      unsigned int binaryLog(mpz_class v) {
        if(v < 0) {
          v *= -1;
        }
        if (v.fits_ulong_p()) {
          unsigned long v_ul = v.get_ui();
          unsigned int res = 1;
          while (v_ul >>= 1) {
            ++res;
          }
          return res;
        }
        size_t bitCount = mpz_sizeinbase(v.get_mpz_t(), 2);
        return static_cast<unsigned int>(bitCount);
      }
      
      int computeExpressionBitWidth(Expr e) {
        int maxBitWidth = 0;
        ExprSet conjs;
        getConj(e, conjs);
        
        for (auto &c : conjs) {
          if (debug >= 4) {
            outs() << "Computing bit width for: " << c << "\n";
          }
          
          if (isOpX<MPZ>(c)) {
            mpz_class val = getTerm<mpz_class>(c);
            int bw = binaryLog(val);
            if (debug >= 4) {
              outs() << "Constant bit width: " << bw << "\n";
            }
            if (bw > maxBitWidth) {
              maxBitWidth = bw;
            }
          }
          
          for (auto arg = c->args_begin(); arg != c->args_end(); ++arg) {
            if (*arg) {
              int argBw = computeExpressionBitWidth(*arg);
              maxBitWidth = std::max(maxBitWidth, argBw);
            }
          }
        }
        return maxBitWidth;
      }
      
      void translateConsts(Expr e) {
        ExprSet conjs;
        getConj(e, conjs);
        
        ExprSet vars;
        
        for (auto &c : conjs) {
          ExprSet localVars;
          filter(c, bind::IsConst(), inserter(localVars, localVars.begin()));
          
          for (auto &v : localVars) {
            if (debug >= 3) {
              outs() << "Found variable candidate: " << *v << "\n";
            }
            
            bool isIntVar = false;
            
            if (bind::isIntConst(v)) {
              isIntVar = true;
              if (debug >= 3) outs() << "  - Direct int const\n";
            }
            else if (isOpX<FAPP>(v) && v->arity() > 0) {
              Expr decl = v->left();
              if (bind::isFdecl(decl)) {
                for (unsigned i = 1; i < decl->arity(); i++) {
                  if (isOpX<INT_TY>(decl->arg(i))) {
                    isIntVar = true;
                    if (debug >= 3) outs() << "  - FAPP with INT_TY\n";
                    break;
                  }
                }
              }
            }
            
            if (isIntVar) {
              vars.insert(v);
            }
          }
        }
        
        if (debug >= 2) {
          outs() << "Found " << vars.size() << " variables\n";
        }
        
        for (auto &var : vars) {
          if (variableMap.count(var) == 0) {
            if (debug >= 3) {
              outs() << "Creating BV var for: " << *var << "\n";
            }
            
            Expr bvVar = bv::bvConst(var, bitwidth);
            variableMap[var] = bvVar;
            
            if (debug >= 3) {
              outs() << "Mapped to BV var: " << *bvVar << "\n";
            }
          }
        }
        
        for (auto &c : conjs) {
          if (debug >= 3) {
            outs() << "Converting constant: " << *c << "\n";
          }
          
          if (isOpX<MPZ>(c)) {
            mpz_class val = getTerm<mpz_class>(c);
            constMap[c] = bv::bvnum(val, bitwidth, c->getFactory());
            if (debug >= 3) {
              outs() << "Mapped " << *c << " to " << *constMap[c] << "\n";
            }
          }
          
          for(auto arg = c->args_begin(); arg != c->args_end(); ++arg) {
            if (*arg) {
              translateConsts(*arg);
            }
          }
        }
      }
      
      bool isBoolVar(Expr var) {
        if (bind::isBoolConst(var)) {
          if (debug >= 3) outs() << "  - Direct bool const\n";
          return true;
        }
        else if (isOpX<FAPP>(var) && var->arity() > 0) {
          Expr decl = var->left();
          if (bind::isFdecl(decl)) {
            for (unsigned i = 1; i < decl->arity(); i++) {
              if (isOpX<BOOL_TY>(decl->arg(i))) {
                if (debug >= 3) outs() << "  - FAPP with BOOL_TY\n";
                return true;
              }
            }
          }
        }
        return false;
      }
      
      ExprVector translateInvVars(const ExprVector &origVars, bool isInvVars = false) {
        ExprVector translatedVars;
        
        for (const auto &var : origVars) {
          if (debug >= 3) {
            outs() << "Translating variable: " << *var << "\n";
          }
          
          // Determine bitwidth based on variable type
          int varBitwidth = isBoolVar(var) ? 1 : bitwidth;
          
          Expr bvVar = bv::bvConst(var, varBitwidth);
          translatedVars.push_back(bvVar);
          
          if (isInvVars) {
            variableMap[var] = bvVar;
          }
          
          if (debug >= 3) {
            outs() << "Translated to BV var: " << *bvVar << " with width " << varBitwidth << "\n";
          }
        }
        return translatedVars;
      }
      
      Expr translateOperation(Expr e, ExprVector n_args) {
        if (n_args.size() > 2) {
          ExprVector nn_args(n_args.begin() + 1, n_args.end());
          Expr subExpression = translateOperation(e, nn_args);
          n_args.resize(1);
          n_args.push_back(subExpression);
        }
        
        if (isOpX<EQ>(e)) return mknary<EQ>(n_args);
        if (isOpX<NEQ>(e)) return mknary<NEQ>(n_args);
        if (isOpX<LEQ>(e)) return mknary<BULE>(n_args); 
        if (isOpX<GEQ>(e)) return mknary<BUGE>(n_args); 
        if (isOpX<LT>(e)) return mknary<BULT>(n_args);  
        if (isOpX<GT>(e)) return mknary<BUGT>(n_args);  
        
        if (isOpX<PLUS>(e)) return mknary<BADD>(n_args);
        
        if (isOpX<MINUS>(e)) {
          if (n_args.size() == 2) {
            return mk<BSUB>(n_args[0], n_args[1]);
          } else {
            return bv::bvneg(n_args[0]);
          }
        }
        
        if (isOpX<MULT>(e)) return mknary<BMUL>(n_args);
        if (isOpX<IDIV>(e)) return mknary<BUDIV>(n_args); 
        if (isOpX<MOD>(e)) return mknary<BUREM>(n_args);  
        
        if (debug >= 1) {
          outs() << "Warning: Unhandled operation in translation: " << *e << "\n";
        }
        return e; 
      }
      
      Expr translateRecursively(Expr exp) {
        if (debug >= 3) outs() << "Translating expression: " << *exp << "\n";
        
        auto isConstant = bind::IsHardIntConst{};
        if (isConstant(exp)) {
          if (constMap.count(exp) > 0) {
            return constMap.at(exp);
          }
          mpz_class val = getTerm<mpz_class>(exp);
          Expr bvConst = bv::bvnum(val, bitwidth, exp->getFactory());
          constMap[exp] = bvConst;
          return bvConst;
        }
        
        if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<IFF>(exp)) {
          ExprVector n_args;
          for (auto it = exp->args_begin(); it != exp->args_end(); ++it) {
            n_args.push_back(translateRecursively(*it));
          }
          return isOpX<AND>(exp) ? conjoin(n_args, exp->getFactory()) : 
                 isOpX<OR>(exp) ? disjoin(n_args, exp->getFactory()) : 
                 mknary<IFF>(n_args);
        }
        
        if (isOpX<NEG>(exp)) {
          return mkNeg(translateRecursively(exp->first()));
        }
        
        if (isOp<ComparissonOp>(exp) || isOp<NumericOp>(exp)) {
          ExprVector n_args;
          
          if (isOpX<UN_MINUS>(exp)) {
            Expr operand = translateRecursively(exp->first());
            return bv::bvneg(operand);
          }
          
          if (isOpX<MINUS>(exp) && exp->arity() == 2) {
            Expr left = translateRecursively(exp->left());
            Expr right = translateRecursively(exp->right());
            return mk<BSUB>(left, right);
          }
          
          if (isOpX<MULT>(exp) && exp->arity() == 2) {
            auto isMinusOne = [](Expr e) -> bool { 
              return bind::IsHardIntConst{}(e) && getTerm<mpz_class>(e) == -1; 
            };
            
            Expr left = exp->left();
            Expr right = exp->right();
            
            if (isMinusOne(left)) {
              return bv::bvneg(translateRecursively(right));
            }
            if (isMinusOne(right)) {
              return bv::bvneg(translateRecursively(left));
            }
          }
          
          for (auto it = exp->args_begin(); it != exp->args_end(); ++it) {
            n_args.push_back(translateRecursively(*it));
          }
          
          return translateOperation(exp, n_args);
        }
        
        if (bind::isBoolConst(exp)) {
          return exp; 
        }
        
        if (isOpX<ITE>(exp)) {
          Expr cond = translateRecursively(exp->arg(0));
          Expr then_branch = translateRecursively(exp->arg(1));
          Expr else_branch = translateRecursively(exp->arg(2));
          return mk<ITE>(cond, then_branch, else_branch);
        }
        
        if (variableMap.count(exp) > 0) {
          return variableMap.at(exp);
        }
        
        if (debug >= 1) {
          outs() << "Warning: Unhandled expression in translation: " << *exp << "\n";
        }
        
        return exp; 
      }
      
      void findBitWidth(const std::vector<HornRuleExt> &origClauses) {
        for (const auto &clause : origClauses) {
          int bw = computeExpressionBitWidth(clause.body);
          if (bw > bitwidth) bitwidth = bw;
        }
        
        bitwidth = std::max(bitwidth, 4);
        
        if (debug >= 2) {
          outs() << "Selected bit width: " << bitwidth << "\n";
        }
      }
      
      ExprSet translateDeclarations(const ExprSet &originals) {
        ExprSet ret;
        
        for (const auto &decl : originals) {
          if (!bind::isFdecl(decl)) continue;
          
          ExprVector types;
          for (int i = 1; i < decl->arity(); ++i) {
            Expr arg = decl->arg(i);
            Expr type;
            
            if (isOpX<INT_TY>(arg)) {
              type = bv::bvsort(bitwidth, arg->getFactory());
            } else if (isOpX<BOOL_TY>(arg)) {
              type = bv::bvsort(1, arg->getFactory());
            } else {
              type = arg;
            }
            
            types.push_back(type);
          }
          
          Expr name = bind::fname(decl);
          Expr translated = bind::fdecl(name, types);
          declsMap[decl] = translated;
          ret.insert(translated);
          
          if (debug >= 3) {
            outs() << "Translated declaration: " << *decl << " to " << *translated << "\n";
          }
        }
        
        return ret;
      }
      
      std::vector<HornRuleExt> translateClauses(const std::vector<HornRuleExt> &origClauses) {
        for (const auto &clause : origClauses) {
          translateConsts(clause.body);
        }
        
        if (debug >= 3) {
          outs() << "Constant mappings:\n";
          for (auto const &entry : constMap) {
            outs() << *entry.first << " -> " << *entry.second << "\n";
          }
        }
        
        std::vector<HornRuleExt> translatedClauses;
        for (const auto &clause : origClauses) {
          translatedClauses.emplace_back();
          HornRuleExt &translated = translatedClauses.back();
          
          translated.isQuery = clause.isQuery;
          translated.isFact = clause.isFact;
          translated.isInductive = clause.isInductive;
          
          translated.srcVars = translateInvVars(clause.srcVars);
          translated.dstVars = translateInvVars(clause.dstVars);
          translated.locVars = translateInvVars(clause.locVars, true);
          
          if (debug >= 3) {
            outs() << "Variable mappings:\n";
            for (auto const &entry : variableMap) {
              outs() << *entry.first << " -> " << *entry.second << "\n";
            }
          }
          
          // Translate the body of the clause
          translated.body = translateRecursively(normalize(clause.body));
          
          if (debug >= 3) {
            outs() << "Original body: " << *clause.body << "\n";
            outs() << "Translated body: " << *translated.body << "\n";
          }
          
          translated.dstRelation = clause.dstRelation;
          translated.srcRelation = clause.srcRelation;
        }
        
        return translatedClauses;
      }
      
    public:
      LIA2BV2(int _debug = 0) : debug(_debug) {}
      
      CHCs* getTransformed() { return transformed.get(); }
      
      void operator()(const CHCs &system) {
        transformed.reset(new CHCs{system.m_efac, system.m_z3});
        CHCs &bvSystem = *transformed;
        
        variableMap.clear();
        declsMap.clear();
        constMap.clear();
        
        findBitWidth(system.chcs);
        
        bvSystem.failDecl = system.failDecl;
        
        for (auto &v : system.invVars) {
          if (v.first == mk<TRUE>(v.first->getFactory())) continue;
          bvSystem.invVars[v.first] = translateInvVars(system.invVars.at(v.first), true);
        }
        
        if (debug >= 2) outs() << "Translating invariant variables\n";
        for (auto &d : system.decls) {
          if (d == mk<TRUE>(d->getFactory())) continue;
          
          if (debug >= 3) outs() << "Declaration: " << *d << "\n";
          
          bvSystem.invVars[d->left()] = translateInvVars(system.invVars.at(d->left()), true);
          
          if (system.invVarsPrime.count(d->left()) > 0) {
            bvSystem.invVarsPrime[d->left()] = translateInvVars(system.invVarsPrime.at(d->left()), true);
          }
        }
        
        bvSystem.chcs = translateClauses(system.chcs);
        
        bvSystem.decls = translateDeclarations(system.decls);
        
        if (debug >= 1) {
          outs() << "LIA to BV translation completed with bit width " << bitwidth << "\n";
        }
      }
      
      Expr translateExpression(const Expr &expr, int forceBitWidth = 0) {
        if (forceBitWidth > 0) {
          bitwidth = forceBitWidth;
        } else if (bitwidth == 0) {
          bitwidth = computeExpressionBitWidth(expr);
          bitwidth = std::max(bitwidth, 4);
        }
        
        translateConsts(expr);
        return translateRecursively(expr);
      }

      Expr translateExpression(Expr expr, unsigned bitWidth = 32) {
        if (debug > 0) 
            outs() << "Translating expression: " << *expr << "\n";
            
        if (variableMap.count(expr) > 0) {
            if (debug > 1) outs() << "Found variable in map: " << *expr << " -> " << *variableMap[expr] << "\n";
            return variableMap[expr];
        }
        
        if (bind::isIntConst(expr) || 
            (isOpX<FAPP>(expr) && expr->arity() > 0 && bind::isFdecl(expr->left()))) {
            if (debug > 1) outs() << "Creating BV var for variable: " << *expr << "\n";
            Expr bvVar = bv::bvConst(expr, bitWidth);
            variableMap[expr] = bvVar;
            return bvVar;
        }
        
        if (isOpX<MPZ>(expr)) {
            mpz_class val = getTerm<mpz_class>(expr);
            return bv::bvnum(val, bitWidth, expr->getFactory());
        }
        
        if (expr->arity() >= 1) {
            if (isOpX<PLUS>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                return mknary<BADD>(args);
            }
            else if (isOpX<MINUS>(expr)) {
                if (expr->arity() == 1) {
                    return bv::bvneg(translateExpression(expr->arg(0), bitWidth));
                } else {
                    return mk<BSUB>(translateExpression(expr->arg(0), bitWidth), 
                                   translateExpression(expr->arg(1), bitWidth));
                }
            }
            else if (isOpX<MULT>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                return mknary<BMUL>(args);
            }
            else if (isOpX<IDIV>(expr)) {
                return mk<BUDIV>(translateExpression(expr->arg(0), bitWidth), 
                               translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<UN_MINUS>(expr)) {
                Expr arg = translateExpression(expr->arg(0), bitWidth);
                return bv::bvneg(arg);
            }
            else if (isOpX<EQ>(expr)) {
                return mk<EQ>(translateExpression(expr->arg(0), bitWidth), 
                            translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<NEQ>(expr)) {
                Expr arg0 = translateExpression(expr->arg(0), bitWidth);
                Expr arg1 = translateExpression(expr->arg(1), bitWidth);
                return mk<NEG>(mk<EQ>(arg0, arg1));
            }
            else if (isOpX<LEQ>(expr)) {
                return mk<BULE>(translateExpression(expr->arg(0), bitWidth), 
                              translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<LT>(expr)) {
                return mk<BULT>(translateExpression(expr->arg(0), bitWidth), 
                              translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<GEQ>(expr)) {
                return mk<BUGE>(translateExpression(expr->arg(0), bitWidth), 
                              translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<GT>(expr)) {
                return mk<BUGT>(translateExpression(expr->arg(0), bitWidth), 
                              translateExpression(expr->arg(1), bitWidth));
            }
            else if (isOpX<AND>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                return mknary<AND>(args);
            }
            else if (isOpX<OR>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                return mknary<OR>(args);
            }
            else if (bind::isBoolConst(expr)) {
                return expr; 
            }
        }
        
        if (expr->arity() == 0 || (isOpX<FAPP>(expr) && expr->arity() <= 2)) {
            if (debug > 1) outs() << "Treating as variable: " << *expr << "\n";
            
            if (variableMap.count(expr) > 0) {
                return variableMap[expr];
            }
            Expr bvVar = bv::bvConst(expr, bitWidth);
            variableMap[expr] = bvVar;
            return bvVar;
        }
        
        outs() << "Warning: Unhandled expression in translation: " << *expr << "\n";
        return expr;
      }
    };

  } // namespace passes
} // namespace ufo

#endif // LIA2BV2_HPP
