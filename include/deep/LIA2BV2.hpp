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
      
      Expr wrapConstant(mpz_class val, ExprFactory &efac) {
        Expr bvConst = bv::bvnum(val, bitwidth, efac);
        constMap[bvConst] = bvConst;
        return bvConst;
      }

      Expr makeNegativeConstant(mpz_class val, ExprFactory &efac) {
        // Use subtraction from zero instead of bvneg
        Expr zero = bv::bvnum(0, bitwidth, efac);
        Expr posConst = bv::bvnum(val, bitwidth, efac);
        return mk<BSUB>(zero, posConst);
      }

      Expr handleConstantMultiplication(mpz_class val, Expr other) {
        if (val == -1) {
          return bv::bvneg(other);
        }
        if (val < 0) {
          // Convert -N*x directly to bvneg(bvmul(N,x)) instead of using subtraction
          val = -val;
          Expr posConst = bv::bvnum(val, bitwidth, other->getFactory());
          return bv::bvneg(mk<BMUL>(posConst, other));
        }
        return mk<BMUL>(bv::bvnum(val, bitwidth, other->getFactory()), other);
      }

      Expr handleArithmeticTerm(Expr term) {
        // Use bb::BVNEG for checking bit-vector negation
        if (isOpX<BNEG>(term)) {
          Expr zero = bv::bvnum(0, bitwidth, term->getFactory());
          return mk<BSUB>(zero, term->arg(0));
        }
        return term;
      }

      Expr translateOperation(Expr e, ExprVector n_args) {
        if (n_args.size() == 0) return nullptr;
        if (n_args.size() == 1) return n_args[0];
        
        if (n_args.size() > 2) {
          // Build operations in strict binary fashion left-to-right
          ExprVector bin_args;
          bin_args.push_back(n_args[0]);
          
          for (size_t i = 1; i < n_args.size(); i++) {
            ExprVector pair = {bin_args[0], n_args[i]};
            
            if (isOpX<PLUS>(e)) {
              // For addition, handle subtractions specially
              if (isOpX<BSUB>(n_args[i]) && isOpX<MPZ>(n_args[i]->left()) &&
                  getTerm<mpz_class>(n_args[i]->left()) == 0) {
                bin_args[0] = mk<BSUB>(bin_args[0], n_args[i]->right());
              } else {
                bin_args[0] = mk<BADD>(bin_args[0], n_args[i]);
              }
            } else {
              bin_args[0] = translateOperation(e, pair);
            }
          }
          return bin_args[0];
        }

        // Now handle the binary case
        if (isOpX<PLUS>(e)) {
          // Special case: combining a term with a subtraction
          if (isOpX<BSUB>(n_args[1]) && isOpX<MPZ>(n_args[1]->left()) &&
              getTerm<mpz_class>(n_args[1]->left()) == 0) {
            // Convert (bvadd x (bvsub 0 y)) to (bvsub x y)
            return mk<BSUB>(n_args[0], n_args[1]->right());
          }
          return mk<BADD>(n_args[0], n_args[1]);
        }

        // For other operations, use direct translation
        if (isOpX<EQ>(e)) {
          return mk<EQ>(n_args[0], n_args[1]);
        }
        if (isOpX<NEQ>(e)) {
          return mk<NEQ>(n_args[0], n_args[1]); 
        }
        if (isOpX<LEQ>(e)) {
          return mk<BULE>(n_args[0], n_args[1]);
        }
        if (isOpX<GEQ>(e)) {
          return mk<BUGE>(n_args[0], n_args[1]);
        }
        if (isOpX<LT>(e)) {
          return mk<BULT>(n_args[0], n_args[1]);
        }
        if (isOpX<GT>(e)) {
          return mk<BUGT>(n_args[0], n_args[1]);
        }
        
        if (isOpX<PLUS>(e)) {
          if (isOpX<BSUB>(n_args[1]) && isOpX<MPZ>(n_args[1]->left()) && 
              getTerm<mpz_class>(n_args[1]->left()) == 0) {
            // Convert (bvadd x (bvsub 0 y)) to (bvsub x y)
            return mk<BSUB>(n_args[0], n_args[1]->right());
          }
          return mk<BADD>(n_args[0], n_args[1]);
        }

        // For other operations, use direct translation
        if (isOpX<PLUS>(e)) {
          return mk<BADD>(n_args[0], n_args[1]);
        }
        if (isOpX<MULT>(e)) {
          return mk<BMUL>(n_args[0], n_args[1]);
        }
        if (isOpX<MINUS>(e)) {
          if (n_args.size() == 2) {
            return mk<BSUB>(n_args[0], n_args[1]);
          }
          return bv::bvneg(n_args[0]);
        }
        if (isOpX<IDIV>(e)) {
          return mk<BUDIV>(n_args[0], n_args[1]);
        }
        if (isOpX<MOD>(e)) {
          return mk<BUREM>(n_args[0], n_args[1]);
        }
        
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
          if (val < 0) {
            val = -val; // Make positive
            Expr result = makeNegativeConstant(val, exp->getFactory());
            constMap[exp] = result;
            return result;
          }
          Expr bvConst = bv::bvnum(val, bitwidth, exp->getFactory());
          constMap[exp] = bvConst;
          return bvConst;
        }
        
        if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<IFF>(exp)) {
          ExprVector n_args;
          for (auto it = exp->args_begin(); it != exp->args_end(); ++it) {
            n_args.push_back(translateRecursively(*it));
          }

          if (n_args.size() > 2) {
            Expr result = n_args[0];
            for (size_t i = 1; i < n_args.size(); ++i) {
              if (isOpX<AND>(exp)) {
                result = mk<AND>(result, n_args[i]);
              } else if (isOpX<OR>(exp)) {
                result = mk<OR>(result, n_args[i]);
              } else {
                result = mk<IFF>(result, n_args[i]);
              }
            }
            return result;
          }
          return translateOperation(exp, n_args);
        }

        // Handle all forms of unary minus in one place
        if (isOpX<UN_MINUS>(exp)) {
          Expr operand = translateRecursively(exp->first());
          return isOpX<NEG>(exp) ? operand : bv::bvneg(operand);
        }
        
        if (isOp<ComparissonOp>(exp) || isOp<NumericOp>(exp)) {
          ExprVector n_args;
          
          // Special case: multiplication by -1
          if (isOpX<MULT>(exp) && exp->arity() == 2) {
            auto isMinusOne = [](Expr e) -> bool { 
              return bind::IsHardIntConst{}(e) && getTerm<mpz_class>(e) == -1; 
            };
            
            Expr left = exp->left();
            Expr right = exp->right();
            
            if (isMinusOne(left) || isMinusOne(right)) {
              return bv::bvneg(translateRecursively(isMinusOne(left) ? right : left));
            }
          }
          
          // Handle binary minus separately from unary minus
          if (isOpX<MINUS>(exp) && exp->arity() == 2) {
            Expr left = translateRecursively(exp->left());
            Expr right = translateRecursively(exp->right());
            return mk<BSUB>(left, right);
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
          translated.body = translateRecursively(simplifyArithm(normalize(clause.body)));
          
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
            // Handle n-ary operations by building binary chains
            if (isOpX<PLUS>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                // Convert n-ary PLUS to binary chain
                Expr result = args[0];
                for (size_t i = 1; i < args.size(); ++i) {
                    result = mk<BADD>(result, args[i]);
                }
                return result;
            }
            else if (isOpX<MULT>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                // Convert n-ary MULT to binary chain 
                Expr result = args[0];
                for (size_t i = 1; i < args.size(); ++i) {
                    result = mk<BMUL>(result, args[i]);
                }
                return result;
            }
            else if (isOpX<AND>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                // Convert n-ary AND to binary chain
                Expr result = args[0];
                for (size_t i = 1; i < args.size(); ++i) {
                    result = mk<AND>(result, args[i]);
                }
                return result;
            }
            else if (isOpX<OR>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                // Convert n-ary OR to binary chain
                Expr result = args[0];
                for (size_t i = 1; i < args.size(); ++i) {
                    result = mk<OR>(result, args[i]);
                }
                return result;
            }
            // Keep binary operations as-is
            else if (isOpX<MINUS>(expr)) {
                if (expr->arity() == 1) {
                    return bv::bvneg(translateExpression(expr->arg(0), bitWidth));
                } else {
                    return mk<BSUB>(translateExpression(expr->arg(0), bitWidth), 
                                  translateExpression(expr->arg(1), bitWidth));
                }
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
                return mk<AND>(args[0], args[1]);
            }
            else if (isOpX<OR>(expr)) {
                ExprVector args;
                for (auto it = expr->args_begin(); it != expr->args_end(); ++it) {
                    args.push_back(translateExpression(*it, bitWidth));
                }
                return mk<OR>(args[0], args[1]);
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
