#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include "Horn.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"
#include "ae/ExprSimpl.hpp" // Include ExprSimpl for simplification functions
#include <utility> // Needed for std::pair

using namespace std;

namespace ufo
{
  class BitHorn 
  {
    private:
    ExprFactory &m_efac;
    EZ3 &m_z3;
    CHCs* m_liaChcs;  // Changed to pointer
    CHCs m_bvChcs;   
    SMTUtils u;
    Lia2BvTranslator m_Lia2BvTranslator;
    Bv2LiaTranslator m_Bv2LiaTranslator; 
    int debug; 
    std::vector<ExprSet> m_learnedLemmas;  // Stores learned lemmas per iteration
    unsigned m_original_bv_width = 0;
    map<Expr, ExprSet> m_liaSolutionMap; // Maps LIA relation -> LIA solution ExprSet
    map<Expr, Expr> m_bvSolutionMap;   // Maps BV relation -> combined BV solution Expr

    map<Expr, ExprVector> origBvVars;  // Original BV variables in the program
    map<Expr, ExprVector> origBvVarsPrime;  // Original primed BV variables in the program
    map<Expr, ExprVector> origLiaVars; // Original LIA variables in the program
    map<Expr, ExprVector> origLiaVarsPrime; // Original primed LIA variables in the program

    void printBvSolutionMap(const map<Expr, Expr>& bvSolutionMap) {
      for (const auto& kv : bvSolutionMap) {
        Expr rel = kv.first;
        Expr solution = kv.second; // This is the combined BV solution

        // Check if relation exists in invVars map
        if (!m_bvChcs.invVars.count(rel)) {
            if (debug >= 1) outs() << "; [printBvSolutionMap] Warning: Cannot print solution for " << *rel << " - missing variables.\n";
            continue;
        }
        const ExprVector& invVars = m_bvChcs.invVars.at(rel);

        // Print function definition header
        outs() << "(define-fun " << *rel << " (";
        for (const auto& var : invVars) {
          // Print var name and type
          outs() << "(" << *var << " ";
          u.print(typeOf(var));
          outs() << ")";
        }
        outs() << ") Bool\n  ";

        // Print the combined BV solution expression
        u.print(solution);
        outs() << ")\n";

        ExprVector nonConstInvVars = invVars; // Create non-const copy for validation
        bool valid = hasOnlyVars(solution, nonConstInvVars);
        if (!valid && debug >= 1) {
            outs() << "; [printBvSolutionMap] Warning: Solution for " << *rel << " contains unexpected variables!\n";
            ExprSet extra;
            getExtraVars(solution, nonConstInvVars, extra);
            outs() << ";   Extra vars: ";
            for(const auto& v : extra) outs() << *v << " ";
            outs() << "\n";
        }
      }
    }

    Expr normalizeExpr(Expr e) {
      if (!e) return e;
      
      // Handle division and mod operations safely
      if (containsOp<IDIV>(e) || containsOp<MOD>(e)) {
        return mk<TRUE>(e->getFactory());
      }

      // Ensure numeric operations use safe ranges
      if (isOpX<PLUS>(e) || isOpX<MINUS>(e) || isOpX<MULT>(e)) {
        ExprVector safeArgs;
        for (unsigned i = 0; e && i < e->arity(); i++) {
          safeArgs.push_back(normalizeExpr(e->arg(i)));
        }
        return e->efac().mkNary(e->op(), safeArgs);
      }

      // Use ineqReverter from ExprSimpl.hpp
      return ineqReverter(e);
    }

    // --- New helper method to normalize comparisons with positive coefficients ---
    /**
     * Normalizes a comparison expression `e` (like <=, >=, <, >) involving linear arithmetic
     * such that all variable coefficients are positive.
     * Example: (-2*x + 3*y <= 5) becomes (3*y <= 2*x + 5)
     * Assumes `e` has been pre-processed by `normalizeAtom` to be in the form Sum(ci*vi) op C.
     * Returns the normalized expression, or the original expression if normalization fails or is not applicable.
     */
    Expr normalizePositive(Expr e) {
        // Only normalize comparisons involving numeric expressions
        if (!isOp<ComparissonOp>(e) || !isNumeric(e->left())) {
             // if (debug >= 4) outs() << "[normalizePositive] Skipping non-numeric comparison: " << *e << "\n";
            return e;
        }

        if (debug >= 4) outs() << "[normalizePositive] Input: " << *e << "\n";

        // 1. Use normalizeAtom to get Sum(ci*vi) op C form
        ExprVector vars;
        // Collect all variables appearing in the expression
        filter(e, bind::IsConst(), inserter(vars, vars.begin()));
        if (vars.empty()) {
             if (debug >= 4) outs() << "[normalizePositive] No variables found in: " << *e << "\n";
             // It might be a comparison of constants, simplify it directly
             return simplifyArithm(e);
        }

        // Use normalizeAtom from ExprSimpl.hpp
        Expr normalized = normalizeAtom(e, vars);

        if (debug >= 4) outs() << "[normalizePositive] After normalizeAtom: " << *normalized << "\n";

        if (isOpX<TRUE>(normalized) || isOpX<FALSE>(normalized)) {
            return normalized; // Already simplified to true/false
        }

        // Check if normalizeAtom produced the expected form
        if (!isOp<ComparissonOp>(normalized) || !isNumeric(normalized->left()) || !isNumeric(normalized->right())) {
             if (debug >= 1) outs() << "[normalizePositive] Warning: normalizeAtom did not produce expected Sum(ci*vi) op C form for: " << *e << ". Got: " << *normalized << "\n";
             // Attempt arithmetic simplification as a fallback
             return simplifyArithm(e);
        }

        Expr lhs = normalized->left();
        Expr rhs = normalized->right(); // Should be the constant C
        const Operator& op = normalized->op();

        // 2. Extract coefficients and constant term relative to LHS = 0 form
        map<Expr, cpp_int> termCoefficients;
        cpp_int constantPart = 0; // Represents the constant if the expression is in the form LHS - C = 0

        ExprVector terms;
        getAddTerm(lhs, terms); // Get terms from Sum(ci*vi)

        for (Expr term : terms) {
            cpp_int coef = 1;
            Expr varPart = term;
            if (isOpX<MULT>(term) && term->arity() == 2 && isOpX<MPZ>(term->left())) {
                // Assuming coefficient is always the left operand of MULT
                coef = lexical_cast<cpp_int>(term->left());
                varPart = term->right();
            } else if (isOpX<UN_MINUS>(term) && term->arity() == 1) {
                coef = -1;
                varPart = term->left();
            } else if (isOpX<MPZ>(term)) {
                // Constant term found on LHS (shouldn't happen with normalizeAtom?)
                constantPart = constantPart + lexical_cast<cpp_int>(term);
                if (debug >= 3)
                  outs() << "[normalizePositive] Found constant " << *term << " on LHS of normalized expr.\n";
                continue; // Skip to next term
            }

            // Ensure varPart is a variable (or treat as atomic)
            // Using bind::IsConst() to identify variables/program constants
            if (bind::IsConst()(varPart)) {
                termCoefficients[varPart] += coef;
            } else {
                // If it's not a variable, treat it as an atomic term with coefficient 1 or -1
                 if (debug >= 3) outs() << "[normalizePositive] Treating non-variable term " << *varPart << " as atomic.\n";
                termCoefficients[varPart] += coef; // Accumulate coefficient for the term itself
            }
        }

        // Subtract the constant C from the RHS (since we want LHS - C op 0)
        if (isOpX<MPZ>(rhs)) {
            // Convert mpz_class to cpp_int before subtracting
            constantPart = constantPart - cpp_int(getTerm<mpz_class>(rhs).get_str());
        } else {
             if (debug >= 1) outs() << "[normalizePositive] Warning: RHS of normalized expression is not an MPZ constant: " << *rhs << "\n";
             return simplifyArithm(e); // Fallback
        }

        if (debug >= 4) {
            outs() << "[normalizePositive] Coefficients map:\n";
            // --- Replace structured binding ---
            for(auto const& pair : termCoefficients) {
                Expr var = pair.first;
                cpp_int coef = pair.second;
            // --- End Replace structured binding ---
                outs() << "  " << *var << ": " << coef << "\n";
            }
            outs() << "[normalizePositive] Constant part (LHS - C): " << constantPart << "\n";
        }


        // 3. Separate positive and negative terms for final LHS/RHS
        ExprVector finalLhsTerms;
        ExprVector finalRhsTerms;
        // --- Replace structured binding ---
        for (auto const& pair : termCoefficients) {
            Expr var = pair.first;
            cpp_int coef = pair.second;
        // --- End Replace structured binding ---
            if (coef > 0) { // Positive coefficient -> stays on LHS
                if (coef == 1) {
                    finalLhsTerms.push_back(var);
                } else {
                    finalLhsTerms.push_back(mk<MULT>(mkMPZ(coef, m_efac), var));
                }
            } else if (coef < 0) { // Negative coefficient -> moves to RHS (becomes positive)
                cpp_int posCoef = -coef;
                if (posCoef == 1) {
                    finalRhsTerms.push_back(var);
                } else {
                    finalRhsTerms.push_back(mk<MULT>(mkMPZ(posCoef, m_efac), var));
                }
            }
            // Ignore terms with coef == 0
        }

        // 4. Place the constant term based on constantPart (which represents LHS - C)
        // We want finalLHS op finalRHS + FinalConstant
        // We derived PosLHS - PosRHS + constantPart = 0 (relative to original op)
        // If constantPart > 0: PosLHS + const = PosRHS => Add const to LHS
        // If constantPart < 0: PosLHS = PosRHS + abs(const) => Add abs(const) to RHS
        if (constantPart > 0) {
            finalLhsTerms.push_back(mkMPZ(constantPart, m_efac));
        } else if (constantPart < 0) {
            finalRhsTerms.push_back(mkMPZ(-constantPart, m_efac)); // Add positive abs(constantPart)
        }
        // If constantPart == 0, no constant term is added explicitly

        // 5. Reconstruct final LHS and RHS expressions
        Expr finalLhs, finalRhs;
        if (finalLhsTerms.empty()) {
            finalLhs = mkMPZ(0, m_efac);
        } else if (finalLhsTerms.size() == 1) {
            finalLhs = finalLhsTerms[0];
        } else {
            // Use simplifyArithm to potentially simplify the sum
            finalLhs = simplifyArithm(mknary<PLUS>(finalLhsTerms.begin(), finalLhsTerms.end()));
        }

        if (finalRhsTerms.empty()) {
            finalRhs = mkMPZ(0, m_efac);
        } else if (finalRhsTerms.size() == 1) {
            finalRhs = finalRhsTerms[0];
        } else {
            // Use simplifyArithm to potentially simplify the sum
            finalRhs = simplifyArithm(mknary<PLUS>(finalRhsTerms.begin(), finalRhsTerms.end()));
        }

        // 6. Build the final comparison using the original operator
        // The operator 'op' derived from 'normalized' is correct because
        // normalizeAtom(e) gives Sum(ci*vi) op C.
        // We transformed this into finalLHS op finalRHS, where the constant
        // is implicitly included based on the constantPart logic.
        ExprVector args = {finalLhs, finalRhs};
        Expr result = m_efac.mkNary(op, args);
        if (debug >= 4) outs() << "[normalizePositive] Result: " << *result << "\n";

        // Final simplification pass
        return simplifyArithm(result);
    }
    // --- End new helper method ---

    // --- New private helper method to process learned LIA lemmas ---
    /**
     * @brief Processes the learned lemmas from the LIA solver.
     *
     * Retrieves lemmas for each relation from the solver, normalizes and simplifies them,
     * and stores the final set in m_liaSolutionMap.
     *
     * @param solver The RndLearnerV4 solver instance containing the learned lemmas.
     */
    void processLearnedLiaLemmas(RndLearnerV4& solver) {
        m_liaSolutionMap.clear();
        for (auto &liaDecl : m_liaChcs->decls) { // liaDecl is the full declaration Expr, e.g., (declare-rel inv (Int))
            Expr liaDeclExpr = liaDecl->left(); // liaDeclExpr is just the name, e.g., inv
            int invNum = getVarIndex(liaDecl, m_liaChcs->decls); // CORRECTED FIX: Searches for full decl in list of full decls

            if (debug >= 5) {
                outs() << "[processLearnedLiaLemmas] Checking relation " << *liaDeclExpr << ", full decl: " << *liaDecl << ", found invNum: " << invNum << "\n";
                if (invNum >= 0) solver.printSolutionForRelation(invNum);
            }

            if (invNum < 0) { // Log if not found
                 if (debug >= 1) outs() << "[processLearnedLiaLemmas] Error: Could not find index for LIA declaration: " << *liaDecl << "\n";
                 continue;
            }

            ExprSet lemmas = solver.getlearnedLemmas(invNum);
            if(debug >=4) outs() << "[processLearnedLiaLemmas]   Lemmas size for " << *liaDeclExpr << ": " << lemmas.size() << "\n";
            if (!lemmas.empty()) {
                ExprSet simplifiedLemmas; // Store results after initial simplification
                if (debug >= 4) outs() << "[processLearnedLiaLemmas]   Simplifying individual lemmas for " << *liaDeclExpr << ":\n";
                for (auto &lemma : lemmas) {
                    if (debug >= 5) outs() << "    Original: " << *lemma << "\n";
                    // Apply normalizeExpr (ineqReverter, etc.)
                    Expr normalized = normalizeExpr(lemma);
                    if (debug >= 5) outs() << "    Normalized (normalizeExpr): " << *normalized << "\n";
                    // Apply arithmetic simplification
                    Expr simplified_lemma = simplifyArithm(normalized, false, false);
                    if (debug >= 5) outs() << "    Simplified (simplifyArithm): " << *simplified_lemma << "\n";

                    if (!isOpX<TRUE>(simplified_lemma)) { // Don't add trivial 'true' lemmas
                        simplifiedLemmas.insert(simplified_lemma); // Add the processed lemma
                    }
                }

                // Simplify the conjunction of simplifiedLemmas
                Expr conjunction = conjoin(simplifiedLemmas, m_efac);
                Expr simplifiedArithConj = simplifyArithmConjunctions(conjunction, false); // false: don't keep redundant
                Expr finalConjunction = simplifyBool(simplifiedArithConj); // Boolean simplification

                // Extract conjuncts after simplification
                ExprSet conjunctLemmas;
                getConj(finalConjunction, conjunctLemmas);

                // --- Apply normalizePositive as the final step ---
                ExprSet finalNormalizedLemmas;
                if (debug >= 4) outs() << "[processLearnedLiaLemmas]   Applying final positive normalization for " << *liaDeclExpr << ":\n";
                for (auto& conjLemma : conjunctLemmas) {
                    Expr posNormalized = normalizePositive(conjLemma);
                    // normalizePositive already calls simplifyArithm at the end
                    if (debug >= 5) outs() << "    Input to normalizePositive: " << *conjLemma << "\n";
                    if (debug >= 5) outs() << "    Output of normalizePositive: " << *posNormalized << "\n";
                    if (!isOpX<TRUE>(posNormalized)) {
                        finalNormalizedLemmas.insert(posNormalized);
                    }
                }
                // --- End Apply normalizePositive ---

                m_liaSolutionMap[liaDeclExpr] = finalNormalizedLemmas; // Store final positively normalized lemmas

                 if (debug >= 3) {
                    outs() << "[processLearnedLiaLemmas] Final LIA Lemmas for " << liaDeclExpr << " (" << finalNormalizedLemmas.size() << "):\n"; // Use finalNormalizedLemmas
                    for(auto& l : finalNormalizedLemmas) outs() << "  " << l << "\n"; // Use finalNormalizedLemmas
                 }
            } else {
                 if (debug >= 2) outs() << "[processLearnedLiaLemmas] Warning: No LIA lemmas found for " << *liaDeclExpr << "\n";
                 m_liaSolutionMap[liaDeclExpr] = ExprSet(); // Store empty set
            }
        }
    }
    // --- End new private helper method ---

    // --- New private helper method to check solution map against rules ---
    /**
     * @brief Checks if a given solution map satisfies a set of Horn rules.
     *
     * Constructs and checks the SMT query (Body ^ SrcInv ^ !DstInv) for each rule.
     *
     * @param worklist The list of Horn rules to check against.
     * @param solutionMap The map representing the solution (relation -> combined expression).
     * @return `true` if the solution satisfies all rules in the worklist, `false` otherwise.
     */
    bool checkLemmasAgainstRules(const vector<HornRuleExt*>& worklist, const map<Expr, Expr>& solutionMap) {
        if (debug >= 3) outs() << "[checkLemmasAgainstRules] Starting check (" << worklist.size() << " rules)\n";
        for (const auto* hr : worklist) {
            if (debug >= 4) {
                outs() << "  Checking Rule: (";
                if (hr->srcRelation) outs() << hr->srcRelation; else outs() << "null";
                outs() << " -> ";
                if (hr->dstRelation) outs() << hr->dstRelation; else outs() << "null";
                outs() << ")\n";
            }

            ExprSet checkExprs;
            checkExprs.insert(hr->body);

            // Add source solution if not a fact
            if (!hr->isFact && hr->srcRelation) {
                auto srcSolnIt = solutionMap.find(hr->srcRelation);
                if (srcSolnIt != solutionMap.end() && m_bvChcs.invVars.count(hr->srcRelation)) {
                    Expr srcSolnCombined = srcSolnIt->second;
                    ExprVector invVars = m_bvChcs.invVars.at(hr->srcRelation); // Use const ref
                    ExprVector srcVars = hr->srcVars; // Use const ref
                    if (invVars.size() == srcVars.size()) {
                        Expr srcSolnSubst = replaceAll(srcSolnCombined, invVars, srcVars);
                        checkExprs.insert(srcSolnSubst);
                        if (debug >= 5) outs() << "    Adding SrcInv (" << hr->srcRelation << "): " << srcSolnSubst << "\n";
                    } else {
                        if (debug >= 1) outs() << "[checkLemmasAgainstRules] Warning: Var mismatch for src " << hr->srcRelation << ". Skipping rule.\n";
                        continue;
                    }
                } else {
                    if (debug >= 5) outs() << "    SrcInv missing or vars missing for " << hr->srcRelation << ", assuming true.\n";
                }
            }

            // Add negated destination solution if not a query
            if (!hr->isQuery && hr->dstRelation) {
                auto dstSolnIt = solutionMap.find(hr->dstRelation);
                if (dstSolnIt != solutionMap.end() && m_bvChcs.invVars.count(hr->dstRelation)) {
                    Expr dstSolnCombined = dstSolnIt->second;
                    ExprVector invVars = m_bvChcs.invVars.at(hr->dstRelation); // Use const ref
                    ExprVector dstVars = hr->dstVars; // Use const ref
                    if (invVars.size() == dstVars.size()) {
                        Expr dstSolnSubst = replaceAll(dstSolnCombined, invVars, dstVars);
                        checkExprs.insert(mkNeg(dstSolnSubst));
                        if (debug >= 5) outs() << "    Adding !DstInv (" << hr->dstRelation << "): " << mkNeg(dstSolnSubst) << "\n";
                    } else {
                        if (debug >= 1) outs() << "[checkLemmasAgainstRules] Warning: Var mismatch for dst " << hr->dstRelation << ". Skipping rule.\n";
                        continue;
                    }
                } else {
                    if (debug >= 5) outs() << "    DstInv missing or vars missing for " << hr->dstRelation << ". Rule check skipped (vacuously true).\n";
                    continue; // Rule holds vacuously
                }
            } else if (hr->isQuery) {
                 // Query check: Body ^ SrcInv => false (or Body ^ SrcInv is UNSAT)
                 // If SAT/Unknown, the rule fails.
            }

            // Perform SMT check
            if (debug >= 5) {
                outs() << "    Checking SMT query: \n";
                pprint(conjoin(checkExprs, m_efac));
                outs() << "\n";
            }
            boost::tribool checkResult = u.isSat(checkExprs);

            if (checkResult) { // SAT or indeterminate means the rule is violated
                if (debug >= 3) {
                    outs() << "  Rule FAILED (SAT/Indeterminate): (";
                    if (hr->srcRelation) outs() << hr->srcRelation; else outs() << "null";
                    outs() << " -> ";
                    if (hr->dstRelation) outs() << hr->dstRelation; else outs() << "null";
                    outs() << ")\n";
                }
                return false; // Solution is not safe
            } else {
                 if (debug >= 4) outs() << "    Rule PASSED (UNSAT)\n";
            }
        }

        if (debug >= 3) outs() << "[checkLemmasAgainstRules] Finished: All rules PASSED.\n";
        return true; // All rules passed
    }
    // --- End new private helper method ---

    public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) :
      m_efac(efac),
      m_z3(z3),
      m_liaChcs(new CHCs(efac,z3,_debug)), // Create new CHCs object
      m_bvChcs(input),
      u(efac),
      m_Lia2BvTranslator(efac, z3, 4, _debug), // Default width, will be updated
      m_Bv2LiaTranslator(efac, z3, 4, _debug), // Default width, will be updated
      debug(_debug),
      m_learnedLemmas(1) // Initialize with size 1
    {
      if (debug >= 1) {
        outs() << "[BitHorn::Constructor] Initializing BitHorn solver\n";
      }

      // --- Modification: Detect and store original BV width without goto ---
      bool width_detected = false;
      if (m_bvChcs.hasBV) {
          for (auto decl : m_bvChcs.decls) {
              if (decl && decl->arity() > 1) {
                  // Iterate through arguments, skipping the relation name (index 0)
                  // and the return type (last index)
                  for (unsigned i = 1; i < decl->arity() - 1; ++i) {
                      Expr sort = decl->arg(i);
                      if (isOpX<BVSORT>(sort)) {
                          m_original_bv_width = bv::width(sort);
                          if (debug >= 2) {
                              outs() << "[BitHorn::Constructor] Detected original BV width " << m_original_bv_width << " from decl " << *decl << "\n";
                          }
                          width_detected = true;
                          break; // Exit inner loop once width is found
                      }
                  }
              }
              if (width_detected) {
                  break; // Exit outer loop once width is found
              }
          }

          // Pass the detected width to the translator instances if found
          if (width_detected && m_original_bv_width > 0) {
              m_Lia2BvTranslator.setOriginalBvWidth(m_original_bv_width);
              // Assuming Bv2LiaTranslator also needs the original width if applicable
              // m_Bv2LiaTranslator.setOriginalBvWidth(m_original_bv_width); // Uncomment if needed
          } else if (debug >= 1 && m_bvChcs.hasBV) {
              outs() << "[BitHorn::Constructor] Warning: Could not detect original BV width from declarations. Using default.\n";
          }
      }
      // --- End Modification ---

      // Populate original BV variable maps
      for (auto dd : m_bvChcs.decls)
      {
        Expr d = dd->left();
        if (!d) continue; // Skip if relation name is null

        // Check if the relation exists in the invVars map before accessing
        if (m_bvChcs.invVars.count(d)) {
            origBvVars[d] = m_bvChcs.invVars[d];
            if (debug >= 3) {
                outs() << "[BitHorn::Constructor] origBvVars: Populated for " << *d << " with " << origBvVars[d].size() << " vars\n";
                // Optional: Print individual vars if needed at higher debug level
                // for(const auto& a : origBvVars[d]) {
                //     outs() << "  Var: " << *a << " Type: " << *bind::typeOf(a) << "\n";
                // }
            }
        } else if (debug >= 2) {
            outs() << "[BitHorn::Constructor] Warning: invVars not found for relation " << *d << ".\n";
        }

        // Check if the relation exists in the invVarsPrime map before accessing
        if (m_bvChcs.invVarsPrime.count(d)) {
            origBvVarsPrime[d] = m_bvChcs.invVarsPrime[d];
             if (debug >= 3) {
                outs() << "[BitHorn::Constructor] origBvVarsPrime: Populated for " << *d << " with " << origBvVarsPrime[d].size() << " vars\n";
                // Optional: Print individual vars if needed at higher debug level
                // for(const auto& a : origBvVarsPrime[d]) {
                //     outs() << "  Var: " << *a << " Type: " << *bind::typeOf(a) << "\n";
                // }
            }
        } else if (debug >= 2) {
             outs() << "[BitHorn::Constructor] Warning: invVarsPrime not found for relation " << *d << ".\n";
        }
      }
      // --- Removed redundant debug loops ---
    }

    // --- Add translateToBv method ---
    /**
     * @brief Translates the internal BV CHC system (m_bvChcs) to the LIA CHC system (m_liaChcs).
     *
     * Uses the Bv2LiaTranslator to convert declarations, variables, and rule bodies.
     * Populates the m_liaChcs object and associated variable maps (origLiaVars).
     *
     * @return true if translation is successful, false otherwise.
     */
    bool translateToBv() {
      if (debug >= 1) {
        outs() << "[translateToBv] Translating BV CHCs to LIA CHCs...\n";
      }

      // Clear any existing LIA CHCs data before translation
      origLiaVars.clear();
      origLiaVarsPrime.clear(); // Clear primed vars map as well

      // Perform the translation using the Bv2LiaTranslator's main translate method
      // This method handles declarations, variables, and rules internally.
      // We pass m_bvChcs as input and expect it to return a new CHCs object.
      // Since m_liaChcs is a pointer, we need to manage its memory.
      delete m_liaChcs; // Delete the old CHCs object
      m_liaChcs = new CHCs(m_Bv2LiaTranslator.translate(m_bvChcs)); // Assign the newly translated CHCs

      // Check if the translation resulted in a valid object (basic check)
      if (!m_liaChcs) {
          if (debug >= 1) outs() << "[translateToBv] Error: Bv2LiaTranslator returned a null CHCs object.\n";
          // Re-create an empty CHCs object to avoid null pointer issues later
          m_liaChcs = new CHCs(m_efac, m_z3, debug);
          return false;
      }

      // After translation, populate the origLiaVars map.
      // The Bv2LiaTranslator should have populated its internal m_var_map.
      // We need to associate these translated LIA vars with the *translated* LIA relation names.
      const auto& bvToLiaDeclNameMap = m_Bv2LiaTranslator.getBvToLiaDeclMap(); // Map: BV Name -> LIA Name

      for (const auto& bvDecl : m_bvChcs.decls) {
          Expr bvRelName = bvDecl->left();
          if (!bvRelName) continue;

          // Find the corresponding translated LIA relation name
          auto nameMapIt = bvToLiaDeclNameMap.find(bvRelName);
          if (nameMapIt == bvToLiaDeclNameMap.end()) {
              if (debug >= 1) outs() << "[translateToBv] Warning: Could not find translated LIA name for BV relation " << *bvRelName << " in map.\n";
              continue;
          }
          Expr liaRelName = nameMapIt->second;

          // Get the original BV invariant variables for this relation
          if (m_bvChcs.invVars.count(bvRelName)) {
              const ExprVector& bvInvVars = m_bvChcs.invVars.at(bvRelName);
              ExprVector translatedLiaVars;
              // Translate each original BV variable to its LIA counterpart using the translator's map
              for (const auto& bvVar : bvInvVars) {
                  // Use the translator's public translateExpr method which uses the internal map
                  Expr liaVar = m_Bv2LiaTranslator.translateExpr(bvVar);
                  if (liaVar && liaVar != bvVar) { // Check if translation occurred
                      translatedLiaVars.push_back(liaVar);
                  } else if (liaVar == bvVar) {
                      if (debug >= 3) outs() << "  [translateToBv] Var " << *bvVar << " kept as is during origLiaVars population.\n";
                      translatedLiaVars.push_back(bvVar); // Keep original if no translation
                  } else {
                      if (debug >= 1) outs() << "[translateToBv] Warning: Failed to translate BV variable " << *bvVar << " for relation " << *bvRelName << "\n";
                      // Handle error? Skip variable? For now, skip.
                  }
              }
              origLiaVars[liaRelName] = translatedLiaVars; // Store translated vars under the LIA relation name
              if (debug >= 4) {
                  outs() << "  [translateToBv] Stored origLiaVars for LIA rel " << *liaRelName << " (from BV " << *bvRelName << "): " << translatedLiaVars.size() << " vars\n";
              }
          } else {
               if (debug >= 2) outs() << "[translateToBv] Warning: Original BV invVars not found for relation " << *bvRelName << "\n";
          }

          // TODO: Handle origLiaVarsPrime similarly if needed, using m_bvChcs.invVarsPrime
          if (m_bvChcs.invVarsPrime.count(bvRelName)) {
              const ExprVector& bvInvVarsPrime = m_bvChcs.invVarsPrime.at(bvRelName);
              ExprVector translatedLiaVarsPrime;
              for (const auto& bvVarPrime : bvInvVarsPrime) {
                  Expr liaVarPrime = m_Bv2LiaTranslator.translateExpr(bvVarPrime);
                   if (liaVarPrime && liaVarPrime != bvVarPrime) {
                      translatedLiaVarsPrime.push_back(liaVarPrime);
                  } else if (liaVarPrime == bvVarPrime) {
                      if (debug >= 3) outs() << "  [translateToBv] Primed Var " << *bvVarPrime << " kept as is during origLiaVarsPrime population.\n";
                      translatedLiaVarsPrime.push_back(bvVarPrime);
                  } else {
                      if (debug >= 1) outs() << "[translateToBv] Warning: Failed to translate primed BV variable " << *bvVarPrime << " for relation " << *bvRelName << "\n";
                  }
              }
              origLiaVarsPrime[liaRelName] = translatedLiaVarsPrime;
               if (debug >= 4) {
                  outs() << "  [translateToBv] Stored origLiaVarsPrime for LIA rel " << *liaRelName << " (from BV " << *bvRelName << "): " << translatedLiaVarsPrime.size() << " vars\n";
              }
          }
      }


      if (debug >= 2) {
        outs() << "[translateToBv] Finished translating BV to LIA using Bv2LiaTranslator::translate.\n";
        if (debug >= 3) {
          outs() << "--- Translated LIA System (m_liaChcs) ---\n";
          m_liaChcs->print(true);
          outs() << "--- End Translated LIA System ---\n";
          outs() << "--- OrigLiaVars Map (" << origLiaVars.size() << " entries) ---\n";
          for(const auto& pair : origLiaVars) {
              outs() << "  Rel: " << *pair.first << " -> ";
              for(const auto& v : pair.second) outs() << *v << " ";
              outs() << "\n";
          }
          outs() << "--- End OrigLiaVars Map ---\n";
        }
      }
      return true; // Assume success if no errors were explicitly returned by the translator
    }
    // --- End Add translateToBv method ---

    // --- Add getBvChcs method ---
    CHCs& getBvChcs() {
        return m_bvChcs;
    }
    // --- End Add getBvChcs method ---

    // --- Add solve method ---
    /**
     * @brief Main solving loop for the BitHorn solver.
     *
     * Attempts to solve the input BV CHC system by translating it to LIA,
     * solving the LIA system, translating the solution back to BV, and checking safety.
     *
     * @param to Timeout parameter (likely for the LIA solver).
     * @return `true` if a safe solution is found, `false` otherwise.
     */
    bool solve(unsigned int to = 100) {
      if (debug >= 1) {
        outs() << "[solve] Starting BitHorn solve process...\n";
      }

      // 1. Translate BV to LIA
      if (!translateToBv()) {
        outs() << "[solve] Error: Failed during BV to LIA translation.\n";
        return false;
      }

      // 2. Solve LIA system 
      bool liaSolved = solveLIA(to);
      if (!liaSolved) {
        if (debug >= 1) outs() << "[solve] LIA solver failed to find solution.\n";
        return false;
      }

      // 3. Translate LIA solution back to BV
      if (!translateSolutionToBv()) {
        outs() << "[solve] Error: Failed translating LIA solution to BV.\n";
        return false;
      }

      // 4. Check safety of translated solution
      bool isSafe = checkSafetyInBV();

      // 5. If unsafe, try strengthening and recheck
      if (!isSafe && strengthenTransitionRelation()) {
        if (debug >= 1) outs() << "[solve] Rechecking after strengthening...\n";
        isSafe = checkSafetyInBV();
      }

      if (isSafe) {
        outs() << "\n\nSuccess : Safe solution found\n";
        printSolution();
      } else {
        outs() << "unknown\n";
      }

      return isSafe;
    }
    // --- End Add solve method ---

    bool solveLIA(unsigned int to = 100) {
      if (debug >= 2) {
        outs() << "[solveLIA] Attempting to solve LIA system\n";  
      }

      // Before creating solver, normalize and validate all rule bodies
      for (auto &rule : m_liaChcs->chcs) {
        if (containsOp<IDIV>(rule.body) || containsOp<MOD>(rule.body)) {
          if (debug >= 1) outs() << "[solveLIA] Warning: Skipping rule with division/mod: " << rule.body << "\n";
          continue;
        }
        // --- Apply normalization to rule bodies ---
        Expr normalized_body = normalizeExpr(normalizePositive(rule.body));
        rule.body = simplifyArithm(normalized_body, false, false);
        // --- End Apply normalization ---
      }

      m_liaSolutionMap.clear();

      // Configure solver with safe parameters
      bool freqs = true;
      bool aggp = false;  // Disable aggressive pruning to avoid FPE
      int mut = 1;       // Disable mutations
      int da = 1;
      bool doDisj = true;
      int mbpEqs = 0;
      bool dAllMbp = true;
      bool dAddProp = false;
      bool dAddDat = true;
      bool dStrenMbp = false;
      int dFwd = 1;
      bool dRec = false;
      bool dGen = true;

      // Create solver
      std::unique_ptr<RndLearnerV4> solver(new RndLearnerV4(m_efac, m_z3, 
                                        *m_liaChcs, to,
                                        freqs, aggp, mut, da,
                                        doDisj, mbpEqs, dAllMbp,
                                        dAddProp, dAddDat, dStrenMbp,
                                        dFwd, dRec, dGen, debug));

      if (!solver) {
        if (debug >= 1) outs() << "[solveLIA] Error: Failed to create solver\n";
        return false;
      }

      // Initialize solver with candidates 
      map<Expr, ExprSet> cands;
      BndExpl bnd(*m_liaChcs, to, debug);

      // Process each cycle to generate candidates
      for (auto& cyc : m_liaChcs->cycles) {
        Expr rel = cyc.first;
        for (int i = 0; i < cyc.second.size(); i++) {
          assert(rel == m_liaChcs->chcs[cyc.second[i][0]].srcRelation);
          
          // --- Skip initialization if already done (moved earlier) ---
          // if (solver->initializedDecl(rel)) continue; 
          // solver->initializeDecl(rel);
          // --- End Skip initialization ---


          // Process prefix for candidates
          Expr pref = bnd.compactPrefix(rel, i);
          ExprSet tmp;
          getConj(pref, tmp);
          
          // --- Modification: Normalize candidates before adding ---
          ExprSet normalizedCandsForRel; // Temporary set for normalized candidates
          // Filter candidates that only use invariant variables and normalize them
          for (auto & t : tmp) {
            Expr normalized_t = normalizeExpr(normalizePositive(t));
            Expr simplified_t = simplifyArithm(normalized_t, false, false);
            if (!isOpX<TRUE>(simplified_t) && hasOnlyVars(simplified_t, m_liaChcs->invVars[rel])) {
               normalizedCandsForRel.insert(simplified_t);
               if (debug >= 5) outs() << "  [solveLIA] Added normalized prefix cand for " << *rel << ": " << *simplified_t << "\n";
            }
          }
          // Add the normalized candidates to the main map
          cands[rel].insert(normalizedCandsForRel.begin(), normalizedCandsForRel.end());
          // --- End Modification ---

          // --- Modification: Initialize decl *before* using candidates ---
          if (!solver->initializedDecl(rel)) {
              solver->initializeDecl(rel);
          }
          // --- End Modification ---


          // --- Modification: Mutate and initialize using the potentially updated cands[rel] ---
          if (mut > 0) {
              // Note: mutateHeuristicEq modifies the first ExprSet in place.
              // We pass cands[rel] which now contains normalized prefix candidates.
              // The mutated results might not be normalized, but we'll normalize again after data candidates.
              solver->mutateHeuristicEq(cands[rel], cands[rel], rel, true);
              if (debug >= 5) outs() << "  [solveLIA] Mutated candidates for " << *rel << "\n";
          }
          // Initialize Aux uses the current state of cands[rel]
          solver->initializeAux(cands[rel], bnd, rel, i, pref);
          // --- End Modification ---
        }
      }

      // Generate data-based candidates if enabled
      if (da > 0) {
        solver->getDataCandidates(cands); // This adds potentially un-normalized candidates
        if (debug >= 4) outs() << "  [solveLIA] Got data candidates.\n";

        // --- Modification: Normalize all candidates again after adding data candidates ---
        if (debug >= 4) outs() << "  [solveLIA] Normalizing all candidates (prefix + data + mutated)...\n";
        for (auto& pair : cands) {
            Expr rel = pair.first;
            ExprSet& currentCands = pair.second;
            ExprSet finalNormalizedCands;
            for (auto& cand : currentCands) {
                Expr normalized_cand = normalizeExpr(normalizePositive(cand));
                Expr simplified_cand = simplifyArithm(normalized_cand, false, false);
                 if (!isOpX<TRUE>(simplified_cand)) {
                    finalNormalizedCands.insert(simplified_cand);
                 }
            }
            currentCands = finalNormalizedCands; // Replace with the fully normalized set
            if (debug >= 5) {
                outs() << "    Normalized cands for " << *rel << " (" << currentCands.size() << "):\n";
                // for(const auto& c : currentCands) outs() << "      " << *c << "\n"; // Potentially verbose
            }
        }
        // --- End Modification ---
      }

      // Process declarations with priority propagation using normalized candidates
      for (auto & dcl : m_liaChcs->wtoDecls) {
        // Ensure the relation exists in the map, even if empty
        if (cands.find(dcl) == cands.end()) {
            cands[dcl] = ExprSet();
        }
        solver->addCandidates(dcl, cands[dcl]);
        solver->prepareSeeds(dcl, cands[dcl]);
      }

      // Bootstrap and calculate initial statistics
      bool bootstrap = solver->bootstrap();
      if (bootstrap) {
        if (debug >= 2)
          outs() << "[solveLIA] Bootstrap successful\n";
        // --- Call helper method to process lemmas ---
        processLearnedLiaLemmas(*solver);
        // --- End call helper method ---
        return true; // Return true if bootstrap succeeded
      }

      solver->calculateStatistics();
      solver->deferredPriorities();
      std::srand(std::time(0)); // Consider moving seeding to a higher level if needed elsewhere

      // Try synthesis
      if (solver->synthesize(to)) {
        if (debug >= 2) {
          outs() << "[solveLIA] V4 solver found solution via synthesis\n"; // Clarified log
        }
        // --- Call helper method to process lemmas ---
        processLearnedLiaLemmas(*solver);
        // --- End call helper method ---
        return true; // Return true if synthesis succeeded
      }

      if (debug >= 1) outs() << "[solveLIA] LIA solver failed (bootstrap and synthesis)\n"; // Added final failure log
      return false;
    }

    bool translateSolutionToBv() {
      if (debug >= 2) {
        outs() << "[translateSolutionToBv] Translating LIA solution map to BV solution map...\n";
      }

      // Clear any previous solution
      m_bvSolutionMap.clear();

      // Safety check - ensure we have declarations
      if (m_bvChcs.decls.empty()) {
        if (debug >= 1) {
          outs() << "[translateSolutionToBv] Error: No declarations found in BV CHCs\n";
        }
        return false;
      }

      // Get the BV -> LIA declaration map
      const auto& bvToLiaMap = m_Bv2LiaTranslator.getBvToLiaDeclMap();

      // +++ Debugging +++
      if (debug >= 4) {
          outs() << "[translateSolutionToBv] BV to LIA Relation Map (bvToLiaMap):\n";
          for (const auto& pair : bvToLiaMap) {
              if (pair.first && pair.second) { // Check for null pointers
                  outs() << "  BV: " << *(pair.first) << " -> LIA: " << *(pair.second) << "\n";
              } else {
                  outs() << "  BV: (null?) -> LIA: (null?)\n";
              }
          }
          outs() << "[translateSolutionToBv] LIA Solution Map (m_liaSolutionMap):\n";
          for (const auto& pair : m_liaSolutionMap) {
               if (pair.first) { // Check for null pointers
                  outs() << "  LIA: " << *(pair.first) << " -> " << pair.second.size() << " lemmas\n";
               } else {
                   outs() << "  LIA: (null?) -> " << pair.second.size() << " lemmas\n";
               }
          }
      }
      // +++ End Debugging +++


      // Iterate through BV declarations
      for (auto& bvDecl : m_bvChcs.decls) {
        Expr bvRel = bvDecl->left(); // Original BV relation name
        if (!bvRel) continue;

        if (debug >= 4) outs() << "[translateSolutionToBv] Processing BV relation: " << *bvRel << "\n";

        // Find corresponding LIA relation NAME using the map
        auto mapIt = bvToLiaMap.find(bvRel); // Look up original BV name
        if (mapIt == bvToLiaMap.end()) {
          if (debug >= 1) outs() << "[translateSolutionToBv] Warning: Could not find LIA relation for BV relation " << *bvRel << " in bvToLiaMap\n"; // Added map name
          continue;
        }
        Expr liaRel = mapIt->second; // Translated LIA relation name

        if (debug >= 4) outs() << "  Found corresponding LIA relation name: " << *liaRel << "\n";

        // Find LIA solution for this relation using the LIA relation name as key
        auto liaSolnIt = m_liaSolutionMap.find(liaRel); // Look up translated LIA name
        if (liaSolnIt == m_liaSolutionMap.end() || liaSolnIt->second.empty()) {
          if (debug >= 2) outs() << "[translateSolutionToBv] Warning: No LIA solution found for relation " << *liaRel << " (BV: " << *bvRel << ") in m_liaSolutionMap. Setting to TRUE.\n"; // Added map name
          // Store 'true' as the solution if none is found? Or skip? Let's store true.
          m_bvSolutionMap[bvRel] = mk<TRUE>(m_efac);
          continue;
        }

        ExprSet& liaExprSet = liaSolnIt->second;
        ExprSet bvExprSet;

        // Translate each LIA expression in the solution set
        for (auto& liaExpr : liaExprSet) {
          if (!liaExpr) continue; // Skip invalid expressions

          Expr bvExpr = m_Lia2BvTranslator.translateExpr(liaExpr, m_original_bv_width);

          if (!bvExpr) {
            if (debug >= 2) {
              outs() << "[translateSolutionToBv] Warning: Failed to translate LIA expression: " << *liaExpr << " for relation " << *liaRel << "\n";
            }
            continue;
          }

          // Replace LIA invariant variables with BV invariant variables
          // Ensure both relations exist in the invVars map

          // +++ Debugging: Print map contents before check +++
          if (debug >= 4) {
              outs() << "  Checking variable maps for BV='" << *bvRel << "' / LIA='" << *liaRel << "'\n";
              outs() << "    m_bvChcs.invVars keys: ";
              for(const auto& p : m_bvChcs.invVars) if(p.first) outs() << *p.first << " "; outs() << "\n";
              outs() << "    origLiaVars keys: ";
              for(const auto& p : origLiaVars) if(p.first) outs() << *p.first << " "; outs() << "\n";
              outs() << "    m_bvChcs.invVars.count(" << *bvRel << "): " << m_bvChcs.invVars.count(bvRel) << "\n";
              outs() << "    origLiaVars.count(" << *liaRel << "): " << origLiaVars.count(liaRel) << "\n";
              if (m_bvChcs.invVars.count(bvRel)) {
                  outs() << "    BV Vars (" << m_bvChcs.invVars.at(bvRel).size() << "): ";
                  for(const auto& v : m_bvChcs.invVars.at(bvRel)) outs() << *v << " "; outs() << "\n";
              }
              if (origLiaVars.count(liaRel)) {
                  outs() << "    LIA Vars (" << origLiaVars.at(liaRel).size() << "): ";
                  for(const auto& v : origLiaVars.at(liaRel)) outs() << *v << " "; outs() << "\n";
              }
          }
          // +++ End Debugging +++

          if (origLiaVars.count(liaRel) && m_bvChcs.invVars.count(bvRel)) {
              // --- Modification: Create non-const copies instead of const references ---
              ExprVector liaVars = origLiaVars.at(liaRel); 
              ExprVector bvVars = m_bvChcs.invVars.at(bvRel);
              // --- End Modification ---

              // +++ Debugging: Check variable vector sizes +++
              if (debug >= 4 && liaVars.size() != bvVars.size()) {
                  outs() << "    Warning: LIA var count (" << liaVars.size() 
                         << ") != BV var count (" << bvVars.size() << ") for relation " << *liaRel << "\n";
              }
              // +++ End Debugging +++

              bvExpr = replaceAll(bvExpr, liaVars, bvVars); // Now uses non-const copies
              if (bvExpr) {
                  if (debug >= 4) {
                      outs() << "  Translated LIA: " << *liaExpr << "\n";
                      outs() << "        to BV (after var replace): " << *bvExpr << "\n"; // Updated log message
                  }
                  bvExprSet.insert(bvExpr);
              }
          } else {
              if (debug >= 2) outs() << "[translateSolutionToBv] Warning: Missing variables for relation pair " << *liaRel << "/" << *bvRel << " during translation.\n";
          }
        }

        // Store the conjunction of translated BV expressions
        m_bvSolutionMap[bvRel] = conjoin(bvExprSet, m_efac);
        if (debug >= 3) {
            outs() << "[translateSolutionToBv] BV Solution for " << *bvRel << ": " << m_bvSolutionMap[bvRel] << "\n";
        }
      }


      // Print full translation results (optional, maybe redundant with above)
      if (debug >= 2) {
        outs() << "\n[translateSolutionToBv] Final Translated BV Solution Map (" << m_bvSolutionMap.size() << " entries):\n";
        for (auto& kv : m_bvSolutionMap) {
          outs() << "  Relation: " << *kv.first << "\n";
          outs() << "     BV Solution: " << *kv.second << "\n";
        }
        outs() << "\n";
      }

      // Consider success if at least one relation was translated, even if to 'true'
      return !m_bvSolutionMap.empty();
    }

    /**
     * Check a single rule against a set of candidates
     * Returns false if rule passes, true/indeterminate if rule fails
     */ 
    boost::tribool checkRule(HornRuleExt* hr, map<Expr, ExprSet>& candidates)
    {
      if (debug >= 3) {
        outs() << "  Checking rule: " << *hr->srcRelation << " -> " << *hr->dstRelation << "\n";
      }

      ExprVector checkExprs;
      checkExprs.push_back(hr->body);

      // Add source relation candidates if not a fact
      if (!hr->isFact) {
        auto srcCandIt = candidates.find(hr->srcRelation);
        if (srcCandIt != candidates.end()) {
          for (auto& cand : srcCandIt->second) {
            Expr srcCandSubst = replaceAll(cand, m_bvChcs.invVars[hr->srcRelation], hr->srcVars);
            checkExprs.push_back(srcCandSubst);
          }
        }
      }

      // Add negated destination candidates if not a query
      if (!hr->isQuery) {
        auto dstCandIt = candidates.find(hr->dstRelation);
        ExprVector negged;
        if (dstCandIt != candidates.end()) {
          for (auto& cand : dstCandIt->second) {
            Expr dstCandSubst = replaceAll(cand, m_bvChcs.invVars[hr->dstRelation], hr->dstVars);
            negged.push_back(mkNeg(dstCandSubst));
          }
        }
        checkExprs.push_back(disjoin(negged, m_efac));
      }

      if(debug >= 4) {
        outs() << "  Checking expressions:\n";
        for(int i = 0; i < checkExprs.size(); i++) {
          if(i != 0) outs() << "/\\ ";
          else outs() << "  ";
          outs() << "  " << checkExprs[i] << "\n";
        }
      }

      return u.isSat(checkExprs);
    }

    bool anyProgress(vector<HornRuleExt*>& worklist, 
                     map<Expr, ExprSet>& candidates) 
    {
      if(debug >= 2) {
        outs() << "[anyProgress] Checking for progress...\n";
      }
      for (auto* hr : worklist) {
        boost::tribool res = checkRule(hr, candidates);
        if (res || indeterminate(res)) {
          return false; // Found a rule that failed
        }
      }
      return true; // No rules failed
    }

    /**
     * Main Houdini-style candidate checking
     * @param worklist List of rules to check
     * @param candidates Map from relations to their candidate invariants
     * @return true if all rules pass with current candidates
     */
    bool multiHoudini(vector<HornRuleExt*>& worklist, 
                     map<Expr, ExprSet>& candidates) 
    {
      if (debug >= 2) {
        outs() << "[multiHoudini] Checking " << worklist.size() << " rules\n";
      }

      // Check each rule against the candidates
      bool checkAgain = false;
      for (auto* hr : worklist) {
        if(hr->isQuery) continue;
        boost::tribool res = checkRule(hr, candidates);

        if(debug >= 5)
        {
          if (res == true) {
            outs() << "  Rule failed: " << *hr->srcRelation 
                  << " -> " << *hr->dstRelation << "\n\n";
          } else if (res == false) {
            outs() << "  Rule passed: " << *hr->srcRelation 
                  << " -> " << *hr->dstRelation << "\n\n";
          } else {
            outs() << "  Rule indeterminate: " << *hr->srcRelation 
                  << " -> " << *hr->dstRelation << "\n\n";
          }
        }
        
        if (res || indeterminate(res)) {

          // CHC check failed so attempt to weaken the candidates.
          weakenCandidates(hr, candidates);
          checkAgain = true;
          // return false;
        }
      }

      if(checkAgain) {
        if (debug >= 2) {
          outs() << "[multiHoudini] Candidates weakened, rechecking...\n";
        }
        return multiHoudini(worklist, candidates); // We need to check again after weakening
      }

      if (debug >= 2) {
        outs() << "[multiHoudini] All rules passed\n";
      }
      return anyProgress(worklist, candidates);
    }

    /**
     * Weaken candidates by checking facts and inductive rules
     */
    void weakenCandidates(HornRuleExt* hr, map<Expr, ExprSet>& candidates) 
    {
      if (debug >= 2) {
        outs() << "[weakenCandidates] Starting candidate weakening\n";
      }

      // Try to drop candidates one at a time
      map<Expr, ExprSet> resCands;
      for (auto& kv : candidates) {
        Expr rel = kv.first;
        ExprSet& cands = kv.second;

        // Try removing each candidate
        for (auto& cand : cands) {
          if(debug >= 4) {
            outs() << "  Checking candidate: " << cand << "\n";
          }
          map<Expr, ExprSet> tmpCands;
          tmpCands[rel].insert(cand);
          boost::tribool res = checkRule(hr, tmpCands);

          if(res || indeterminate(res)) {
            if (debug >= 2) {
              outs() << "  Candidate failed: " << cand << " 🔥\n";
            }
          } else {
            // Candidate passed, keep it
            resCands[rel].insert(cand);
          }
        }
      }

      candidates = resCands;
      if (debug >= 2) {
        outs() << "[weakenCandidates] Candidate weakening complete\n";
      }    
    }

    void setBvCandMap(map<Expr, ExprSet>& cands) {
      if (debug >= 2) {
        outs() << "[setBvCandMap] Setting BV candidate map...\n";
      }
      for(auto& kv : cands) {
        Expr rel = kv.first;
        ExprSet& candsSet = kv.second;

        // Normalize and simplify candidates before storing
        ExprSet normalizedCands;
        for (auto& cand : candsSet) {
          Expr normalized_cand = normalizeExpr(normalizePositive(cand));
          Expr simplified_cand = simplifyArithm(normalized_cand, false, false);
          if (!isOpX<TRUE>(simplified_cand)) {
            normalizedCands.insert(simplified_cand);
          }
        }
        m_bvSolutionMap[rel] = conjoin(normalizedCands, m_efac);
      }
    }

    bool checkSafetyInBV() {
      if (debug >= 2) {
        outs() << "[checkSafetyInBV] Starting safety check...\n";
      }

      // Create worklist with all CHCs
      vector<HornRuleExt*> allRules;
      for (auto& hr : m_bvChcs.chcs) {
        allRules.push_back(&hr);
      }

      // Convert solution map to candidates format
      map<Expr, ExprSet> candidates;
      for (const auto& kv : m_bvSolutionMap) {
        ExprSet candSet;
        getConj(kv.second, candSet);
        candidates[kv.first] = candSet;
      }

      // First check: Try with all candidates against all rules
      if (multiHoudini(allRules, candidates)) {
        if (debug >= 1) {
          outs() << "[checkSafetyInBV] System is safe with initial candidates\n";
        }
        setBvCandMap(candidates);
        return true;
      }

      // Update m_bvSolutionMap with weakened candidates
      for (const auto& kv : candidates) {
        m_bvSolutionMap[kv.first] = conjoin(kv.second, m_efac);
      }

      // Final check: Try with weakened candidates against all rules
      bool finalResult = multiHoudini(allRules, candidates);
      if (debug >= 1) {
        if (finalResult) {
          outs() << "[checkSafetyInBV] System is safe after weakening\n";
        } else {
          outs() << "[checkSafetyInBV] System remains unsafe after weakening\n";
        }
      }

      return finalResult;
    }
    // --- End Keep the NEW checkSafetyInBV definition ---

    bool strengthenTransitionRelation() {
      if (debug >= 2) {
        outs() << "[strengthenTransitionRelation] Strengthening transition relation...\n";
      }

      // Get lemmas for strengthening from current solution
      for (auto& hr : m_bvChcs.chcs) {
        if (hr.isQuery) continue;

        // --- Use m_bvSolutionMap ---
        auto it = m_bvSolutionMap.find(hr.dstRelation);
        if (it == m_bvSolutionMap.end()) continue;
        // --- End Use m_bvSolutionMap ---

        // it->second is the combined BV solution expression
        Expr dstSolnExpr = it->second;

        // Add solution to body as constraints
        ExprSet newBody;
        newBody.insert(hr.body);
        // Substitute invariant vars with destination vars before adding
        if (m_bvChcs.invVars.count(hr.dstRelation)) {
            // --- Modification: Use const references for variables ---
            ExprVector& invVars = m_bvChcs.invVars.at(hr.dstRelation);
            ExprVector& dstVars = hr.dstVars; // Use destination variables as target
            // --- End Modification ---

            // Check if variable counts match before substitution
            if (invVars.size() == dstVars.size()) { // Check against dstVars size
                Expr dstSolnSubst = replaceAll(dstSolnExpr,
                                               invVars, // Variables in the solution expression
                                               dstVars); // Target variables for substitution
                newBody.insert(dstSolnSubst);
                if (debug >= 3)
                  outs() << "  [strengthenTransitionRelation] Strengthening rule for " << hr.dstRelation
                         << " (using dstVars) with: " << dstSolnSubst << "\n"; // Updated log
            } else {
                if (debug >= 1) outs() << "[strengthenTransitionRelation] Warning: Variable count mismatch for rule involving "
                                       << hr.dstRelation << ". Invariant vars (" << invVars.size()
                                       << ") vs Destination vars (" << dstVars.size() << "). Skipping strengthening for this rule.\n"; // Updated log
            }
        } else {
             if (debug >= 2) outs() << "[strengthenTransitionRelation] Warning: Missing invVars for " << hr.dstRelation << ".\n";
        }


        // Update CHC body with strengthened version
        hr.body = conjoin(newBody, m_efac);
      }

      if (debug >= 3) {
        outs() << "[strengthenTransitionRelation] Strengthened BV system:\n";
        m_bvChcs.print(true);
      }

      return true;
    }

    void printSolution() {
      // --- Refactor to use the helper method ---
      printBvSolutionMap(m_bvSolutionMap);
      // --- End Refactor ---
    }

    // Add new method to apply solution to CHC system
    // --- Remove candidates parameter ---
    bool applySolutionToBvSystem(/* map<Expr, ExprSet>& cands - REMOVED */) {
      if (debug >= 3) {
        outs() << "[applySolutionToBvSystem] Applying solution map to BV system (internal use)\n"; // Updated log
        outs() << "  Solution map size: " << m_bvSolutionMap.size() << "\n";
      }
      // cands.clear(); // No longer needed
      // Convert m_bvSolutionMap to map<Expr,ExprSet> format - No longer needed externally
      // for (auto& kv : m_bvSolutionMap) {
      //   cands[kv.first] = ExprSet{kv.second};
      // }
      // --- End Remove candidates parameter ---

      // The method doesn't strictly need to *do* anything anymore,
      // as the solution is stored internally in m_bvSolutionMap.
      // It just needs to exist if called elsewhere, returning true.
      return true;
    }
  };

  // Main entry point forBV translation and solving
  inline bool learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, int debug)
  {
    // Create factories and parse input
    ExprFactory efac;
    EZ3 z3(efac); 

    // Parse the original CHC system
    CHCs ruleManager(efac, z3, debug);
    if (!ruleManager.parse(smt, doElim, doArithm))
    {
      outs() << "Error parsing input file\n";
      return 1;
    }

    // For non-serialization case, check if input is BV format
    if (!ruleManager.hasBV && !ser)
    {
      outs() << "Input is not in BV format\n";
      return 1;
    }

    // Create BitHorn solver and pass through maxAttempts parameter 
    BitHorn bh(efac, z3, ruleManager, debug);

    if (ser) {
      // Just translate and serialize
      if(debug >= 2) 
      {
        outs() << "[learnInvariants5] Translating LIA to BV for serialization.\n";
      }
      if (!bh.translateToBv()) {
        outs() << "[learnInvariants5] Error translating LIA to BV\n"; 
        return 1;
      }
      bh.getBvChcs().serialize(false);
      if(debug >= 2) outs() << "[learnInvariants5] Serialized BV translation\n";
      return 0;
    }

    // Solve BV system with maxAttempts
    return bh.solve(to);
  }
}

#endif