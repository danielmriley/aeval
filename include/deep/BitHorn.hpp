#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include "Horn.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"
#include "ae/ExprSimpl.hpp" // Include ExprSimpl for simplification functions
// Removed include "ufo/ExprVisitor.hpp"

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
    unsigned m_original_bv_width = 0; // Store original BV width

    // --- Refactored Solution Storage ---
    // m_liaSolution is removed
    map<Expr, ExprSet> m_liaSolutionMap; // Maps LIA relation -> LIA solution ExprSet
    // m_bvSolution is removed
    map<Expr, Expr> m_bvSolutionMap;   // Maps BV relation -> combined BV solution Expr
    // --- End Refactored Solution Storage ---

    map<Expr, ExprVector> origBvVars;  // Original BV variables in the program
    map<Expr, ExprVector> origBvVarsPrime;  // Original primed BV variables in the program
    map<Expr, ExprVector> origLiaVars; // Original LIA variables in the program
    map<Expr, ExprVector> origLiaVarsPrime; // Original primed LIA variables in the program

    // --- Add new private helper method for printing BV solution map ---
    void printBvSolutionMap(const map<Expr, Expr>& bvSolutionMap) {
      outs() << "; --- BV Solution Map ---\n";
      for (const auto& kv : bvSolutionMap) {
        Expr rel = kv.first;
        Expr solution = kv.second; // This is the combined BV solution

        // Check if relation exists in invVars map
        if (!m_bvChcs.invVars.count(rel)) {
            if (debug >= 1) outs() << "; Warning: Cannot print solution for " << *rel << " - missing variables.\n";
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

        // --- Validation Check (Optional but good practice) ---
        ExprVector nonConstInvVars = invVars; // Create non-const copy for validation
        bool valid = hasOnlyVars(solution, nonConstInvVars);
        if (!valid && debug >= 1) {
            outs() << "; Warning: Solution for " << *rel << " contains unexpected variables!\n";
            ExprSet extra;
            getExtraVars(solution, nonConstInvVars, extra);
            outs() << "; Extra vars: ";
            for(const auto& v : extra) outs() << *v << " ";
            outs() << "\n";
        }
        // --- End Validation Check ---
      }
      outs() << "; --- End BV Solution Map ---\n";
    }
    // --- End new private helper method ---

    // Add helper to normalize expressions (existing)
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
             // if (debug >= 4) outs() << "normalizePositive: Skipping non-numeric comparison: " << *e << "\n";
            return e;
        }

        if (debug >= 4) outs() << "normalizePositive: Input: " << *e << "\n";

        // 1. Use normalizeAtom to get Sum(ci*vi) op C form
        ExprVector vars;
        // Collect all variables appearing in the expression
        filter(e, bind::IsConst(), inserter(vars, vars.begin()));
        if (vars.empty()) {
             if (debug >= 4) outs() << "normalizePositive: No variables found in: " << *e << "\n";
             // It might be a comparison of constants, simplify it directly
             return simplifyArithm(e);
        }

        // Use normalizeAtom from ExprSimpl.hpp
        Expr normalized = normalizeAtom(e, vars);

        if (debug >= 4) outs() << "normalizePositive: After normalizeAtom: " << *normalized << "\n";

        if (isOpX<TRUE>(normalized) || isOpX<FALSE>(normalized)) {
            return normalized; // Already simplified to true/false
        }

        // Check if normalizeAtom produced the expected form
        if (!isOp<ComparissonOp>(normalized) || !isNumeric(normalized->left()) || !isNumeric(normalized->right())) {
             if (debug >= 1) outs() << "Warning: normalizeAtom did not produce expected Sum(ci*vi) op C form for: " << *e << ". Got: " << *normalized << "\n";
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
                  outs() << "normalizePositive: Found constant " << *term << " on LHS of normalized expr.\n";
                continue; // Skip to next term
            }

            // Ensure varPart is a variable (or treat as atomic)
            // Using bind::IsConst() to identify variables/program constants
            if (bind::IsConst()(varPart)) {
                termCoefficients[varPart] += coef;
            } else {
                // If it's not a variable, treat it as an atomic term with coefficient 1 or -1
                 if (debug >= 3) outs() << "normalizePositive: Treating non-variable term " << *varPart << " as atomic.\n";
                termCoefficients[varPart] += coef; // Accumulate coefficient for the term itself
            }
        }

        // Subtract the constant C from the RHS (since we want LHS - C op 0)
        if (isOpX<MPZ>(rhs)) {
            // Convert mpz_class to cpp_int before subtracting
            constantPart = constantPart - cpp_int(getTerm<mpz_class>(rhs).get_str());
        } else {
             if (debug >= 1) outs() << "Warning: RHS of normalized expression is not an MPZ constant: " << *rhs << "\n";
             return simplifyArithm(e); // Fallback
        }

        if (debug >= 4) {
            outs() << "normalizePositive: Coefficients map:\n";
            // --- Replace structured binding ---
            for(auto const& pair : termCoefficients) {
                Expr var = pair.first;
                cpp_int coef = pair.second;
            // --- End Replace structured binding ---
                outs() << "  " << *var << ": " << coef << "\n";
            }
            outs() << "normalizePositive: Constant part (LHS - C): " << constantPart << "\n";
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
        if (debug >= 4) outs() << "normalizePositive: Result: " << *result << "\n";

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
                outs() << "  processLearnedLiaLemmas: Checking relation " << *liaDeclExpr << ", full decl: " << *liaDecl << ", found invNum: " << invNum << "\n";
                if (invNum >= 0) solver.printSolutionForRelation(invNum);
            }

            if (invNum < 0) { // Log if not found
                 if (debug >= 1) outs() << "Error: Could not find index for LIA declaration: " << *liaDecl << "\n";
                 continue;
            }

            ExprSet lemmas = solver.getlearnedLemmas(invNum);
            if(debug >=4) outs() << "  lemmas size: " << lemmas.size() << "\n";
            if (!lemmas.empty()) {
                ExprSet simplifiedLemmas; // Store results after initial simplification
                if (debug >= 4) outs() << "  Simplifying individual lemmas for " << *liaDeclExpr << ":\n";
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
                if (debug >= 4) outs() << "  Applying final positive normalization for " << *liaDeclExpr << ":\n";
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
                    outs() << "LIA Lemmas for " << liaDeclExpr << " (" << finalNormalizedLemmas.size() << "):\n"; // Use finalNormalizedLemmas
                    for(auto& l : finalNormalizedLemmas) outs() << "  " << l << "\n"; // Use finalNormalizedLemmas
                 }
            } else {
                 if (debug >= 2) outs() << "Warning: No LIA lemmas found for " << liaDeclExpr << "\n";
                 m_liaSolutionMap[liaDeclExpr] = ExprSet(); // Store empty set
            }
        }
    }
    // --- End new private helper method ---

    public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) : 
      m_efac(efac), 
      m_z3(z3),
      m_liaChcs(new CHCs(efac,z3,_debug)), // Create new CHCs object
      m_bvChcs(input),
      u(efac),
      m_Lia2BvTranslator(efac, z3, 4, _debug),
      m_Bv2LiaTranslator(efac, z3, 4, _debug),
      debug(_debug),
      m_learnedLemmas(1) // Initialize with size 1 to store lemmas for the first relation
    { 
      if (debug >= 1) {
        outs() << "Initializing BitHorn solver\n";
      }
      // --- Modification: Detect and store original BV width ---
      if (m_bvChcs.hasBV) {
          for (auto decl : m_bvChcs.decls) {
              if (decl && decl->arity() > 1) {
                  for (unsigned i = 1; i < decl->arity() - 1; ++i) {
                      Expr sort = decl->arg(i);
                      if (isOpX<BVSORT>(sort)) {
                          m_original_bv_width = bv::width(sort);
                          if (debug >= 2) {
                              outs() << "BitHorn: Detected original BV width " << m_original_bv_width << " from decl " << *decl << "\n";
                          }
                          goto width_detected_constructor; // Found it
                      }
                  }
              }
          }
          width_detected_constructor:; 
          // Pass the detected width to the LIA->BV and BV->LIA translator instances
          if (m_original_bv_width > 0) {
              m_Lia2BvTranslator.setOriginalBvWidth(m_original_bv_width);
          }
      }
      // --- End Modification ---

      for (auto dd : m_bvChcs.decls)
      {
        Expr d = dd->left();
        // Copy vectors directly
        origBvVars[d] = m_bvChcs.invVars[d];
        origBvVarsPrime[d] = m_bvChcs.invVarsPrime[d];
      }
      for(auto v: origBvVars)
      {
        if (debug >= 3) {
          outs() << "origBvVars: " << v.first << "\n";
          for(auto a: v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
        }
      }
      for(auto v: origBvVarsPrime)
      {
        if (debug >= 3) {
          outs() << "origBvVarsPrime: " << v.first << "\n";
          for(auto a: v.second)
          {
            outs() << "  Var: " << a << "\n";
            outs() << "  Type: " << bind::typeOf(a) << "\n";
          }
        }
      }
    }

    ~BitHorn() {
      if (m_liaChcs) delete m_liaChcs;
    }

    // Add reset method
    void resetLiaChcs() {
      if (m_liaChcs) {
        m_liaChcs->reinitialize(m_bvChcs);
      } else {
        m_liaChcs = new CHCs(m_bvChcs);
      }
    }

    bool translateToBv()
    {
      if(debug >= 3)
      {
        outs() << "Beginning translation\n";
      }
      
      // Create temporary CHCs for the translation
      CHCs translatedChcs = m_Lia2BvTranslator.translate(m_bvChcs);
      for(auto d: translatedChcs.decls)
      {
        // Copy vectors directly
        origBvVars[d] = translatedChcs.invVars[d];
        origBvVarsPrime[d] = translatedChcs.invVarsPrime[d];
      }
      
      // Properly reinitialize m_bvChcs from translated version
      m_bvChcs.reinitialize(translatedChcs);

      if (debug >= 3)
      {
        outs() << "Ending translation\n";
        m_bvChcs.print(true);
      }

      // Serialize the translated program  
      m_bvChcs.serialize(false);

      return true;
    }

    bool translateToLia()
    {
      if (debug >= 2)
      {
        outs() << "Translating BV to LIA\n";
      }

      // --- Potential Crash Site ---
      // The GDB backtrace indicates a segmentation fault inside m_Bv2LiaTranslator.translate,
      // specifically when calling ENode::arg().
      // Based on debug logs, this likely occurs when processing a rule involving a 0-arity
      // predicate like 'true' (as source) or 'fail' (as destination).
      // The translator might be attempting node->arg(0) on the ENode representing 'true' or 'fail'
      // without checking node->arity() first, leading to an out-of-bounds access.
      // The fix requires modifying the Bv2LiaTranslator::translate implementation
      // (likely in simpl/Bv2Lia.hpp) to correctly handle 0-arity predicates.
      // --- End Potential Crash Site ---

      // Create temporary CHCs for the translation
      CHCs translatedChcs = m_Bv2LiaTranslator.translate(m_bvChcs);

      // --- Modification: Clear maps and add debug prints ---
      origLiaVars.clear(); 
      origLiaVarsPrime.clear();
      if (debug >= 4) outs() << "Populating origLiaVars:\n";
      // --- End Modification ---

      for (auto d : translatedChcs.decls)
      {
        // --- Modification: Use relation name as key ---
        Expr relName = d->left(); 
        if (!relName) continue; // Skip if name is null

        // Copy vectors directly, using the relation NAME as the key
        origLiaVars[relName] = translatedChcs.invVars[relName];
        origLiaVarsPrime[relName] = translatedChcs.invVarsPrime[relName];
        // --- End Modification ---

        if (debug >= 4) {
          outs() << "  Relation: " << *relName << "\n";
          outs() << "    invVars (" << origLiaVars[relName].size() << "): ";
          for(const auto& v : origLiaVars[relName]) outs() << *v << " "; outs() << "\n";
          outs() << "    invVarsPrime (" << origLiaVarsPrime[relName].size() << "): ";
          for(const auto& v : origLiaVarsPrime[relName]) outs() << *v << " "; outs() << "\n";
        }
      }

      // Properly reinitialize m_liaChcs from translated version
      // --- Modification: Use reinitialize instead of parse ---
      if (!m_liaChcs) {
          m_liaChcs = new CHCs(m_efac, m_z3, debug);
      }
      m_liaChcs->reinitialize(translatedChcs);
      // --- End Modification ---

      // Old code:
      // m_liaChcs->serialize(false); // Serialize to chc.smt2
      // delete m_liaChcs;
      // m_liaChcs = new CHCs(m_efac, m_z3, debug);
      // m_liaChcs->parse("chc.smt2");

      // Debug dump of CHCs contents
      if (debug >= 5)
      {
        outs() << "\n=== Debug dump of LIA CHCs ===\n";

        // Print declarations
        outs() << "Declarations:\n";
        for (auto decl : m_liaChcs->decls)
        {
          outs() << "decl: " << *decl << "\n";
          if (decl && decl->left())
          {
            outs() << "decl->left(): " << *decl->left() << "\n";
          }
        }

        // Print variables per declaration
        outs() << "\nVariables per declaration:\n";
        for (auto &kv : m_liaChcs->invVars)
        {
          if (kv.first)
          {
            outs() << "For declaration " << *kv.first << ":\n";
            for (auto &var : kv.second)
            {
              outs() << "  var: " << *var << "\n";
              if (var && var->left())
              {
                outs() << "  var->left(): " << *var->left() << "\n";
              }
            }
          }
        }

        // Print Horn rules
        outs() << "\nHorn Rules:\n";
        for (auto &rule : m_liaChcs->chcs)
        {
          outs() << "Rule:\n";
          if (rule.srcRelation)
          {
            outs() << "  src: " << *rule.srcRelation << "\n";
            if (rule.srcRelation->left())
            {
              outs() << "  src->left(): " << *rule.srcRelation->left() << "\n";
            }
          }
          if (rule.dstRelation)
          {
            outs() << "  dst: " << *rule.dstRelation << "\n";
            if (rule.dstRelation->left())
            {
              outs() << "  dst->left(): " << *rule.dstRelation->left() << "\n";
            }
          }
          if (rule.body)
          {
            outs() << "  body: " << *rule.body << "\n";
            if (rule.body->left())
            {
              outs() << "  body->left(): " << *rule.body->left() << "\n";
            }
          }

          outs() << "  Source vars:\n";
          for (auto &v : rule.srcVars)
          {
            outs() << "    var: " << *v << "\n";
            if (v && v->left())
            {
              outs() << "    var->left(): " << *v->left() << "\n";
            }
          }

          outs() << "  Destination vars:\n";
          for (auto &v : rule.dstVars)
          {
            outs() << "    var: " << *v << "\n";
            if (v && v->left())
            {
              outs() << "    var->left(): " << *v->left() << "\n";
            }
          }
        }

        // Print WTO info
        outs() << "\nWTO Declarations:\n";
        for (auto &decl : m_liaChcs->wtoDecls)
        {
          outs() << "decl: " << *decl << "\n";
          if (decl && decl->left())
          {
            outs() << "decl->left(): " << *decl->left() << "\n";
          }
        }

        outs() << "\nWTO CHCs:\n";
        for (auto &wto : m_liaChcs->wtoCHCs)
        {
          outs() << "WTO rule:\n";
          if (wto && wto->srcRelation)
          {
            outs() << "  src: " << *wto->srcRelation << "\n";
            if (wto->srcRelation->left())
            {
              outs() << "  src->left(): " << *wto->srcRelation->left() << "\n";
            }
          }
          if (wto && wto->dstRelation)
          {
            outs() << "  dst: " << *wto->dstRelation << "\n";
            if (wto->dstRelation->left())
            {
              outs() << "  dst->left(): " << *wto->dstRelation->left() << "\n";
            }
          }
        }

        outs() << "\ndWTO CHCs:\n";
        for (auto &wto : m_liaChcs->dwtoCHCs)
        {
          outs() << "WTO rule:\n";
          if (wto && wto->srcRelation)
          {
            outs() << "  src: " << *wto->srcRelation << "\n";
            if (wto->srcRelation->left())
            {
              outs() << "  src->left(): " << *wto->srcRelation->left() << "\n";
            }
          }
          if (wto && wto->dstRelation)
          {
            outs() << "  dst: " << *wto->dstRelation << "\n";
            if (wto->dstRelation->left())
            {
              outs() << "  dst->left(): " << *wto->dstRelation->left() << "\n";
            }
          }
        }

        outs() << "=== End debug dump ===\n\n";
      }

      return true;
    }

    CHCs& getLiaChcs() { return *m_liaChcs; }
    CHCs& getBvChcs() { return m_bvChcs; }

    // --- Updated getSolution methods ---
    void getSolution(map<Expr, Expr> &e) { // Changed signature
      e = m_bvSolutionMap;
    }

    map<Expr, Expr> getSolution() { // Changed signature
      return m_bvSolutionMap;
    }
    // --- End Updated getSolution methods ---

    bool solve(unsigned to = 100) {
      if (debug >= 1) {
        outs() << "Starting BitHorn solver with timeout " << to << "\n";
      }

      for (unsigned i = 0; i < to; i++) {
        if (debug >= 2) {
          outs() << "\nIteration " << i << " of " << to << "\n";
        }

        // 1. Translate current BV system to LIA
        if (!translateToLia()) {
          if (debug >= 1) outs() << "Failed to translate BV to LIA\n";
          return false;
        }
        
        if (debug >= 3) {
          outs() << "Translated BV -> LIA system:\n";
          m_liaChcs->print(true);
        }

        // 2. Try to solve LIA system with timeout
        if (!solveLIA()) { // solveLIA now populates m_liaSolutionMap
          if (debug >= 1) outs() << "Could not find LIA solution\n";
          // return false;
          // Instead of quitting, use the lemmas found to strengthen the BV system and try again.
        }

        if (debug >= 3) {
          outs() << "Found LIA solution with " << m_liaSolutionMap.size() << " relations\n"; // Updated log
        }

        // 3. Translate LIA solution back to BV
        if (!translateSolutionToBv()) { // translateSolutionToBv now uses m_liaSolutionMap and populates m_bvSolutionMap
          if (debug >= 1) outs() << "Failed to translate solution to BV\n";
          return false;
        }

        if (debug >= 3) {
          outs() << "Translated solution back to BV with " << m_bvSolutionMap.size() << " relations\n"; // Updated log
        }

        // --- Call the new print method here ---
        if (debug >= 2) { // Print intermediate solution if debug level is 2 or higher
            printBvSolutionMap(m_bvSolutionMap);
        }
        // --- End call ---

        // 4. Check if solution is safe in BV
        map<Expr, ExprSet> candidates;
        if (!applySolutionToBvSystem(candidates)) {
          if (debug >= 1) outs() << "Failed to apply BV solution\n";
          return false;
        }

        bool isSafe = checkSafetyInBV(candidates);
        
        if (isSafe) {
          outs() << "Success : Found safe BV solution after " << (i+1) << " iterations!\n";
          printSolution();

          return true;
        }

        if (debug >= 2) {
          outs() << "Solution not safe in BV, strengthening...\n";
        }

        // 5. Strengthen transition relation and continue
        if (!strengthenTransitionRelation()) {
          if (debug >= 1) outs() << "Failed to strengthen transition relation\n";
          return false;
        }
      }

      if (debug >= 1) {
        outs() << "No solution found after " << to << " iterations\n";
      }
      return false;
    }

    private:
    void initializeSolver(std::unique_ptr<RndLearnerV4> solver)
    {
      
    }

    bool solveLIA(unsigned int to = 100) {
      if (debug >= 2) {
        outs() << "Attempting to solve LIA system\n";  
      }

      // Before creating solver, normalize and validate all rule bodies
      for (auto &rule : m_liaChcs->chcs) {
        if (containsOp<IDIV>(rule.body) || containsOp<MOD>(rule.body)) {
          if (debug >= 1) outs() << "Warning: Skipping rule with division\n";
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
        if (debug >= 1) outs() << "Error: Failed to create solver\n";
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
               if (debug >= 5) outs() << "  solveLIA: Added normalized prefix cand for " << *rel << ": " << *simplified_t << "\n";
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
              if (debug >= 5) outs() << "  solveLIA: Mutated candidates for " << *rel << "\n";
          }
          // Initialize Aux uses the current state of cands[rel]
          solver->initializeAux(cands[rel], bnd, rel, i, pref);
          // --- End Modification ---
        }
      }

      // Generate data-based candidates if enabled
      if (da > 0) {
        solver->getDataCandidates(cands); // This adds potentially un-normalized candidates
        if (debug >= 4) outs() << "  solveLIA: Got data candidates.\n";

        // --- Modification: Normalize all candidates again after adding data candidates ---
        if (debug >= 4) outs() << "  solveLIA: Normalizing all candidates (prefix + data + mutated)...\n";
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
          outs() << "Bootstrap successful\n";
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
          outs() << "V4 solver found solution via synthesis\n"; // Clarified log
        }
        // --- Call helper method to process lemmas ---
        processLearnedLiaLemmas(*solver);
        // --- End call helper method ---
        return true; // Return true if synthesis succeeded
      }

      if (debug >= 1) outs() << "LIA solver failed (bootstrap and synthesis)\n"; // Added final failure log
      return false;
    }

    bool translateSolutionToBv() {
      if (debug >= 2) {
        outs() << "Translating LIA solution map to BV solution map...\n";
      }

      // Clear any previous solution
      m_bvSolutionMap.clear();

      // Safety check - ensure we have declarations
      if (m_bvChcs.decls.empty()) {
        if (debug >= 1) {
          outs() << "Error: No declarations found in BV CHCs\n";
        }
        return false;
      }

      // Get the BV -> LIA declaration map
      const auto& bvToLiaMap = m_Bv2LiaTranslator.getBvToLiaDeclMap();

      // +++ Debugging +++
      if (debug >= 4) {
          outs() << "BV to LIA Relation Map (bvToLiaMap):\n";
          for (const auto& pair : bvToLiaMap) {
              if (pair.first && pair.second) { // Check for null pointers
                  outs() << "  BV: " << *(pair.first) << " -> LIA: " << *(pair.second) << "\n";
              } else {
                  outs() << "  BV: (null?) -> LIA: (null?)\n";
              }
          }
          outs() << "LIA Solution Map (m_liaSolutionMap):\n";
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

        if (debug >= 4) outs() << "Processing BV relation: " << *bvRel << "\n";

        // Find corresponding LIA relation NAME using the map
        auto mapIt = bvToLiaMap.find(bvRel); // Look up original BV name
        if (mapIt == bvToLiaMap.end()) {
          if (debug >= 1) outs() << "Warning: Could not find LIA relation for BV relation " << *bvRel << " in bvToLiaMap\n"; // Added map name
          continue;
        }
        Expr liaRel = mapIt->second; // Translated LIA relation name

        if (debug >= 4) outs() << "  Found corresponding LIA relation name: " << *liaRel << "\n";

        // Find LIA solution for this relation using the LIA relation name as key
        auto liaSolnIt = m_liaSolutionMap.find(liaRel); // Look up translated LIA name
        if (liaSolnIt == m_liaSolutionMap.end() || liaSolnIt->second.empty()) {
          if (debug >= 2) outs() << "Warning: No LIA solution found for relation " << *liaRel << " (BV: " << *bvRel << ") in m_liaSolutionMap\n"; // Added map name
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
              outs() << "Warning: Failed to translate LIA expression: " << *liaExpr << " for relation " << *liaRel << "\n";
            }
            continue;
          }

          // Replace LIA invariant variables with BV invariant variables
          // Ensure both relations exist in the respective variable maps

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
              if (debug >= 2) outs() << "Warning: Missing variables for relation pair " << *liaRel << "/" << *bvRel << " during translation.\n";
          }
        }

        // Store the conjunction of translated BV expressions
        m_bvSolutionMap[bvRel] = conjoin(bvExprSet, m_efac);
        if (debug >= 3) {
            outs() << "BV Solution for " << *bvRel << ": " << m_bvSolutionMap[bvRel] << "\n";
        }
      }


      // Print full translation results (optional, maybe redundant with above)
      if (debug >= 2) {
        outs() << "\nFinal Translated BV Solution Map (" << m_bvSolutionMap.size() << " entries):\n";
        for (auto& kv : m_bvSolutionMap) {
          outs() << "Relation: " << *kv.first << "\n";
          outs() << "     BV Solution: " << *kv.second << "\n";
        }
        outs() << "\n";
      }

      // Consider success if at least one relation was translated, even if to 'true'
      return !m_bvSolutionMap.empty();
    }


    // TODO: Review again to make sure it does what it should be doing.
    // Namely, it should check the BV system
    bool multiHoudini(vector<HornRuleExt*> worklist) // Removed recur parameter
    {
      if (debug >= 3) outs() << "MultiHoudini (Validation)\n";

      for (auto &hr : worklist)
      {
        if (debug >= 3) {
          outs() << "  Checking CHC (" << hr->srcRelation << " -> "
                 << hr->dstRelation << ")\n";
        }

        ExprSet exprs = {hr->body};

        // Add source solution constraints if not a fact
        if (!hr->isFact) {
          auto srcSolnIt = m_bvSolutionMap.find(hr->srcRelation);
          if (srcSolnIt != m_bvSolutionMap.end()) {
            // Check if srcRelation exists in invVars before accessing
            if (m_bvChcs.invVars.count(hr->srcRelation)) {
                // srcSolnIt->second is the combined BV solution for the relation
                Expr srcSolnCombined = srcSolnIt->second;
                // Substitute invariant variables with rule's source variables
                Expr srcSolnSubst = replaceAll(srcSolnCombined,
                                          m_bvChcs.invVars.at(hr->srcRelation), // BV Invariant Vars
                                          hr->srcVars);                         // BV Rule Source Vars
                exprs.insert(srcSolnSubst);
                if(debug >= 3) outs() << "    Source solution (" << hr->srcRelation << "): " << srcSolnSubst << "\n"; // Updated log
            } else {
                 if (debug >= 2) outs() << "Warning: Source relation " << hr->srcRelation << " not found in invVars map during multiHoudini check.\n";
                 continue;
            }
          } else {
             if (debug >= 3) outs() << "    Source solution missing for " << hr->srcRelation << ", assuming true.\n";
             // If solution for source is missing, it implies 'true', so we don't add anything.
          }
        }

        // Add negated destination solution constraints if not a query
        if (!hr->isQuery) {
          auto dstSolnIt = m_bvSolutionMap.find(hr->dstRelation);
          if (dstSolnIt != m_bvSolutionMap.end()) {
             // Check if dstRelation exists in invVars before accessing
             if (m_bvChcs.invVars.count(hr->dstRelation)) {
                // dstSolnIt->second is the combined BV solution for the relation
                Expr dstSolnCombined = dstSolnIt->second;
                 // Substitute invariant variables with rule's destination variables
                Expr dstSolnSubst = replaceAll(dstSolnCombined,
                                          m_bvChcs.invVars.at(hr->dstRelation), // BV Invariant Vars
                                          hr->dstVars);                         // BV Rule Destination Vars
                exprs.insert(mkNeg(dstSolnSubst));
                 if(debug >= 3) outs() << "    Neg Dest solution (" << hr->dstRelation << "): " << mkNeg(dstSolnSubst) << "\n"; // Updated log
             } else {
                 if (debug >= 2) outs() << "Warning: Destination relation " << hr->dstRelation << " not found in invVars map during multiHoudini check.\n";
                 continue;
             }
          } else {
            if (debug >= 3) outs() << "    Destination solution missing for " << hr->dstRelation << ", rule trivially satisfied.\n";
            continue; // Skip the SAT check for this rule
          }
        }
        // For query rules, we don't add a negated destination. The check is Body ^ SrcInv => false.
        // Which means we check satisfiability of Body ^ SrcInv.

        // --- Debug Print ---
        if (debug >= 4) {
            outs() << "    Checking SAT for: \n";
            pprint(conjoin(exprs, m_efac));
            outs() << "\n";
          }
        // --- End Debug Print ---

        if (u.isSat(exprs)) {
          // If SAT, the implication Body ^ SrcInv => DstInv (or Body ^ SrcInv => false for queries) is violated.
          if (debug >= 3) outs() << "    CHC check failed (SAT)\n";
          return false; // Solution is not valid for this rule
        }
        else {
           if (debug >= 3) outs() << "    CHC check succeeded (UNSAT)\n";
        }
      }

      // If all rules in the worklist passed the check
      if (debug >= 3) outs() << "MultiHoudini: All checks passed.\n";
      return true; // Solution is valid for all rules checked
    }

    bool checkSafetyInBV(map<Expr, ExprSet>& candidates) { // candidates param seems unused but kept for signature stability
      if (debug >= 2) {
        outs() << "Checking safety of BV solution\n";
      }

      vector<HornRuleExt*> worklist;

      // Add all query rules to the worklist
      for (auto& hr : m_bvChcs.chcs) {
        // --- Modification: Add all rules, not just queries ---
        worklist.push_back(&hr);
        // --- End Modification ---
      }

      if (worklist.empty()) {
        if (debug >= 2) {
          outs() << "No rules to check (system is empty?)\n"; // Updated log
        }
        return true; // No rules means safe
      }

      // Call multiHoudini to check safety
      // multiHoudini returns true if the solution satisfies all rules in the worklist (is safe)
      // multiHoudini returns false if any rule is violated (is unsafe)
      return multiHoudini(worklist); // Return the result directly
    }

    bool strengthenTransitionRelation() {
      if (debug >= 2) {
        outs() << "Strengthening transition relation\n";
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
            // --- Modification: Substitute invariant vars with DESTINATION vars ---
            // --- Create non-const copies ---
            ExprVector invVars = m_bvChcs.invVars.at(hr.dstRelation);
            ExprVector dstVars = hr.dstVars; // Use destination variables as target
            // --- End Create non-const copies ---

            // Check if variable counts match before substitution
            if (invVars.size() == dstVars.size()) { // Check against dstVars size
                Expr dstSolnSubst = replaceAll(dstSolnExpr,
                                               invVars, // Variables in the solution expression (now a copy)
                                               dstVars); // Target variables for substitution (now a copy)
                newBody.insert(dstSolnSubst);
                if (debug >= 3)
                  outs() << "  Strengthening rule for " << hr.dstRelation
                         << " (using dstVars) with: " << dstSolnSubst << "\n"; // Updated log
            } else {
                if (debug >= 1) outs() << "Warning: Variable count mismatch during strengthening for rule involving "
                                       << hr.dstRelation << ". Invariant vars (" << invVars.size()
                                       << ") vs Destination vars (" << dstVars.size() << "). Skipping strengthening for this rule.\n"; // Updated log
            }
            // --- End Modification ---
        } else {
             if (debug >= 2) outs() << "Warning: Missing invVars for " << hr.dstRelation << " during strengthening.\n";
        }


        // Update CHC body with strengthened version
        hr.body = conjoin(newBody, m_efac);
      }

      if (debug >= 3) {
        outs() << "Strengthened BV system:\n";
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
    bool applySolutionToBvSystem(map<Expr, ExprSet>& cands) {
      if (debug >= 3) {
        outs() << "Applying solution map to BV system (for candidates map)\n";
        outs() << "Solution map size: " << m_bvSolutionMap.size() << "\n";
      }
      cands.clear();
      // Convert m_bvSolutionMap to map<Expr,ExprSet> format
      // --- Use m_bvSolutionMap ---
      for (auto& kv : m_bvSolutionMap) {
        // kv.first is BV relation, kv.second is combined BV solution Expr
        cands[kv.first] = ExprSet{kv.second};
      }
      // --- End Use m_bvSolutionMap ---

      return true;
    }
  };

  // Main entry point for BV translation and solving
  inline void learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
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
      return;
    }

    // For non-serialization case, check if input is BV format
    if (!ruleManager.hasBV && !ser)
    {
      outs() << "Input is not in BV format\n";
      return;
    }

    // Create BitHorn solver and pass through maxAttempts parameter 
    BitHorn bh(efac, z3, ruleManager, debug);

    if (ser) {
      // Just translate and serialize
      if(debug >= 2) 
      {
        outs() << "Translating LIA to BV.\n";
      }
      if (!bh.translateToBv()) {
        outs() << "Error translating LIA to BV\n"; 
        return;
      }
      bh.getBvChcs().serialize(false);
      if(debug >= 2) outs() << "Serialized BV translation\n";
      return;
    }

    // Solve BV system with maxAttempts
    bh.solve(to);
  }
}

#endif
