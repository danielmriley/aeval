#ifndef LIA2BV__HPP__
#define LIA2BV__HPP__

#include "deep/Horn.hpp"
#include "ufo/Smt/EZ3.hh" // Include necessary headers
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"

using namespace std;
using namespace expr::op; // Include namespace for operators like TRUE, FALSE, etc.

namespace ufo
{
  class Lia2BvTranslator 
  {
    private:
      ExprFactory &m_efac;
      EZ3 &m_z3;
      unsigned int m_width;
      int debug;  // Add debug member
      unsigned int m_original_bv_width = 0; // Store original BV width if applicable
      
      // Maps for tracking translations
      std::map<Expr, Expr> m_var_map;      // Maps LIA vars to BV vars  
      std::map<Expr, Expr> m_decl_map;     // Maps LIA decls (full Expr) to BV decls (full Expr)
      
      // Translation helpers
      Expr translateVar(Expr var)
      {
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
            return it->second;

        // Check if it's an integer constant variable before translating
        if (!bind::isIntConst(var)) {
             if (debug >= 3) outs() << "Kept non-Int var: " << *var << "\n";
             return var; // Keep non-integer vars as is
        }
            
        // Create BV variable using bv::bvConst
        Expr name = bind::fname(bind::fname(var)); // Get the name Expr
        Expr bvVar = bv::bvConst(name, m_width); // Create BV constant with the same name
        m_var_map[var] = bvVar; // Map original LIA var Expr to BV var Expr
        
        if (debug >= 3) {
            outs() << "Mapped LIA var " << *var << " to BV var " << *bvVar << "\n";
        }
        return bvVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        
        for (const auto &var : origVars)
        {
            // Check if it's an integer variable before translating
            if (!bind::isIntConst(var)) {
                translatedVars.push_back(var); // Keep non-Int vars
                if (debug >= 3) outs() << "Kept non-Int invVar: " << *var << "\n";
                continue;
            }

            // Use same translation logic as translateVar
            Expr name = bind::fname(bind::fname(var)); // Get name Expr
            Expr bvVar = bv::bvConst(name, m_width); // Create BV var
            translatedVars.push_back(bvVar);
            
            if (cacheVars) {
                m_var_map[var] = bvVar; // Map original LIA var to BV var
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
        if (v == 0) return 1; // Need 1 bit for 0
        
        // Get absolute value for negative numbers, need extra bit for sign
        bool negative = (v < 0);
        if (negative) v = -v;
        
        // Calculate log2 rounded up for magnitude
        unsigned int width = 0;
        // Handle v=1 case correctly
        mpz_class temp_v = v;
        if (temp_v == 1 && !negative) return 1; // 1 needs 1 bit
        
        // Find the highest set bit position (equivalent to floor(log2(v)) + 1)
        width = mpz_sizeinbase(temp_v.get_mpz_t(), 2);

        // Add 1 bit for the sign if negative OR if positive and needs sign bit space
        // For two's complement, width needs to accommodate max(abs(v), abs(v)-1 if negative)
        // If v = -8 (1000), width=4. If v=7 (0111), width=4.
        // If v = -1 (1), width=1. If v=0 (0), width=1.
        // Width calculated is for magnitude. Add 1 for sign.
        return width + 1; 
      }

      unsigned int findMinBitWidth(const std::vector<HornRuleExt>& rules)
      {
        unsigned int maxWidth = m_width; // Start with default or provided width

        // Helper to process an expression and update maxWidth
        std::function<void(Expr)> processExpr = [&](Expr e) {
          if (!e) return;
          
          // Check for integer constants (MPZ)
          if (isOpX<MPZ>(e)) {
            mpz_class val = getTerm<mpz_class>(e); // Get value for debugging
            unsigned int width = binaryLog(val);
            // --- Debugging Added ---
            if (debug >= 3) { 
                outs() << "Lia2Bv::findMinBitWidth(rules): Found constant " << val.get_str() 
                       << ", requires width " << width << ". Current maxWidth = " << maxWidth << "\n";
            }
            // --- End Debugging ---
            maxWidth = std::max(maxWidth, width); 
            // --- Debugging Added ---
            if (debug >= 3) { 
                outs() << "Lia2Bv::findMinBitWidth(rules): Updated maxWidth = " << maxWidth << "\n";
            }
            // --- End Debugging ---
          }
          
          // Recursively process all arguments
          for (unsigned i = 0; i < e->arity(); ++i) {
            processExpr(e->arg(i));
          }
        };

        // Process all rules and involved variables/constants
        for (const auto& rule : rules) {
          processExpr(rule.body);
          // Also consider variables if they imply range constraints, though less direct
          // for (const auto& v : rule.srcVars) processExpr(v); // Variables usually don't have intrinsic width
          // for (const auto& v : rule.dstVars) processExpr(v);
          // for (const auto& v : rule.locVars) processExpr(v);
        }

        // Ensure minimum width (e.g., 4 bits)
        maxWidth = std::max(maxWidth, (unsigned int)4);

        // Optional: Round up to nearest power of 2 (common practice)
        // unsigned int pow2 = 4;
        // while (pow2 < maxWidth) pow2 *= 2;
        // return pow2;
        
        // Or just return the calculated max width
        return maxWidth;
      }

      // --- New Overload Added ---
      // Calculate minimum bit width required for a single expression
      unsigned int findMinBitWidth(Expr e)
      {
          unsigned int exprMaxWidth = 1; // Minimum width is 1

          std::function<void(Expr)> processExpr = [&](Expr node) {
              if (!node) return;

              if (isOpX<MPZ>(node)) {
                  mpz_class val = getTerm<mpz_class>(node);
                  unsigned int width = binaryLog(val);
                  // Debugging
                  if (debug >= 3) {
                      outs() << "Lia2Bv::findMinBitWidth(Expr): Found constant " << val.get_str()
                             << ", requires width " << width << ". Current exprMaxWidth = " << exprMaxWidth << "\n";
                  }
                  exprMaxWidth = std::max(exprMaxWidth, width);
                  if (debug >= 3) {
                      outs() << "Lia2Bv::findMinBitWidth(Expr): Updated exprMaxWidth = " << exprMaxWidth << "\n";
                  }
              }

              for (unsigned i = 0; i < node->arity(); ++i) {
                  processExpr(node->arg(i));
              }
          };

          processExpr(e);
          return exprMaxWidth; // Just return width needed for constants in 'e'
      }
      // --- End New Overload ---


    public:
      Lia2BvTranslator(ExprFactory &efac, EZ3 &z3, unsigned width = 4, int _debug = 0) : 
        m_efac(efac), m_z3(z3), m_width(width), debug(_debug) {}

      // --- New Method Added ---
      void setOriginalBvWidth(unsigned width) {
          m_original_bv_width = width;
          if (debug >= 2 && m_original_bv_width > 0) {
              outs() << "Lia2Bv: Original BV width set to " << m_original_bv_width << "\n";
          }
      }
      // --- End New Method ---


      CHCs translate(CHCs &input)
      {
        // Clear maps before translation
        m_var_map.clear();
        m_decl_map.clear();
        m_original_bv_width = 0; // Reset in case translator is reused

        // --- Modification: Detect original BV width ---
        if (input.hasBV) {
            for (Expr decl : input.decls) {
                if (decl && decl->arity() > 1) {
                    // Check sorts (args 1 to N-1)
                    for (unsigned i = 1; i < decl->arity() - 1; ++i) {
                        Expr sort = decl->arg(i);
                        if (isOpX<BVSORT>(sort)) {
                            m_original_bv_width = bv::width(sort);
                            if (debug >= 2) {
                                outs() << "Lia2Bv::translate(CHCs): Detected original BV width " << m_original_bv_width << " from decl " << *decl << "\n";
                            }
                            goto width_detected; // Found it, stop searching
                        }
                    }
                }
            }
            width_detected:; // Label to jump to after finding width
        }
        // --- End Modification ---


        // Calculate minimum required bitwidth based on constants in the input LIA CHCs
        unsigned const_width = findMinBitWidth(input.chcs);
        // --- Modification: Use max of const_width and original_bv_width ---
        m_width = std::max({const_width, m_original_bv_width, (unsigned)4}); // Ensure at least 4
        
        if (debug >= 2) {
          outs() << "Lia2Bv::translate(CHCs): Width from constants: " << const_width 
                 << ", Original BV width: " << m_original_bv_width 
                 << ". Using final initial width: " << m_width << "\n";
        }

        CHCs result(m_efac, m_z3, input.debug);

        // Copy basic fields first
        result.failDecl = input.failDecl; // Keep original failDecl name/Expr
        result.debug = input.debug;
        result.hasQuery = input.hasQuery;
        result.hasArrays = input.hasArrays; // Should be false if input is LIA
        result.hasAnyArrays = input.hasAnyArrays; // Should be false
        result.hasBV = true; // Set to true since we're translating to BV
        result.glob_ind = input.glob_ind;

        // Copy checking sets
        result.chcsToCheck1 = input.chcsToCheck1; 
        result.chcsToCheck2 = input.chcsToCheck2;
        result.toEraseChcs = input.toEraseChcs;
        
        // 1. Translate declarations and create new variables
        result.decls = translateDeclarations(input.decls);

        // 2. Create new variable maps 
        translateVariableMaps(input, result);

        // 3. Translate CHC rules (pass input and result)
        result.chcs = translateClauses(input.chcs, input, result);

        // 4. Copy cycle information
        result.cycleSearchDone = input.cycleSearchDone;
        result.loopheads = input.loopheads;
        result.cycles = input.cycles;
        result.prefixes = input.prefixes;
        result.acyclic = input.acyclic;
        result.seqPoints = input.seqPoints;

        // 5. Handle WTO information 
        result.wtoDecls.clear();
        
        // First translate all declarations and ensure they exist in the map
        for (auto decl : input.wtoDecls) { // decl is the original full LIA declaration Expr
          if (decl && !isOpX<TRUE>(decl)) {  // Only process valid declarations
            auto it = m_decl_map.find(decl); // Find using original full decl
            // It's possible a decl in wtoDecls is not in the main decls if simplified away
            if (it != m_decl_map.end()) {
                result.wtoDecls.push_back(it->second); // Store the translated full BV declaration Expr
            } else if (decl->arg(0) != input.failDecl) { // Check name against failDecl name
                 if (debug >= 1) outs() << "Warning: WTO decl " << *decl << " not found in map during LIA->BV translation.\n";
                 // Decide how to handle this - skip or assert? Skipping for now.
            }
          }
        }

        // Clear both pointer lists before rebuilding
        result.wtoCHCs.clear();
        result.dwtoCHCs.clear();

        // Map original rule pointers to their index in the input.chcs vector
        std::map<const HornRuleExt*, size_t> inputRuleIndex;
        for(size_t i = 0; i < input.chcs.size(); ++i) {
            inputRuleIndex[&input.chcs[i]] = i;
        }

        // Iterate through the *original* wtoCHCs list
        for (const HornRuleExt* origWtoRulePtr : input.wtoCHCs) {
            if (!origWtoRulePtr) continue;

            // Find the index of this rule in the original CHCs
            auto idxIt = inputRuleIndex.find(origWtoRulePtr);
            if (idxIt == inputRuleIndex.end()) {
                 assert(false && "Original WTO rule not found in input CHCs during LIA->BV translation");
                 continue;
            }
            size_t ruleIndex = idxIt->second;

            // Ensure the index is valid for the translated rules
            if (ruleIndex < result.chcs.size()) {
                // Get the pointer to the corresponding translated rule
                HornRuleExt* translatedRulePtr = &result.chcs[ruleIndex];

                // Basic sanity check (optional but good)
                #ifndef NDEBUG // Only include assertions in debug builds
                Expr expectedTranslatedSrcName;
                if (isOpX<TRUE>(origWtoRulePtr->srcRelation)) {
                    expectedTranslatedSrcName = mk<TRUE>(m_efac);
                } else {
                    Expr originalSrcDecl = input.getDeclByName(origWtoRulePtr->srcRelation); // Get original full decl by name
                    assert(originalSrcDecl && "Original WTO source declaration not found");
                    auto srcIt = m_decl_map.find(originalSrcDecl); // Find translated full decl
                    assert(srcIt != m_decl_map.end() && "WTO Source relation not found in decl_map");
                    expectedTranslatedSrcName = srcIt->second->arg(0); // Get translated name
                }

                Expr expectedTranslatedDstName;
                if (origWtoRulePtr->dstRelation == input.failDecl) { // Compare names
                    expectedTranslatedDstName = result.failDecl; // Use result's failDecl name
                } else {
                    Expr originalDstDecl = input.getDeclByName(origWtoRulePtr->dstRelation); // Get original full decl by name
                    assert(originalDstDecl && "Original WTO destination declaration not found");
                    auto dstIt = m_decl_map.find(originalDstDecl); // Find translated full decl
                    assert(dstIt != m_decl_map.end() && "WTO Destination relation not found in decl_map");
                    expectedTranslatedDstName = dstIt->second->arg(0); // Get translated name
                }

                // Compare translated rule's name with expected translated name
                assert(translatedRulePtr->srcRelation == expectedTranslatedSrcName && "WTO Source relation mismatch after LIA->BV translation");
                assert(translatedRulePtr->dstRelation == expectedTranslatedDstName && "WTO Destination relation mismatch after LIA->BV translation");
                #endif

                result.wtoCHCs.push_back(translatedRulePtr);
                if (!translatedRulePtr->isQuery) { // Check the translated rule's property
                    result.dwtoCHCs.push_back(translatedRulePtr);
                }
            } else {
                assert(false && "Rule index out of bounds after LIA->BV translation");
            }
        }


        if (debug >= 3) {
          outs() << "Lia2Bv: Built wtoCHCs with " << result.wtoCHCs.size() << " rules\n";
          outs() << "Lia2Bv: Built dwtoCHCs with " << result.dwtoCHCs.size() << " rules\n";
        }

        // Re-run cycle detection to ensure consistency  
        result.cycleSearchDone = false; // Force recalculation
        result.findCycles(); // This rebuilds outgs internally

        return result;
      }

      // Add public method to translate individual expressions
      Expr translateExpr(Expr e, unsigned width = 0)
      {
        // --- Modification Starts ---
        unsigned original_width = m_width; // Store the class's default width (set by translate(CHCs&))
        unsigned target_width = width;     // Start with the explicitly provided width

        if (target_width == 0) { // If no width was provided by the caller
            unsigned required_width = findMinBitWidth(e); // Calculate width needed for constants in this specific expression 'e'
            // Use the maximum of the width required by 'e', the default width calculated from the original CHCs, and the original BV width.
            target_width = std::max({required_width, original_width, m_original_bv_width}); 
            if (debug >= 2) {
                 outs() << "Lia2Bv::translateExpr: No width provided. Calculated required: " << required_width 
                        << ", CHC default: " << original_width 
                        << ", Original BV: " << m_original_bv_width 
                        << ". Using target width: " << target_width << "\n";
            }
        } else {
             // If width > 0, the caller explicitly requested a width.
             // Ensure it's not smaller than the original BV width, if one exists.
             unsigned enforced_width = std::max(target_width, m_original_bv_width);
             if (debug >= 2) {
                 outs() << "Lia2Bv::translateExpr: Width provided: " << width 
                        << ", Original BV: " << m_original_bv_width 
                        << ". Using target width: " << enforced_width << "\n";
             }
             target_width = enforced_width;
        }

        m_width = target_width; // Temporarily set the class width for the helper function call below
        // --- Modification Ends ---
        
        // Ensure maps are initialized if called standalone (might need context)
        // For now, assume maps are populated by a prior call to translate(CHCs&)
        // or handle initialization explicitly if needed for standalone use.
        Expr result = translateExprHelper(e); // This helper uses the temporarily set m_width

        m_width = original_width; // Restore original class default width before returning
        return result;
      }

    private:
      ExprSet translateDeclarations(const ExprSet &decls)
      {
        ExprSet result;
        for (Expr decl : decls) // decl is the original full LIA declaration Expr
        {
          if (decl == NULL) continue;
          
          ExprVector sorts;
          // Start from index 1 to skip the relation name (arg 0)
          for (unsigned i = 1; i < decl->arity()-1; i++) // Stop before the Bool return type
          {
            Expr sort = decl->arg(i);
            // Handle INT_TY sorts - convert to BVSORT
            if (isOpX<INT_TY>(sort)) {
              sorts.push_back(bv::bvsort(m_width, m_efac)); // Use calculated/provided m_width
            }
            // Handle other sorts (keep as is)
            else {
              sorts.push_back(sort);
            }
            
            if (debug >= 3) {
              outs() << "Translating sort: " << *sort 
                     << " to: " << *sorts.back() << "\n";
            }
          }
          
          // Add boolean return type
          sorts.push_back(mk<BOOL_TY>(m_efac));
          
          // Create new declaration with translated types, keeping original name
          Expr newDecl = bind::fdecl(decl->arg(0), sorts); // Use original name decl->arg(0)
          m_decl_map[decl] = newDecl; // Map original full decl to translated full decl

          if (debug >= 3) {
            outs() << "Translated declaration " << *decl 
                   << " to " << *newDecl << "\n";
          }

          result.insert(newDecl);
        }
        return result;
      }

      void translateVariableMaps(const CHCs &input, CHCs &output)
      {
        // Translate invVars
        output.invVars.clear();
        for (const auto &kv : input.invVars) // kv.first is relation name (Expr)
        {
            Expr originalDecl = input.getDeclByName(kv.first); // Find original full decl
            if (!originalDecl) {
                 if (debug >= 1) outs() << "Warning: Declaration for invVar " << *kv.first << " not found.\n";
                 continue;
            }
            auto it = m_decl_map.find(originalDecl); // Find translated full decl
            if (it != m_decl_map.end()) {
                Expr translatedName = it->second->arg(0); // Get translated name
                output.invVars[translatedName] = translateInvVars(kv.second, true); // Map translated name to translated vars
            } else {
                 if (debug >= 1) outs() << "Warning: Translated declaration for invVar " << *kv.first << " not found in map.\n";
            }
        }

        // Translate invVarsPrime similarly
        output.invVarsPrime.clear();
        for (const auto &kv : input.invVarsPrime) // kv.first is relation name (Expr)
        {
            Expr originalDecl = input.getDeclByName(kv.first); // Find original full decl
             if (!originalDecl) {
                 if (debug >= 1) outs() << "Warning: Declaration for invVarPrime " << *kv.first << " not found.\n";
                 continue;
            }
            auto it = m_decl_map.find(originalDecl); // Find translated full decl
            if (it != m_decl_map.end()) {
                Expr translatedName = it->second->arg(0); // Get translated name
                output.invVarsPrime[translatedName] = translateInvVars(kv.second, true); // Map translated name to translated vars
            } else {
                 if (debug >= 1) outs() << "Warning: Translated declaration for invVarPrime " << *kv.first << " not found in map.\n";
            }
        }
      }

      // Update signature to accept input and result CHCs
      std::vector<HornRuleExt> translateClauses(const std::vector<HornRuleExt> &rules, const CHCs& input, CHCs& result)
      {
        std::vector<HornRuleExt> translatedRules;
        for (const auto &rule : rules)
        {
          HornRuleExt newRule = rule; // Copy basic structure

          // Translate source relation name
          if (!isOpX<TRUE>(rule.srcRelation)) { // rule.srcRelation is the NAME
              Expr originalDecl = input.getDeclByName(rule.srcRelation); // Get original full decl by name
              assert(originalDecl && "Original source declaration not found");
              auto it = m_decl_map.find(originalDecl); // Find translated full decl using original full decl as key
              assert(it != m_decl_map.end() && "Source relation not found in decl_map during LIA->BV translation");
              newRule.srcRelation = it->second->arg(0); // Set to translated NAME
          } else {
              newRule.srcRelation = mk<TRUE>(m_efac); // Keep TRUE as TRUE
          }

          // Translate destination relation name
          if (rule.dstRelation != input.failDecl) { // rule.dstRelation is the NAME, compare with failDecl NAME
              Expr originalDecl = input.getDeclByName(rule.dstRelation); // Get original full decl by name
              assert(originalDecl && "Original destination declaration not found");
              auto it = m_decl_map.find(originalDecl); // Find translated full decl using original full decl as key
              assert(it != m_decl_map.end() && "Destination relation not found in decl_map during LIA->BV translation");
              newRule.dstRelation = it->second->arg(0); // Set to translated NAME
          } else {
              newRule.dstRelation = result.failDecl; // Use failDecl name from the target CHC
          }

          // Translate variables (ensure maps are populated correctly before this)
          // This uses m_var_map implicitly via translateInvVars
          translateRuleVariables(newRule); 

          // Translate body constraints
          newRule.body = fixFormatting(translateExprHelper(rule.body)); // Use helper, translateExpr uses m_var_map

          // Clear fields that need rebuilding based on translated vars/relations
          // These were specific to the original rule structure and parsing
          newRule.lin.clear();
          newRule.origSrc.clear();
          newRule.origDst.clear();
          newRule.origSrcVars.clear();

          translatedRules.push_back(newRule);
        }
        return translatedRules;
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

        // Handle ITE expressions 
        if (isOpX<ITE>(e)) {
          // --- Add Arity Check ---
          if (e->arity() != 3) {
               if (debug >= 1) outs() << "Warning: Malformed ITE expression encountered (arity != 3): " << *e << "\n";
               return mk<TRUE>(m_efac); // CORRECTED: Return boolean TRUE as a safe fallback
          }
          // --- End Arity Check ---
          Expr cond = translateExprHelper(e->arg(0)); // Recursive call
          Expr thenBranch = translateExprHelper(e->arg(1)); // Recursive call
          Expr elseBranch = translateExprHelper(e->arg(2)); // Recursive call
          
          // If condition was originally boolean (not LIA Int), it remains boolean.
          // If condition was LIA Int, it's now BV. Convert BV1 to boolean for ITE.
          if (isOpX<BVSORT>(typeOf(cond)) && width(typeOf(cond)) == 1) {
            cond = bv::tobool(cond); // Convert bv1 to bool
          }
          // If original condition was bool, cond is already bool.
          
          return mk<ITE>(cond, thenBranch, elseBranch);
        }
        
        // Handle variables (constants in Expr terminology)
        if (bind::IsConst()(e))
          return translateVar(e); // Uses m_var_map

        // Handle integer literals (MPZ)
        if (isOpX<MPZ>(e))
        {
          mpz_class val = getTerm<mpz_class>(e);
          // Convert LIA constant to BV constant using calculated width
          return bv::bvnum(val, m_width, m_efac); 
        }

        // Handle LIA arithmetic operations -> BV operations (signed)
        if (isOpX<PLUS>(e))
          return bv::bvadd(translateExprHelper(e->left()), translateExprHelper(e->right()));
        else if (isOpX<MINUS>(e))
          // Use bvsub for consistency, though mk<BSUB> might work
          return mk<expr::op::BSUB>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<MULT>(e))
          // Use bvmul for consistency
          return mk<expr::op::BMUL>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<DIV>(e)) { 
          // LIA division (integer division towards zero) -> Signed BV division (BSDIV)
          Expr left = translateExprHelper(e->left());
          Expr right = translateExprHelper(e->right());
          // Add check for division by zero? Z3 handles it by returning uninterpreted value.
          return mk<BSDIV>(left, right); 
        }
        else if (isOpX<IDIV>(e)) { 
          // LIA floor division -> Signed BV division (BSDIV) - Note: Semantics differ for negative numbers!
          // LIA IDIV: floor(a/b). BSDIV: round towards zero(a/b).
          // This translation might be imprecise.
          if (debug >= 1) outs() << "Warning: Translating LIA IDIV to BSDIV, semantics may differ.\n";
          Expr left = translateExprHelper(e->left());
          Expr right = translateExprHelper(e->right());
          return mk<BSDIV>(left, right);
        }
        else if (isOpX<MOD>(e)) {
          // LIA modulo -> Signed BV remainder (BSREM) - Note: Semantics differ for negative numbers!
          // LIA MOD: a - b*floor(a/b). BSREM: a - b*(a bvsdiv b).
          // This translation might be imprecise.
          if (debug >= 1) outs() << "Warning: Translating LIA MOD to BSREM, semantics may differ.\n";
          Expr left = translateExprHelper(e->left());
          Expr right = translateExprHelper(e->right());
          return mk<BSREM>(left, right);
        }
        else if (isOpX<UN_MINUS>(e)) // LIA unary minus -> BV negation
          return bv::bvneg(translateExprHelper(e->left()));
          
        // Handle LIA comparisons -> Signed BV comparisons
        else if (isOpX<LEQ>(e))
          return bv::bvsle(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<LT>(e))
          return bv::bvslt(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<GEQ>(e))
          return bv::bvsge(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<GT>(e))
          return bv::bvsgt(translateExprHelper(e->left()), translateExprHelper(e->right())); 
        else if (isOpX<EQ>(e)) // Equality
          return mk<EQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));
        else if (isOpX<NEQ>(e)) // Inequality
          return mk<NEQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          
        // Keep boolean operations (AND, OR, NOT, IMPL, IFF, XOR) untranslated
        else if (isOp<BoolOp>(e))
        {
          ExprVector args;
          for (unsigned i = 0; i < e->arity(); i++)
            args.push_back(translateExprHelper(e->arg(i))); // Recursive call
          return e->efac().mkNary(e->op(), args); // Reconstruct with same operator
        }
        
        // Handle FAPP (relation calls)
        else if (isOpX<FAPP>(e))
        {
            // --- Add Arity Check ---
            if (e->arity() < 1) {
                 if (debug >= 1) outs() << "Warning: Malformed FAPP expression encountered (arity < 1): " << *e << "\n";
                 return mk<TRUE>(m_efac); // CORRECTED: Return boolean TRUE as a safe fallback
            }
            // --- End Arity Check ---
            Expr fdecl = e->arg(0); // This is the FDECL expression
            Expr originalName = bind::fname(fdecl); // Get the name Expr

            // Find the original full declaration using the name
            // This requires access to the input CHCs context.
            // Assuming m_decl_map maps original full decl to translated full decl.
            // Need a way to find the original decl from name or context.
            // Fallback: Assume fdecl itself is the key if it was in input.decls.
            auto decl_it = m_decl_map.find(fdecl);
            Expr translated_fdecl;
            if (decl_it != m_decl_map.end()) {
                translated_fdecl = decl_it->second;
            } else {
                if (debug >= 1) outs() << "Warning: FDECL " << *fdecl << " not found in decl_map during FAPP translation.\n";
                translated_fdecl = fdecl; // Keep original as fallback
            }

            ExprVector args;
            args.push_back(translated_fdecl); // Use translated FDECL
            // Translate arguments recursively
            // Loop starts from 1, safe even if arity is 1
            for (unsigned i = 1; i < e->arity(); ++i)
              args.push_back(translateExprHelper(e->arg(i))); // Recursive call
            return mknary<FAPP>(args);
        }


        // Any other operation - recursively translate args and keep operator
        // This might cover UFs or other non-LIA/Bool constructs if present.
        if (debug >= 1) outs() << "Warning: Translating unknown operator " << e->op() << " recursively.\n";
        ExprVector args;
        for (unsigned i = 0; i < e->arity(); i++)
          args.push_back(translateExprHelper(e->arg(i)));
        return e->efac().mkNary(e->op(), args);
      }

      Expr fixFormatting(Expr e)
      {
        // Fix rules that end with NULL (should not happen with proper parsing/translation)
        if (e == NULL) 
        {
          if (debug >= 1) outs() << "Warning: Encountered NULL expression in fixFormatting.\n";
          return mk<FALSE>(m_efac); // Return FALSE instead of NULL
        }

        // Recursively fix formatting for arguments
        ExprVector args;
        bool changed = false;
        for (unsigned i = 0; i < e->arity(); i++)
        {
          Expr oldArg = e->arg(i);
          Expr newArg = fixFormatting(oldArg);
          args.push_back(newArg);
          if (oldArg != newArg) changed = true;
        }

        // If no arguments or no changes, return original expression
        if (args.empty() || !changed) return e;
        
        // Reconstruct expression with fixed arguments
        return e->efac().mkNary(e->op(), args);
      }
  };
}

#endif
