#ifndef LIA2BV__HPP__
#define LIA2BV__HPP__

#include "deep/Horn.hpp"
#include "ufo/Smt/EZ3.hh" // Include necessary headers
#include "ufo/ExprBv.hh"
#include "ufo/Expr.hpp"
#include <cmath> // Needed for ceil and log2 (or manual calculation)
#include <limits> // Needed for numeric_limits

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

        // --- Fix: Check variable type, not if it's a constant literal ---
        // Check if it's an integer variable based on its type
        Expr varType = bind::typeOf(var);
        if (!(isOpX<FAPP>(var) && varType && isOpX<INT_TY>(varType))) { 
             if (debug >= 3) outs() << "Kept non-Int var: " << *var << " (type: " << (varType ? varType : Expr()) << ")\n";
             return var; // Keep non-integer vars as is
        }
        // --- End Fix ---
            
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
            // --- Fix: Check variable type, not if it's a constant literal ---
            // Check if it's an integer variable based on its type
            Expr varType = bind::typeOf(var);
            if (!(isOpX<FAPP>(var) && varType && isOpX<INT_TY>(varType))) {
                translatedVars.push_back(var); // Keep non-Int vars
                if (debug >= 3) outs() << "Kept non-Int invVar: " << *var << " (type: " << (varType ? varType : Expr()) << ")\n";
                continue;
            }
            // --- End Fix ---

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

      // --- New Helper Method Added ---
      // Rounds up to the nearest power of 2 if n > 4
      unsigned int adjustWidth(unsigned int n)
      {
        if (n <= 4) {
            return n; // Keep width if 4 or less
        }
        
        // Check if n is already a power of 2
        // (n & (n - 1)) == 0 handles n=0 incorrectly, but we ensured n > 4
        if ((n > 0) && ((n & (n - 1)) == 0)) {
            return n; // Already a power of 2
        }

        // Find the next power of 2
        unsigned int p = 1;
        // Use unsigned long long for intermediate to avoid overflow during shift
        unsigned long long p_ll = 1; 
        while (p_ll < n) {
            p_ll <<= 1;
            // Check if the result still fits in unsigned int
            if (p_ll > std::numeric_limits<unsigned int>::max()) {
                 if (debug >= 1) {
                     outs() << "Warning: Power of 2 calculation overflowed for width " << n 
                            << ". Returning original width.\n";
                 }
                 return n; // Return original width if overflow occurs
            }
        }
        return static_cast<unsigned int>(p_ll);
      }
      // --- End New Helper Method ---


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

        // --- Modification: Round up to power of 2 if > 4 ---
        unsigned int adjustedWidth = adjustWidth(maxWidth);
        if (debug >= 3 && adjustedWidth != maxWidth) {
            outs() << "Lia2Bv::findMinBitWidth(rules): Rounded maxWidth " << maxWidth 
                   << " up to power of 2: " << adjustedWidth << "\n";
        }
        return adjustedWidth;
        // --- End Modification ---
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
          
          // Ensure minimum width (e.g., 4 bits) before rounding
          exprMaxWidth = std::max(exprMaxWidth, (unsigned int)4);

          // --- Modification: Round up to power of 2 if > 4 ---
          unsigned int adjustedWidth = adjustWidth(exprMaxWidth);
          if (debug >= 3 && adjustedWidth != exprMaxWidth) {
              outs() << "Lia2Bv::findMinBitWidth(Expr): Rounded exprMaxWidth " << exprMaxWidth 
                     << " up to power of 2: " << adjustedWidth << "\n";
          }
          return adjustedWidth;
          // --- End Modification ---
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
        // This now incorporates the power-of-2 rounding logic.
        unsigned const_width = findMinBitWidth(input.chcs);
        // --- Modification: Use max of const_width and original_bv_width ---
        m_width = std::max({const_width, m_original_bv_width, (unsigned)4}); // Ensure at least 4
        
        if (debug >= 2) {
          outs() << "Lia2Bv::translate(CHCs): Width from constants (adjusted): " << const_width 
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
        
        // Iterate through the original LIA relation names in wtoDecls
        for (auto liaRelName : input.wtoDecls) { // Assume liaRelName is the Expr representing the relation name (e.g., 'inv')

          // Skip TRUE or failDecl names if they somehow end up here
          if (!liaRelName || isOpX<TRUE>(liaRelName) || liaRelName == input.failDecl) {
              if (debug >= 3) outs() << "Skipping WTO translation for special name: " << (liaRelName ? liaRelName : Expr()) << "\n";
              continue;
          }

          // Find the original full LIA declaration using the name
          Expr originalLiaDecl = input.getDeclByName(liaRelName);

          if (!originalLiaDecl) {
              // This can happen if the declaration was simplified away after WTO calculation
              if (debug >= 1) outs() << "Warning: Original LIA declaration for WTO relation name '" << *liaRelName << "' not found in input.decls (likely simplified).\n";
              continue; // Skip if the original declaration doesn't exist
          }

          // Find the translated full BV declaration in the map using the original full LIA decl as the key
          auto it = m_decl_map.find(originalLiaDecl);
          if (it != m_decl_map.end()) {
              result.wtoDecls.push_back(it->second->arg(0)); // Store the translated relation NAME Expr
              if (debug >= 3) outs() << "Mapped WTO LIA decl " << *originalLiaDecl << " to BV decl name " << *it->second->arg(0) << "\n";
          } else {
              // This case should ideally not happen if originalLiaDecl was found and translateDeclarations worked correctly.
              if (debug >= 1) outs() << "Warning: Translated BV declaration for LIA decl '" << *originalLiaDecl << "' not found in m_decl_map.\n";
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
                // --- Modification: Handle TRUE and failDecl in assertions ---
                Expr expectedTranslatedSrcName;
                if (isOpX<TRUE>(origWtoRulePtr->srcRelation)) {
                    expectedTranslatedSrcName = mk<TRUE>(m_efac);
                } else {
                    // Only call getDeclByName for non-TRUE relations
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
                    // Only call getDeclByName for non-failDecl relations
                    Expr originalDstDecl = input.getDeclByName(origWtoRulePtr->dstRelation); // Get original full decl by name
                    assert(originalDstDecl && "Original WTO destination declaration not found");
                    auto dstIt = m_decl_map.find(originalDstDecl); // Find translated full decl
                    assert(dstIt != m_decl_map.end() && "WTO Destination relation not found in decl_map");
                    expectedTranslatedDstName = dstIt->second->arg(0); // Get translated name
                }
                // --- End Modification ---

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
            // Calculate width needed for constants in 'e', rounded up if > 4
            unsigned required_width = findMinBitWidth(e); 
            // Use the maximum of the width required by 'e', the default width calculated from the original CHCs, and the original BV width.
            target_width = std::max({required_width, original_width, m_original_bv_width}); 
            if (debug >= 2) {
                 outs() << "Lia2Bv::translateExpr: No width provided. Calculated required (adjusted): " << required_width 
                        << ", CHC default: " << original_width 
                        << ", Original BV: " << m_original_bv_width 
                        << ". Using target width: " << target_width << "\n";
            }
        } else {
             // If width > 0, the caller explicitly requested a width.
             // Ensure it's not smaller than the original BV width, if one exists.
             // Also round up the requested width if > 4
             unsigned adjusted_requested_width = adjustWidth(target_width);
             if (debug >= 3 && adjusted_requested_width != target_width) {
                 outs() << "Lia2Bv::translateExpr: Rounded requested width " << target_width 
                        << " up to power of 2: " << adjusted_requested_width << "\n";
             }
             unsigned enforced_width = std::max({adjusted_requested_width, m_original_bv_width, (unsigned)4}); // Ensure at least 4
             if (debug >= 2) {
                 outs() << "Lia2Bv::translateExpr: Width provided: " << width 
                        << " (adjusted requested: " << adjusted_requested_width << ")"
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
            // --- Fix: Skip special names like TRUE or failDecl ---
            if (isOpX<TRUE>(kv.first) || kv.first == input.failDecl) {
                if (debug >= 3) outs() << "Skipping invVar translation for special name: " << *kv.first << "\n";
                continue;
            }
            // --- End Fix ---

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
            // --- Fix: Skip special names like TRUE or failDecl ---
            if (isOpX<TRUE>(kv.first) || kv.first == input.failDecl) {
                 if (debug >= 3) outs() << "Skipping invVarPrime translation for special name: " << *kv.first << "\n";
                 continue;
            }
            // --- End Fix ---

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
        {
          // --- Add check for BOOL_TY variables ---
          Expr varType = bind::typeOf(e);
          if (varType && isOpX<BOOL_TY>(varType)) {
              if (debug >= 3) outs() << "Kept BOOL var: " << *e << "\n";
              return e; // Keep BOOL variables as is
          }
          // --- End check for BOOL_TY variables ---
          return translateVar(e); // Uses m_var_map for other variable types
        }

        // Handle integer literals (MPZ)
        if (isOpX<MPZ>(e))
        {
          mpz_class val = getTerm<mpz_class>(e);
          // Convert LIA constant to BV constant using calculated width
          return bv::bvnum(val, m_width, m_efac); 
        }

        // Handle LIA arithmetic operations -> BV operations (signed)
        e = normalizePositive(e, m_efac, debug); // Normalize to remove unnecessary negations
        if (isOpX<PLUS>(e))
        {
          // Check for patterns that can be converted to BVSUB
          Expr left = e->left();
          Expr right = e->right();

          // Pattern 1: (-A) + B  => B - A
          if (isOpX<UN_MINUS>(left)) {
            Expr A = left->left();
            return mk<expr::op::BSUB>(translateExprHelper(right), translateExprHelper(A));
          }
          // Pattern 2: (MULT -1 A) + B => B - A
          if (isOpX<MULT>(left) && left->arity() == 2 && isOpX<MPZ>(left->left())) {
            mpz_class coef = getTerm<mpz_class>(left->left());
            if (coef == -1) {
              Expr A = left->right();
              return mk<expr::op::BSUB>(translateExprHelper(right), translateExprHelper(A));
            }
          }

          // Pattern 3: A + (-B) => A - B
          if (isOpX<UN_MINUS>(right)) {
            Expr B = right->left();
            return mk<expr::op::BSUB>(translateExprHelper(left), translateExprHelper(B));
          }
          // Pattern 4: A + (MULT -1 B) => A - B
          if (isOpX<MULT>(right) && right->arity() == 2 && isOpX<MPZ>(right->left())) {
            mpz_class coef = getTerm<mpz_class>(right->left());
            if (coef == -1) {
              Expr B = right->right();
              return mk<expr::op::BSUB>(translateExprHelper(left), translateExprHelper(B));
            }
          }

          // Default: Translate to BVADD
          return bv::bvadd(translateExprHelper(left), translateExprHelper(right));
        }
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
        // Handle BV operators if they appear in the input
        else if (isOpX<BAND>(e))
          return mk<BAND>(translateExprHelper(e->left()), translateExprHelper(e->right()));
        else if (isOpX<BOR>(e))
          return mk<BOR>(translateExprHelper(e->left()), translateExprHelper(e->right()));
        else if (isOpX<BSHL>(e))
          return mk<BSHL>(translateExprHelper(e->left()), translateExprHelper(e->right()));
        else if (isOpX<BLSHR>(e))
          return mk<BLSHR>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          
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
