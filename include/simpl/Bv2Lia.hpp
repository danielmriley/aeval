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
      std::map<Expr, Expr> m_decl_map;     // Maps BV decls (full Expr) to LIA decls (full Expr)
      std::map<Expr, Expr> m_bvToLiaDeclMap; // Map from BV decl expr to LIA decl expr

      // Translation helpers
      static bool isBVSort(Expr e) { return isOpX<BVSORT>(e); }
      // static bool isBVVar(Expr e) { return isOpX<FAPP>(e) && isBVSort(e->first()->last()); } // Keep commented or remove

      Expr translateVar(Expr var)
      {
        auto it = m_var_map.find(var);
        if (it != m_var_map.end())
            return it->second;
            
        // Check if it's a BV variable based on its structure and type
        Expr varType = bind::typeOf(var);
        // if (!bv::is_bvvar(var)) { // OLD CHECK
        if (!(isOpX<FAPP>(var) && varType && isOpX<BVSORT>(varType))) { // NEW CHECK
          if (m_debug >= 3) outs() << "Kept non-BV var: " << *var << " (type: " << (varType ? varType : Expr()) << ")\n";
          return var;
        }

        // Create new integer variable using m_efac directly
        Expr name = bind::fname(bind::fname(var)); // Get the name Expr (e.g., _FH_3)
        Expr liaType = mk<INT_TY>(m_efac);         // Define the LIA type
        
        // Explicitly create the FDECL with the name and INT_TY
        Expr liaFdecl = mk<FDECL>(name, liaType); 
        
        // Create the FAPP using the newly created FDECL
        Expr translatedVar = mk<FAPP>(liaFdecl); 
        
        m_var_map[var] = translatedVar; // Cache the translation

        if (m_debug >= 3) {
          outs() << "Mapped BV var " << *var << " (type: " << *bind::typeOf(var) << ")"
                 << " to LIA var " << *translatedVar 
                 << " (type: " << *bind::typeOf(translatedVar) << ")\n"; 
        }
        return translatedVar;
      }

      ExprVector translateInvVars(const ExprVector &origVars, bool cacheVars = false)
      {
        ExprVector translatedVars;
        for (const auto &var : origVars)
        {
          if(m_debug >= 3) {
            outs() << "Translating var: " << *var << "\n";
            outs() << "Searching for var: " << *var << "\n";
            outs() << "var type: " << bind::typeOf(var) << "\n";
          }
          // Check if it's a BV variable before attempting translation
          Expr varType = bind::typeOf(var);
          // if (!bv::is_bvvar(var)) { // OLD CHECK
          if (!(isOpX<FAPP>(var) && varType && isOpX<BVSORT>(varType))) { // NEW CHECK
             translatedVars.push_back(var); // Keep non-BV vars as is
             if (m_debug >= 3) {
               outs() << "Kept non-BV var: " << *var << " (type: " << (varType ? varType : Expr()) << ")\n";
             }
             continue;
          }

          // Use the same translation logic as translateVar
          Expr name = bind::fname(bind::fname(var));
          Expr liaType = mk<INT_TY>(m_efac);
          
          // Explicitly create the FDECL with the name and INT_TY
          Expr liaFdecl = mk<FDECL>(name, liaType);
          
          // Create the FAPP using the newly created FDECL
          Expr liaVar = mk<FAPP>(liaFdecl);          
          
          if(m_debug >= 3) {
            outs() << "Mapped BV var " << *var << " (type: " << *bind::typeOf(var) << ")"
                   << " to LIA var " << *liaVar 
                   << " (type: " << *bind::typeOf(liaVar) << ")\n"; 
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
        // Clear maps before translation
        m_var_map.clear();
        m_decl_map.clear();

        CHCs result(m_efac, m_z3, input.debug);
        
        // Copy basic fields first
        result.failDecl = input.failDecl; // Keep the original failDecl name/Expr
        result.debug = input.debug;
        result.hasQuery = input.hasQuery;
        result.hasArrays = input.hasArrays;
        result.hasAnyArrays = input.hasAnyArrays;
        result.hasBV = false; // Set to false since we're translating to LIA
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
        
        // Iterate through the original BV relation names in wtoDecls
        for (auto bvRelName : input.wtoDecls) { // Assume bvRelName is the Expr representing the relation name

          // Skip TRUE or failDecl names
          if (!bvRelName || isOpX<TRUE>(bvRelName) || bvRelName == input.failDecl) {
              // --- Fix: Use Expr in ternary operator ---
              if (m_debug >= 3) outs() << "Skipping WTO translation for special name: " << (bvRelName ? bvRelName : Expr()) << "\n";
              // --- End Fix ---
              continue;
          }

          // Find the original full BV declaration using the name
          Expr originalBvDecl = input.getDeclByName(bvRelName);

          if (!originalBvDecl) {
              // This can happen if the declaration was simplified away after WTO calculation
              if (m_debug >= 1) outs() << "Warning: Original BV declaration for WTO relation name '" << *bvRelName << "' not found in input.decls (likely simplified).\n";
              continue; // Skip if the original declaration doesn't exist
          }

          // Find the translated full LIA declaration in the map using the original full BV decl as the key
          auto it = m_decl_map.find(originalBvDecl);
          if (it != m_decl_map.end()) {
              result.wtoDecls.push_back(it->second->arg(0)); // Store the translated relation NAME Expr
              if (m_debug >= 3) outs() << "Mapped WTO BV decl " << *originalBvDecl << " to LIA decl name " << *it->second->arg(0) << "\n";
          } else {
              // This case should ideally not happen if originalBvDecl was found and translateDeclarations worked correctly.
              if (m_debug >= 1) outs() << "Warning: Translated LIA declaration for BV decl '" << *originalBvDecl << "' not found in m_decl_map.\n";
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
                 assert(false && "Original WTO rule not found in input CHCs during BV->LIA translation");
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
                assert(translatedRulePtr->srcRelation == expectedTranslatedSrcName && "WTO Source relation mismatch after BV->LIA translation");
                assert(translatedRulePtr->dstRelation == expectedTranslatedDstName && "WTO Destination relation mismatch after BV->LIA translation");
                #endif

                result.wtoCHCs.push_back(translatedRulePtr);
                if (!translatedRulePtr->isQuery) { // Check the translated rule's property
                    result.dwtoCHCs.push_back(translatedRulePtr);
                }
            } else {
                assert(false && "Rule index out of bounds after BV->LIA translation");
            }
        }

        if (m_debug >= 3) {
          outs() << "Bv2Lia: Built wtoCHCs with " << result.wtoCHCs.size() << " rules\n";
          outs() << "Bv2Lia: Built dwtoCHCs with " << result.dwtoCHCs.size() << " rules\n";
        }

        // Re-run cycle detection to ensure consistency
        result.cycleSearchDone = false; // Force recalculation
        result.findCycles(); // This rebuilds outgs internally

        return result;
      }

      // Add public method to translate individual expressions
      Expr translateExpr(Expr e) 
      {
        // Ensure maps are initialized if called standalone (might need context)
        // For now, assume maps are populated by a prior call to translate(CHCs&)
        // or handle initialization explicitly if needed for standalone use.
        // if (m_var_map.empty() && m_decl_map.empty())
        // {
        //   // Handle standalone translation context setup if necessary
        // }
        return translateExprHelper(e);
      }

      // Add getter for the BV to LIA declaration map
      const std::map<Expr, Expr>& getBvToLiaDeclMap() const {
        // +++ Debugging +++
        if (m_debug >= 4) {
            outs() << "Bv2LiaTranslator::getBvToLiaDeclMap() called. Map size: " << m_bvToLiaDeclMap.size() << "\n";
            for (const auto& pair : m_bvToLiaDeclMap) {
                 if (pair.first && pair.second) {
                     outs() << "  Map Entry: BV=" << *(pair.first) << " -> LIA=" << *(pair.second) << "\n";
                 }
            }
        }
        // +++ End Debugging +++
        return m_bvToLiaDeclMap;
      }

    private:
      ExprSet translateDeclarations(const ExprSet &decls)
      {
        ExprSet result;
        m_decl_map.clear(); // Clear previous declaration mappings
        m_bvToLiaDeclMap.clear(); // Clear the BV->LIA map too

        for (Expr decl : decls) // decl is the original full declaration Expr
        {
          if (decl == NULL) continue;
          
          ExprVector sorts;
          // Start from index 1 to skip the relation name (arg 0)
          for (unsigned i = 1; i < decl->arity()-1; i++) // Stop before the Bool return type
          {
            Expr sort = decl->arg(i);
            // Handle BV sorts - convert to INT_TY
            if (isOpX<BVSORT>(sort)) {
              sorts.push_back(mk<INT_TY>(m_efac));
            }
            // Handle other sorts (keep as is)
            else {
              sorts.push_back(sort);
            }
            
            if (m_debug >= 3) {
              outs() << "Translating sort: " << *sort 
                     << " to: " << *sorts.back() << "\n";
            }
          }
          
          // Add boolean return type
          sorts.push_back(mk<BOOL_TY>(m_efac));
          
          // Create new declaration with translated types, keeping original name
          Expr newDecl = bind::fdecl(decl->arg(0), sorts); // Use original name decl->arg(0)
          m_decl_map[decl] = newDecl; // Map original full decl to translated full decl
          m_bvToLiaDeclMap[decl->arg(0)] = newDecl->arg(0); // Map original BV name to translated LIA name

          if (m_debug >= 3) {
            outs() << "Translated declaration " << *decl 
                   << " to " << *newDecl << "\n";
            outs() << "Added to bvToLiaDeclMap: BV=" << *decl->arg(0) << " -> LIA=" << *newDecl->arg(0) << "\n";
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
                 if (m_debug >= 1) outs() << "Warning: Declaration for invVar " << *kv.first << " not found.\n";
                 continue;
            }
            auto it = m_decl_map.find(originalDecl); // Find translated full decl
            if (it != m_decl_map.end()) {
                Expr translatedName = it->second->arg(0); // Get translated name
                output.invVars[translatedName] = translateInvVars(kv.second, true); // Map translated name to translated vars
            } else {
                 if (m_debug >= 1) outs() << "Warning: Translated declaration for invVar " << *kv.first << " not found in map.\n";
            }
        }

        // Translate invVarsPrime similarly
        output.invVarsPrime.clear();
        for (const auto &kv : input.invVarsPrime) // kv.first is relation name (Expr)
        {
            Expr originalDecl = input.getDeclByName(kv.first); // Find original full decl
             if (!originalDecl) {
                 if (m_debug >= 1) outs() << "Warning: Declaration for invVarPrime " << *kv.first << " not found.\n";
                 continue;
            }
            auto it = m_decl_map.find(originalDecl); // Find translated full decl
            if (it != m_decl_map.end()) {
                Expr translatedName = it->second->arg(0); // Get translated name
                output.invVarsPrime[translatedName] = translateInvVars(kv.second, true); // Map translated name to translated vars
            } else {
                 if (m_debug >= 1) outs() << "Warning: Translated declaration for invVarPrime " << *kv.first << " not found in map.\n";
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
              assert(it != m_decl_map.end() && "Source relation not found in decl_map during BV->LIA translation");
              newRule.srcRelation = it->second->arg(0); // Set to translated NAME
          } else {
              newRule.srcRelation = mk<TRUE>(m_efac); // Keep TRUE as TRUE
          }

          // Translate destination relation name
          if (rule.dstRelation != input.failDecl) { // rule.dstRelation is the NAME, compare with failDecl NAME
              Expr originalDecl = input.getDeclByName(rule.dstRelation); // Get original full decl by name
              assert(originalDecl && "Original destination declaration not found");
              auto it = m_decl_map.find(originalDecl); // Find translated full decl using original full decl as key
              assert(it != m_decl_map.end() && "Destination relation not found in decl_map during BV->LIA translation");
              newRule.dstRelation = it->second->arg(0); // Set to translated NAME
          } else {
              newRule.dstRelation = result.failDecl; // Use failDecl name from the target CHC
          }

          // Translate variables (ensure maps are populated correctly before this)
          // This uses m_var_map implicitly via translateInvVars
          translateRuleVariables(newRule); 

          // Translate body constraints
          newRule.body = translateExprHelper(rule.body); // Use helper, translateExpr uses m_var_map

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
          // Handle ITE expressions
          if (isOpX<ITE>(e)) {
            // --- Add Arity Check ---
            if (e->arity() != 3) {
                 if (m_debug >= 1) outs() << "Warning: Malformed ITE expression encountered (arity != 3): " << *e << "\n";
                 return mk<TRUE>(m_efac); // Return TRUE as a safe fallback
            }
            // --- End Arity Check ---
            Expr cond = translateExprHelper(e->arg(0)); // Recursive call to helper
            Expr thenBranch = translateExprHelper(e->arg(1)); // Recursive call to helper
            Expr elseBranch = translateExprHelper(e->arg(2)); // Recursive call to helper
            
            // Handle potential BV1 to bool conversion in condition
            // Check the original expression's argument type
            if (isOpX<BVSORT>(typeOf(e->arg(0))) && width(typeOf(e->arg(0))) == 1) {
               // The translated condition 'cond' should be an integer constant
               // Convert it to a boolean comparison
               cond = mk<EQ>(cond, mkTerm(mpz_class(1), m_efac));
            } else if (bv::is_bvnum(e->arg(0)) && width(typeOf(e->arg(0))) == 1) {
               // Original was bvnum 1 or 0
               cond = mkTerm(toMpz(e->arg(0)) == 1, m_efac);
            }
            
            return mk<ITE>(cond, thenBranch, elseBranch);
          }

          // Handle variables (constants in Expr terminology)
          if (bind::IsConst()(e))
            return translateVar(e); // Uses m_var_map

          // Handle BV numeric constants
          if (bv::is_bvnum(e)) {
            mpz_class val = bv::toMpz(e);
            // Check numeric bounds (optional, consider if needed)
            // if (val > INT_MAX || val < INT_MIN) {
            //   if (m_debug) outs() << "Warning: Number out of safe range\n";
            //   // Decide how to handle out-of-range numbers, e.g., return TRUE?
            //   return mk<TRUE>(m_efac);
            // }
            return mkTerm(val, m_efac); // Convert BV constant to LIA constant
          }

          // Protect against unsafe operations - replace with TRUE?
          // Division/Modulo by zero is undefined in LIA as well.
          // Consider if specific handling is needed or if relying on solver is okay.
          // if (isOp<NumericOp>(e)) {
          //   if (containsOp<IDIV>(e) || containsOp<MOD>(e)) {
          //     // Potentially check for division by zero if possible?
          //     // Or just translate and let the LIA solver handle it.
          //     // return mk<TRUE>(m_efac); 
          //   }
          // }

          // Handle application expressions (relation calls in CHCs)
          if (isOpX<FAPP>(e))
          {
            // --- Add Arity Check ---
            if (e->arity() < 1) {
                 if (m_debug >= 1) outs() << "Warning: Malformed FAPP expression encountered (arity < 1): " << *e << "\n";
                 return mk<TRUE>(m_efac); // Return TRUE as a safe fallback
            }
            // --- End Arity Check ---
            Expr fdecl = e->arg(0); // This is the FDECL expression
            Expr originalName = bind::fname(fdecl); // Get the name Expr
            
            // Find the original full declaration using the name
            // This requires access to the input CHCs, which isn't directly available here.
            // Assuming m_decl_map maps original full decl to translated full decl.
            // We need a reverse map or a way to find the original decl.
            // For now, let's assume the FDECL's name is sufficient if unique,
            // or that the FDECL itself might be mapped if it was part of the input decls.

            // Try finding the FDECL itself in the map first
            auto decl_it = m_decl_map.find(fdecl);
            Expr translated_fdecl;
            if (decl_it != m_decl_map.end()) {
                translated_fdecl = decl_it->second;
            } else {
                // If FDECL not found, maybe only the name was used?
                // This part is tricky without the full context.
                // Let's assume for now we need to translate based on the name somehow,
                // or that this case shouldn't happen if declarations are handled correctly.
                // Fallback: keep original fdecl? Or error?
                if (m_debug >= 1) outs() << "Warning: FDECL " << *fdecl << " not found in decl_map during FAPP translation.\n";
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

          // Basic logical operators (AND, OR, NOT, IMPL, IFF, XOR)
          if (isOp<BoolOp>(e))
          {
            ExprVector args;
            for (unsigned i = 0; i < e->arity(); ++i)
              args.push_back(translateExprHelper(e->arg(i))); // Recursive call
            // Reconstruct with the same boolean operator
            return e->efac().mkNary(e->op(), args);
          }
          
          // Handle inequality expressions explicitly (NEQ)
          if (isOpX<NEQ>(e))
            return mk<NEQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));

          // Arithmetic operations (translate BV ops to LIA ops)
          else if (isOpX<BADD>(e))
            return mk<PLUS>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BSUB>(e))
            return mk<MINUS>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BMUL>(e))
            return mk<MULT>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BUDIV>(e)) // Unsigned division -> LIA division (integer)
            return mk<DIV>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
          else if (isOpX<BSDIV>(e)) // Signed division -> LIA division (integer)
            return mk<DIV>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
          else if (isOpX<BUREM>(e)) // Unsigned remainder -> LIA modulo
            return mk<MOD>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
          else if (isOpX<BSREM>(e)) // Signed remainder -> LIA modulo
            return mk<MOD>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
          else if (isOpX<BSMOD>(e)) // Signed modulo -> LIA modulo (Note: Z3's bvsmod semantics might differ slightly from LIA mod for negative numbers)
            return mk<MOD>(translateExprHelper(e->left()), translateExprHelper(e->right())); 
          
          // Comparisons (translate BV comparisons to LIA comparisons)
          // Both signed/unsigned translate to same LIA ops
          else if (isOpX<BULE>(e) || isOpX<BSLE>(e))
            return mk<LEQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BUGE>(e) || isOpX<BSGE>(e))
            return mk<GEQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BULT>(e) || isOpX<BSLT>(e))
            return mk<LT>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<BUGT>(e) || isOpX<BSGT>(e)) 
            return mk<GT>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          else if (isOpX<EQ>(e)) // Equality check
            return mk<EQ>(translateExprHelper(e->left()), translateExprHelper(e->right()));
          
          // Special bitvector operations
          else if (isOpX<BNEG>(e)) // Bitwise negation - No direct LIA equivalent, maybe handle as error or approximation?
             // Often used for two's complement negation: ~x + 1 == -x
             // If it's just bitwise NOT, it doesn't map well to LIA.
             // Let's translate as unary minus for now, assuming it represents negation.
             return mk<UN_MINUS>(translateExprHelper(e->left()));
          else if (isOpX<expr::op::BCONCAT>(e) || isOpX<expr::op::BEXTRACT>(e) || 
                   isOpX<expr::op::BASHR>(e) || isOpX<expr::op::BLSHR>(e) || isOpX<expr::op::BSHL>(e) ||
                   isOpX<expr::op::BXOR>(e) || isOpX<expr::op::BNAND>(e) || isOpX<expr::op::BNOR>(e) || isOpX<expr::op::BXNOR>(e) ||
                   isOpX<expr::op::BSEXT>(e) || isOpX<expr::op::BZEXT>(e) || // Add expr::op:: prefix here again
                   isOpX<BAND>(e) || isOpX<BOR>(e)) // Bitwise AND/OR don't map directly
          {
              // These operations don't have direct LIA equivalents.
              // Return TRUE or handle as an error/approximation.
              if (m_debug >= 1) outs() << "Warning: Unsupported BV operation encountered: " << e->op() << "\n";
              return mk<TRUE>(m_efac); 
          }


          // Default case: Recursively translate arguments for unknown/other operators
          // This might be needed for things like UFs or array operations if they exist.
          ExprVector newArgs;
          for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it)
            newArgs.push_back(translateExprHelper(*it)); // Recursive call
          
          // Reconstruct expression with the original operator and translated args
          // This assumes the operator itself doesn't need translation (e.g., UFs)
          return e->efac().mkNary(e->op(), newArgs);
        }
        catch (const std::exception& ex) {
          if (m_debug) outs() << "Error during translation of " << *e << ": " << ex.what() << "\n";
          // Return TRUE on error to avoid crashing, but signal potential issue
          return mk<TRUE>(m_efac); 
        }
        // Should not be reached if all cases are handled, but as a fallback:
        if (m_debug >=1) outs() << "Warning: Unhandled expression type in translateExprHelper: " << *e << "\n";
        return e; // Return original expression as fallback
      }
  };
} // namespace ufo

#endif
