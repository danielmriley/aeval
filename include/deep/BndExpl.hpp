#ifndef BNDEXPL__HPP__
#define BNDEXPL__HPP__

#include "Horn.hpp"
#include "Distribution.hpp"
#include "ae/AeValSolver.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"
#include "ufo/ExprBv.hh"
#include <algorithm>
#include <limits>
#include <chrono>
#include <sstream>
#include <cctype>
#include <fstream>
#include <iomanip>

using namespace std;
using namespace boost;
namespace ufo
{
  class BndExpl
  {
  private:
    ExprFactory &m_efac;
    SMTUtils u;
    CHCs &ruleManager;
    Expr extraLemmas;

  public:
    int64_t validatedTraceBound = -1;

  private:
    ExprVector bindVars1;

    int tr_ind; // helper vars
    int pr_ind;
    int k_ind;

    Expr inv; // 1-inductive proof

    bool debug;

    Expr toIntegerExpr(Expr val, double &asDouble, const cpp_int &maxDouble)
    {
      if (val == NULL)
        return NULL;

      cpp_int asInt;
      if (isOpX<MPZ>(val))
      {
        asInt = lexical_cast<cpp_int>(val);
      }
      else if (bv::is_bvnum(val) || bv::is_bvconst(val))
      {
        asInt = lexical_cast<cpp_int>(bv::toMpz(val).get_str());
      }
      else
      {
        return NULL;
      }

      if (asInt > maxDouble || asInt < -maxDouble)
        return NULL;

      asDouble = asInt.convert_to<double>();
      return mkMPZ(asInt, m_efac);
    }

    /**
     * Convert an Expr to SyGuS-compatible string for grammar production.
     * Handles BV comparisons and arithmetic expressions.
     */
    std::string exprToSyGuS(Expr e, unsigned varWidth, int stepWidth)
    {
      if (!e) return "";
      
      // For AND/OR, recursively process
      if (isOpX<AND>(e))
      {
        std::vector<std::string> parts;
        for (auto it = e->args_begin(); it != e->args_end(); ++it)
        {
          std::string part = exprToSyGuS(*it, varWidth, stepWidth);
          if (!part.empty()) parts.push_back(part);
        }
        if (parts.empty()) return "";
        if (parts.size() == 1) return parts[0];
        std::string result = "(and";
        for (auto& p : parts) result += " " + p;
        result += ")";
        return result;
      }
      
      if (isOpX<OR>(e))
      {
        std::vector<std::string> parts;
        for (auto it = e->args_begin(); it != e->args_end(); ++it)
        {
          std::string part = exprToSyGuS(*it, varWidth, stepWidth);
          if (!part.empty()) parts.push_back(part);
        }
        if (parts.empty()) return "";
        if (parts.size() == 1) return parts[0];
        std::string result = "(or";
        for (auto& p : parts) result += " " + p;
        result += ")";
        return result;
      }
      
      if (isOpX<NEG>(e))
      {
        std::string inner = exprToSyGuS(e->left(), varWidth, stepWidth);
        if (inner.empty()) return "";
        return "(not " + inner + ")";
      }
      
      // BV comparisons
      if (isOpX<BULT>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvult Start Start)";
        return "(bvult " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BULE>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvule Start Start)";
        return "(bvule " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BUGT>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvugt Start Start)";
        return "(bvugt " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BUGE>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvuge Start Start)";
        return "(bvuge " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BSLT>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvslt Start Start)";
        return "(bvslt " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BSLE>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvsle Start Start)";
        return "(bvsle " + lhs + " " + rhs + ")";
      }
      
      // LIA comparisons (if not translated back to BV)
      if (isOpX<LT>(e) || isOpX<LEQ>(e))
      {
        return "(bvslt Start Start)";
      }
      
      if (isOpX<GT>(e) || isOpX<GEQ>(e))
      {
        return "(bvsgt Start Start)";
      }
      
      if (isOpX<EQ>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(= Start Start)";
        return "(= " + lhs + " " + rhs + ")";
      }
      
      // BV arithmetic
      if (isOpX<BADD>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvadd Start Start)";
        return "(bvadd " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BSUB>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvsub Start Start)";
        return "(bvsub " + lhs + " " + rhs + ")";
      }
      
      if (isOpX<BMUL>(e))
      {
        std::string lhs = exprToSyGuS(e->left(), varWidth, stepWidth);
        std::string rhs = exprToSyGuS(e->right(), varWidth, stepWidth);
        if (lhs.empty() || rhs.empty()) return "(bvmul Start Start)";
        return "(bvmul " + lhs + " " + rhs + ")";
      }
      
      // BV constants
      if (bv::is_bvnum(e))
      {
        mpz_class val = bv::toMpz(e);
        mpz_class masked = val & ((mpz_class(1) << varWidth) - 1);
        std::stringstream ss;
        ss << std::hex << std::setfill('0') << std::setw(varWidth / 4) << masked;
        return "#x" + ss.str();
      }
      
      // Integer constants (from LIA)
      if (isOpX<MPZ>(e))
      {
        mpz_class val = lexical_cast<mpz_class>(e);
        mpz_class masked = val & ((mpz_class(1) << varWidth) - 1);
        std::stringstream ss;
        ss << std::hex << std::setfill('0') << std::setw(varWidth / 4) << masked;
        return "#x" + ss.str();
      }
      
      // Variables - use Start as placeholder
      if (bind::IsConst()(e) || isOpX<FAPP>(e))
      {
        return "Start";
      }
      
      // Default: return empty (skip this guard)
      return "";
    }

  public:
    vector<ExprVector> bindVars;

    BndExpl(CHCs &r, bool d) : m_efac(r.m_efac), ruleManager(r), u(m_efac), debug(d) {}

    BndExpl(CHCs &r, int to, bool d) : m_efac(r.m_efac), ruleManager(r), u(m_efac, to), debug(d) {}

    BndExpl(CHCs &r, Expr lms, bool d) : m_efac(r.m_efac), ruleManager(r), u(m_efac), extraLemmas(lms), debug(d) {}

    map<Expr, ExprSet> concrInvs;
    set<vector<int>> unsat_prefs;

    vector<ExprVector> getBindVars() { return bindVars; }

    // Helper struct to hold parsed CEX data
    struct CEXData {
      map<Expr, pair<Expr, Expr>> traceValueFuncs; // array -> (indexVar, valueExpr)
      int64_t traceStart = 0;
      int64_t traceEnd = 0;
      Expr traceStartExpr = nullptr;  // For bitvector bounds that exceed int64
      Expr traceEndExpr = nullptr;    // For bitvector bounds that exceed int64
      Expr indexType = nullptr;       // Type of the index (int or bitvector sort)
      bool boundsFound = false;
    };

    // Extract bounds from a quantifier condition expression
    // Handles: (AND (LEQ 0 idx) (LEQ idx N)), (GEQ idx 0), (LT/GT variants)
    void extractBoundsFromCondition(Expr condition, int64_t &traceStart, int64_t &traceEnd, bool &boundsFound)
    {
      if (isOpX<AND>(condition))
      {
        for (auto it = condition->args_begin(); it != condition->args_end(); ++it)
          extractBoundsFromCondition(*it, traceStart, traceEnd, boundsFound);
      }
      else if (isOpX<LEQ>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          cpp_int val = lexical_cast<cpp_int>(left);
          traceStart = val.convert_to<int64_t>();
          boundsFound = true;
        }
        else if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          cpp_int val = lexical_cast<cpp_int>(right);
          traceEnd = val.convert_to<int64_t>();
          boundsFound = true;
        }
      }
      else if (isOpX<GEQ>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          cpp_int val = lexical_cast<cpp_int>(right);
          traceStart = val.convert_to<int64_t>();
          boundsFound = true;
        }
        else if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          cpp_int val = lexical_cast<cpp_int>(left);
          traceEnd = val.convert_to<int64_t>();
          boundsFound = true;
        }
      }
      else if (isOpX<LT>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          cpp_int val = lexical_cast<cpp_int>(left);
          traceStart = val.convert_to<int64_t>() + 1;
          boundsFound = true;
        }
        else if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          cpp_int val = lexical_cast<cpp_int>(right);
          traceEnd = val.convert_to<int64_t>() - 1;
          boundsFound = true;
        }
      }
      else if (isOpX<GT>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          cpp_int val = lexical_cast<cpp_int>(right);
          traceStart = val.convert_to<int64_t>() + 1;
          boundsFound = true;
        }
        else if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          cpp_int val = lexical_cast<cpp_int>(left);
          traceEnd = val.convert_to<int64_t>() - 1;
          boundsFound = true;
        }
      }
      // Bitvector unsigned comparisons (for zero-extend benchmarks)
      else if (isOpX<BULE>(condition))  // bvule: left <= right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          mpz_class val = bv::toMpz(left);
          traceStart = val.get_si();
          boundsFound = true;
        }
        else if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          mpz_class val = bv::toMpz(right);
          traceEnd = val.get_si();
          boundsFound = true;
        }
      }
      else if (isOpX<BUGE>(condition))  // bvuge: left >= right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          mpz_class val = bv::toMpz(right);
          traceStart = val.get_si();
          boundsFound = true;
        }
        else if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          mpz_class val = bv::toMpz(left);
          traceEnd = val.get_si();
          boundsFound = true;
        }
      }
      else if (isOpX<BULT>(condition))  // bvult: left < right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          mpz_class val = bv::toMpz(left);
          traceStart = val.get_si() + 1;
          boundsFound = true;
        }
        else if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          mpz_class val = bv::toMpz(right);
          traceEnd = val.get_si() - 1;
          boundsFound = true;
        }
      }
      else if (isOpX<BUGT>(condition))  // bvugt: left > right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          mpz_class val = bv::toMpz(right);
          traceStart = val.get_si() + 1;
          boundsFound = true;
        }
        else if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          mpz_class val = bv::toMpz(left);
          traceEnd = val.get_si() - 1;
          boundsFound = true;
        }
      }
    }

    // Extract bound expressions (start and end) from a condition
    // This handles bitvector bounds that may exceed int64 capacity
    void extractBoundExprs(Expr condition, Expr &startExpr, Expr &endExpr, Expr &indexType)
    {
      if (isOpX<AND>(condition))
      {
        for (auto it = condition->args_begin(); it != condition->args_end(); ++it)
          extractBoundExprs(*it, startExpr, endExpr, indexType);
      }
      else if (isOpX<BULE>(condition))  // bvule: left <= right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          startExpr = left;
          if (!indexType) indexType = bind::typeOf(right);
        }
        else if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          endExpr = right;
          if (!indexType) indexType = bind::typeOf(left);
        }
      }
      else if (isOpX<BUGE>(condition))  // bvuge: left >= right (unsigned)
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (bv::is_bvnum(right) && !bv::is_bvnum(left))
        {
          startExpr = right;
          if (!indexType) indexType = bind::typeOf(left);
        }
        else if (bv::is_bvnum(left) && !bv::is_bvnum(right))
        {
          endExpr = left;
          if (!indexType) indexType = bind::typeOf(right);
        }
      }
      else if (isOpX<LEQ>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          startExpr = left;
          if (!indexType) indexType = bind::typeOf(right);
        }
        else if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          endExpr = right;
          if (!indexType) indexType = bind::typeOf(left);
        }
      }
      else if (isOpX<GEQ>(condition))
      {
        Expr left = condition->left();
        Expr right = condition->right();
        if (isOpX<MPZ>(right) && !isOpX<MPZ>(left))
        {
          startExpr = right;
          if (!indexType) indexType = bind::typeOf(left);
        }
        else if (isOpX<MPZ>(left) && !isOpX<MPZ>(right))
        {
          endExpr = left;
          if (!indexType) indexType = bind::typeOf(right);
        }
      }
    }

    // Parse CEX assertions to extract trace value functions and bounds
    // CEX format: forall i => (cond -> (select trace_arr i) = value_func(i))
    // or: forall i => (cond -> AND((select arr1 i) = f1(i), (select arr2 i) = f2(i), ...))
    CEXData parseCEXAssertions(const ExprVector &ccex)
    {
      CEXData data;
      
      for (auto &assertion : ccex)
      {
        if (debug)
          outs() << "  Processing CEX assertion: " << *assertion << "\n";
        
        if (!isOpX<FORALL>(assertion)) continue;
        
        // Get the bound variable - for FORALL, the first arg is the variable declaration
        // and the bound variable in the body is bvar(0, type)
        Expr varDecl = assertion->first();
        Expr varType = bind::rangeTy(varDecl);
        Expr indexVar = bind::bvar(0, varType);  // Create the bound variable reference
        
        Expr body = assertion->last();
        
        if (!isOpX<IMPL>(body)) continue;
        
        // Extract bounds from condition (only once)
        if (!data.boundsFound)
        {
          Expr condition = body->left();
          extractBoundsFromCondition(condition, data.traceStart, data.traceEnd, data.boundsFound);
          // Also extract bound expressions for large bitvector values
          extractBoundExprs(condition, data.traceStartExpr, data.traceEndExpr, data.indexType);
        }
        
        // Extract value function from conclusion
        Expr conclusion = body->right();
        
        // Helper lambda to extract value function from an equality
        auto extractFromEq = [&](Expr eq) {
          if (!isOpX<EQ>(eq)) return;
          Expr lhs = eq->left();
          Expr rhs = eq->right();
          
          if (isOpX<SELECT>(lhs))
          {
            data.traceValueFuncs[lhs->left()] = make_pair(indexVar, rhs);
          }
          else if (isOpX<SELECT>(rhs))
          {
            data.traceValueFuncs[rhs->left()] = make_pair(indexVar, lhs);
          }
        };
        
        if (isOpX<EQ>(conclusion))
        {
          extractFromEq(conclusion);
        }
        else if (isOpX<AND>(conclusion))
        {
          // Handle conjunction of equalities
          for (auto it = conclusion->args_begin(); it != conclusion->args_end(); ++it)
          {
            extractFromEq(*it);
          }
        }
      }
      
      return data;
    }

    // Build substitution map from CEX value functions for all steps
    ExprMap buildSubstitutionMap(const CEXData &cexData, const ExprVector &traceArrays)
    {
      ExprMap varToValue;
      
      for (size_t step = 0; step < bindVars.size(); step++)
      {
        int varIdx = 0;
        for (auto &arr : traceArrays)
        {
          if (varIdx < (int)bindVars[step].size())
          {
            auto it = cexData.traceValueFuncs.find(arr);
            if (it != cexData.traceValueFuncs.end())
            {
              Expr indexVar = it->second.first;  // Get the actual index variable from CCEX
              Expr valueFunc = it->second.second;
              
              if (debug)
              {
                outs() << "  [Subst] Step " << step << ", var " << varIdx 
                       << ": indexVar type = " << *bind::typeOf(indexVar)
                       << ", valueFunc = " << *valueFunc << "\n";
              }
              
              // Create step index with matching type
              Expr stepIdx;
              Expr indexType = bind::typeOf(indexVar);
              if (bv::is_bvsort(indexType))
              {
                unsigned width = bv::width(indexType);
                stepIdx = bv::bvnum(mpz_class(step), width, m_efac);
              }
              else
              {
                stepIdx = mkTerm<mpz_class>(step, m_efac);
              }
              
              Expr concreteValue = replaceAll(valueFunc, indexVar, stepIdx);
              
              if (debug)
              {
                outs() << "  [Subst] Replacing " << *indexVar << " with " << *stepIdx 
                       << " -> " << *concreteValue << "\n";
              }

              varToValue[bindVars[step][varIdx]] = concreteValue;
            }
          }
          varIdx++;
        }
      }
      
      return varToValue;
    }

    // Substitute values into SSA formulas and validate the result
    tribool substituteAndValidate(const ExprVector &ssa, ExprMap &varToValue)
    {
      ExprVector substitutedSSA;
      for (auto &formula : ssa)
      {
        // Use the batch replaceAll that takes an ExprMap
        Expr substituted = replaceAll(formula, varToValue);
        substitutedSSA.push_back(substituted);
      }

      if (debug)
      {
        outs() << "  Substituted SSA:\n";
        pprint(substitutedSSA, 4);
      }
      
      SMTUtils u2(m_efac);
      // ruleManager.serializeExpr(conjoin(substitutedSSA, m_efac));
      Expr simpl = u.simplify(conjoin(substitutedSSA, m_efac));
      
      if (debug)
      {
        outs() << "  Simplified: " << simpl << "\n";
      }
      
      return isOpX<TRUE>(simpl);
    }

    // Helper to truncate large numeric constants in output
    string truncateLargeConsts(string s)
    {
      string res = "";
      int digitCount = 0;
      int startDigit = -1;
      
      for (size_t i = 0; i < s.length(); i++)
      {
        if (isdigit(s[i]))
        {
          if (digitCount == 0) startDigit = i;
          digitCount++;
        }
        else
        {
          if (digitCount > 50)
          {
            res += s.substr(startDigit, 10) + "..." + s.substr(i-10, 10);
          }
          else if (digitCount > 0)
          {
            res += s.substr(startDigit, digitCount);
          }
          
          res += s[i];
          digitCount = 0;
        }
      }
      if (digitCount > 50)
      {
        res += s.substr(startDigit, 10) + "..." + s.substr(s.length()-10, 10);
      }
      else if (digitCount > 0)
      {
        res += s.substr(startDigit, digitCount);
      }
      return res;
    }

    // Compute cone of influence: variables that affect the property violation
    // Returns set of variable indices (0-based) that are in the cone
    set<int> computeConeOfInfluence(HornRuleExt* queryCHC, HornRuleExt* transCHC)
    {
      set<int> relevantVarIndices;
      
      if (!queryCHC || !transCHC) return relevantVarIndices;
      
      // Step 1: Find variables used in the property (query) body
      // Filter out trivial equalities like x=x
      ExprSet queryConjuncts;
      getConj(queryCHC->body, queryConjuncts);
      
      ExprSet queryVars;
      for (auto& conj : queryConjuncts)
      {
        // Skip trivial equalities (x = x)
        if (isOpX<EQ>(conj) && conj->left() == conj->right())
          continue;
        
        filter(conj, bind::IsConst(), inserter(queryVars, queryVars.begin()));
      }
      
      // Map query vars to indices in srcVars
      for (size_t i = 0; i < queryCHC->srcVars.size(); i++)
      {
        if (queryVars.count(queryCHC->srcVars[i]) > 0)
          relevantVarIndices.insert(i);
      }
      
      if (debug)
      {
        outs() << "  [Slicing] Initial relevant vars from query: {";
        for (int idx : relevantVarIndices) outs() << idx << " ";
        outs() << "}\n";
      }
      
      // Step 2: Backward reachability through transition relation
      // Build dependency map: dstVar[i] -> set of srcVar indices it depends on
      map<int, set<int>> depMap;
      
      // Parse transition body to find dependencies
      ExprSet transConjuncts;
      getConj(transCHC->body, transConjuncts);
      
      for (size_t dstIdx = 0; dstIdx < transCHC->dstVars.size(); dstIdx++)
      {
        Expr dstVar = transCHC->dstVars[dstIdx];
        
        // Find constraints involving this dstVar
        for (auto& conj : transConjuncts)
        {
          // Skip trivial equalities (x = x)
          if (isOpX<EQ>(conj) && conj->left() == conj->right())
            continue;
            
          if (!contains(conj, dstVar)) continue;
          
          // Get all variables in this conjunct
          ExprSet conjVars;
          filter(conj, bind::IsConst(), inserter(conjVars, conjVars.begin()));
          
          // Find which srcVars are involved
          for (size_t srcIdx = 0; srcIdx < transCHC->srcVars.size(); srcIdx++)
          {
            if (conjVars.count(transCHC->srcVars[srcIdx]) > 0)
              depMap[dstIdx].insert(srcIdx);
          }
        }
      }
      
      if (debug)
      {
        outs() << "  [Slicing] Dependency map:\n";
        for (auto& kv : depMap)
        {
          outs() << "    dst[" << kv.first << "] depends on src{";
          for (int idx : kv.second) outs() << idx << " ";
          outs() << "}\n";
        }
      }
      
      // Step 3: Fixed-point computation
      // For inductive transitions, dstVars correspond to srcVars (same indices)
      bool changed = true;
      while (changed)
      {
        changed = false;
        set<int> toAdd;
        
        for (int idx : relevantVarIndices)
        {
          // idx is a relevant dst variable, add its dependencies
          if (depMap.count(idx) > 0)
          {
            for (int depIdx : depMap[idx])
            {
              if (relevantVarIndices.count(depIdx) == 0)
              {
                toAdd.insert(depIdx);
                changed = true;
              }
            }
          }
        }
        
        relevantVarIndices.insert(toAdd.begin(), toAdd.end());
      }
      
      if (debug)
      {
        outs() << "  [Slicing] Final cone of influence: {";
        for (int idx : relevantVarIndices) outs() << idx << " ";
        outs() << "}\n";
      }
      
      return relevantVarIndices;
    }
    
    // Check if trace arrays cover the cone of influence
    // Returns true if all variables in the cone are covered by the trace
    bool traceCoversCone(const ExprVector& traceArrays, const set<int>& cone, 
                         HornRuleExt* transCHC)
    {
      if (!transCHC) return false;
      
      // The trace arrays correspond to variables by index
      // Check if all cone indices are covered
      for (int idx : cone)
      {
        if (idx >= (int)traceArrays.size())
        {
          if (debug)
            outs() << "  [Slicing] Cone index " << idx << " not covered by trace\n";
          return false;
        }
      }
      
      return true;
    }
    
    // Validate partial CEX by checking only the cone of influence
    // This is called when standard validation fails but trace covers the cone
    tribool validatePartialCEXInductive(ExprVector ccex, const set<int>& cone,
                                        HornRuleExt* initCHC, HornRuleExt* transCHC, 
                                        HornRuleExt* queryCHC, CEXData& cexData,
                                        const ExprVector& traceArrays)
    {
      using namespace std::chrono;
      
      outs() << "\n=== Partial CEX Validation (Cone of Influence) ===\n";
      outs() << "  [Partial] Validating with cone: {";
      for (int idx : cone) outs() << idx << " ";
      outs() << "}\n";
      
      SMTUtils solver(m_efac);
      tribool result = true;
      
      // Helper to check if index is bitvector type
      auto isIndexBvType = [&](Expr indexVar, unsigned &bvWidth) -> bool {
        if (!indexVar) return false;
        if (bind::isBVar(indexVar))
        {
          Expr varType = bind::typeOf(indexVar);
          if (bv::is_bvsort(varType))
          {
            bvWidth = bv::width(varType);
            return true;
          }
          return false;
        }
        if (bind::isFapp(indexVar))
        {
          Expr idxType = bind::rangeTy(bind::fname(indexVar));
          if (bv::is_bvsort(idxType))
          {
            bvWidth = bv::width(idxType);
            return true;
          }
        }
        return false;
      };
      
      // Determine index type
      bool isBvIndex = false;
      unsigned bvWidth = 0;
      if (!traceArrays.empty())
      {
        auto it = cexData.traceValueFuncs.find(traceArrays[0]);
        if (it != cexData.traceValueFuncs.end())
          isBvIndex = isIndexBvType(it->second.first, bvWidth);
      }
      
      // Create symbolic index
      Expr iVar, iPlusOne, boundsExpr;
      if (isBvIndex)
      {
        iVar = bv::bvConst(mkTerm<string>("_cex_i", m_efac), bvWidth);
        iPlusOne = bv::bvadd(iVar, bv::bvnum(mpz_class(1), bvWidth, m_efac));
        Expr startBound = cexData.traceStartExpr ? cexData.traceStartExpr 
                          : bv::bvnum(mpz_class(cexData.traceStart), bvWidth, m_efac);
        Expr endBound = cexData.traceEndExpr 
                        ? bv::bvsub(cexData.traceEndExpr, bv::bvnum(mpz_class(1), bvWidth, m_efac))
                        : bv::bvnum(mpz_class(cexData.traceEnd > 0 ? cexData.traceEnd - 1 : 0), bvWidth, m_efac);
        boundsExpr = mk<AND>(bv::bvuge(iVar, startBound), bv::bvule(iVar, endBound));
      }
      else
      {
        iVar = bind::intConst(mkTerm<string>("_cex_i", m_efac));
        iPlusOne = mk<PLUS>(iVar, mkTerm<mpz_class>(1, m_efac));
        boundsExpr = mk<AND>(
          mk<GEQ>(iVar, mkTerm<mpz_class>(cexData.traceStart, m_efac)),
          mk<LEQ>(iVar, mkTerm<mpz_class>(cexData.traceEnd - 1, m_efac))
        );
      }
      
      // Build substitution maps for ONLY the cone variables
      ExprMap srcSubst, dstSubst;
      for (int idx : cone)
      {
        if (idx >= (int)traceArrays.size()) continue;
        
        Expr arr = traceArrays[idx];
        auto it = cexData.traceValueFuncs.find(arr);
        if (it == cexData.traceValueFuncs.end()) continue;
        
        Expr indexVar = it->second.first;
        Expr valueFunc = it->second.second;
        
        if (idx < (int)transCHC->srcVars.size())
        {
          Expr srcValue = replaceAll(valueFunc, indexVar, iVar);
          srcSubst[transCHC->srcVars[idx]] = srcValue;
        }
        if (idx < (int)transCHC->dstVars.size())
        {
          Expr dstValue = replaceAll(valueFunc, indexVar, iPlusOne);
          dstSubst[transCHC->dstVars[idx]] = dstValue;
        }
      }
      
      // === Transition Check (only for cone variables) ===
      // Extract transition constraints that only involve cone variables
      ExprSet transConjuncts;
      getConj(transCHC->body, transConjuncts);
      
      ExprVector coneConstraints;
      for (auto& conj : transConjuncts)
      {
        // Check if this conjunct only involves cone variables
        ExprSet conjVars;
        filter(conj, bind::IsConst(), inserter(conjVars, conjVars.begin()));
        
        bool inCone = true;
        for (auto& v : conjVars)
        {
          // Check if v is a src/dst var outside the cone
          bool isSrcVar = false, isDstVar = false;
          int srcIdx = -1, dstIdx = -1;
          
          for (size_t i = 0; i < transCHC->srcVars.size(); i++)
          {
            if (transCHC->srcVars[i] == v) { isSrcVar = true; srcIdx = i; break; }
          }
          for (size_t i = 0; i < transCHC->dstVars.size(); i++)
          {
            if (transCHC->dstVars[i] == v) { isDstVar = true; dstIdx = i; break; }
          }
          
          if (isSrcVar && cone.count(srcIdx) == 0) { inCone = false; break; }
          if (isDstVar && cone.count(dstIdx) == 0) { inCone = false; break; }
        }
        
        if (inCone)
          coneConstraints.push_back(conj);
      }
      
      if (debug)
      {
        outs() << "  [Partial] Cone constraints:\n";
        for (auto& c : coneConstraints)
          outs() << "    " << *c << "\n";
      }
      
      // Check transition validity for cone constraints only
      Expr coneBody = conjoin(coneConstraints, m_efac);
      Expr transWithSrc = replaceAll(coneBody, srcSubst);
      Expr transWithBoth = replaceAll(transWithSrc, dstSubst);
      Expr transSimpl = u.simplify(transWithBoth);
      
      if (debug)
        outs() << "  [Partial] Trans after substitution: " << *transSimpl << "\n";
      
      if (isOpX<TRUE>(transSimpl))
      {
        outs() << "  [Partial] Transition: PASS (simplified to TRUE)\n";
      }
      else
      {
        Expr validityCheck = mk<AND>(boundsExpr, mk<NEG>(transSimpl));
        validityCheck = u.simplify(validityCheck);
        
        tribool transResult = solver.isSat(validityCheck);
        
        if (transResult == false)
        {
          outs() << "  [Partial] Transition: PASS (cone constraints valid)\n";
        }
        else
        {
          outs() << "  [Partial] Transition: FAIL (cone constraints not valid)\n";
          result = false;
        }
      }
      
      if (result == true)
      {
        outs() << "  [Partial] CEX VALID: Partial trace covers cone of influence\n";
      }
      else
      {
        outs() << "  [Partial] CEX INVALID: Partial trace does not satisfy cone constraints\n";
      }
      
      return result;
    }

    // Identify which variables caused validation failure
    void reportValidCEXVariables(Expr body, ExprMap &subst, const ExprVector &vars, string stepName)
    {
      outs() << "  [Error State Variable Report]\n";
      
      // Decompose body into conjuncts
      ExprVector conjuncts;
      if (isOpX<AND>(body))
      {
        for (auto it = body->args_begin(); it != body->args_end(); ++it)
           conjuncts.push_back(*it);
      }
      else
      {
        conjuncts.push_back(body);
      }
      
      for (auto &conj : conjuncts)
      {
        // Skip trivial equalities (e.g. x = x)
        if (isOpX<EQ>(conj) && conj->left() == conj->right())
          continue;

        // Handle disjunctions: only report variables in satisfied disjuncts
        if (isOpX<OR>(conj))
        {
           bool handled = false;
           for (auto it = conj->args_begin(); it != conj->args_end(); ++it)
           {
              Expr disjunct = *it;
              Expr val = replaceAll(disjunct, subst);
              Expr simplified = u.simplify(val);
              
              if (isOpX<TRUE>(simplified))
              {
                 stringstream ss;
                 ss << *disjunct;
                 outs() << "    Constraint (satisfied disjunct): " << truncateLargeConsts(ss.str()) << "\n";
                 
                 bool foundVar = false;
                 for (auto &v : vars)
                 {
                    if (contains(disjunct, v))
                    {
                       Expr vVal = subst[v];
                       if (!vVal) vVal = mk<TRUE>(m_efac);
                       stringstream ssVal;
                       ssVal << *vVal;
                       outs() << "      -> Variable: " << *v << " = " << truncateLargeConsts(ssVal.str()) << "\n";
                       foundVar = true;
                    }
                 }
                 if (!foundVar)
                 {
                    outs() << "      -> No tracked variable found in disjunct\n";
                 }
                 handled = true;
              }
           }
           if (handled) continue;
        }

        // For a valid CEX, the conjunct is TRUE.
        // We want to show the constraint and the variables involved.
        stringstream ss;
        ss << *conj;
        outs() << "    Constraint: " << truncateLargeConsts(ss.str()) << "\n";
        
        bool found = false;
        for (auto &v : vars)
        {
          if (contains(conj, v))
          {
            // Evaluate the variable to show its value
            Expr val = subst[v];
            if (!val) val = mk<TRUE>(m_efac); // Should not happen if subst is complete
            
            stringstream ssVal;
            ssVal << *val;
            outs() << "      -> Variable: " << *v << " = " << truncateLargeConsts(ssVal.str()) << "\n";
            found = true;
          }
        }
        if (!found)
        {
           outs() << "      -> No tracked variable found in constraint\n";
        }
      }
      outs() << "  [End Report]\n";
    }

    void identifyFailingVariables(const ExprVector &ssa, ExprMap &varToValue)
    {
      outs() << "\n  [Detailed Validation Report]\n";
      SMTUtils u(m_efac);
      
      for (size_t i = 0; i < ssa.size(); ++i)
      {
        Expr formula = ssa[i];
        Expr subst = replaceAll(formula, varToValue);
        Expr simpl = u.simplify(subst);
        
        if (isOpX<FALSE>(simpl))
        {
          outs() << "  Step " << i << " failed validation.\n";
          
          // Decompose formula into conjuncts
          ExprVector conjuncts;
          if (isOpX<AND>(formula))
          {
            for (auto it = formula->args_begin(); it != formula->args_end(); ++it)
               conjuncts.push_back(*it);
          }
          else
          {
            conjuncts.push_back(formula);
          }
          
          for (auto &conj : conjuncts)
          {
            Expr s = replaceAll(conj, varToValue);
            if (isOpX<FALSE>(u.simplify(s)))
            {
              outs() << "    Failing constraint: " << *conj << "\n";
              
              // Identify involved variables from bindVars[i]
              if (i < bindVars.size())
              {
                bool found = false;
                for (auto &v : bindVars[i])
                {
                  if (contains(conj, v))
                  {
                    outs() << "    -> Potentially incorrect variable: " << *v << "\n";
                    found = true;
                  }
                }
                if (!found)
                {
                   outs() << "    -> No destination variable found in constraint (guard violation?)\n";
                }
              }
            }
          }
        }
      }
      outs() << "  [End Report]\n\n";
    }

    void reportInductiveFailure(Expr body, ExprMap &subst, const ExprVector &vars, string stepName)
    {
      outs() << "  [Detailed " << stepName << " Report]\n";
      SMTUtils u(m_efac);
      
      // Decompose body into conjuncts
      ExprVector conjuncts;
      if (isOpX<AND>(body))
      {
        for (auto it = body->args_begin(); it != body->args_end(); ++it)
           conjuncts.push_back(*it);
      }
      else
      {
        conjuncts.push_back(body);
      }
      
      for (auto &conj : conjuncts)
      {
        // Skip trivial equalities (e.g. x = x)
        if (isOpX<EQ>(conj) && conj->left() == conj->right())
          continue;

        Expr s = replaceAll(conj, subst);
        // Simplify to check if this conjunct fails
        if (isOpX<FALSE>(u.simplify(s)))
        {
          outs() << "    Failing constraint: " << *conj << "\n";
          
          bool found = false;
          for (auto &v : vars)
          {
            if (contains(conj, v))
            {
              outs() << "    -> Potentially incorrect variable: " << *v << "\n";
              found = true;
            }
          }
          if (!found)
          {
             outs() << "    -> No tracked variable found in constraint\n";
          }
        }
      }
      outs() << "  [End Report]\n";
    }

    tribool validateCEX(ExprVector ccex, Expr src, Expr dst)
    {
      using namespace std::chrono;
      auto totalStart = high_resolution_clock::now();
      
      // Parse CEX assertions to extract value functions and bounds
      auto parseStart = high_resolution_clock::now();
      CEXData cexData = parseCEXAssertions(ccex);
      auto parseEnd = high_resolution_clock::now();
      auto parseTime = duration_cast<microseconds>(parseEnd - parseStart).count();
      
      if (debug)
      {
        outs() << "  Extracted bounds: start=" << cexData.traceStart 
               << ", end=" << cexData.traceEnd << "\n";
        outs() << "  Found " << cexData.traceValueFuncs.size() << " trace value functions:\n";
        for (auto &kv : cexData.traceValueFuncs)
          outs() << "    " << *kv.first << " -> " << *kv.second.second << "\n";
      }
      
      // Calculate trace length from bounds
      // Trace structure: 1 init + N transitions + 1 query = N + 2 CHCs
      // To reach state traceEnd from state traceStart, we need (traceEnd - traceStart) transitions
      // Total CHCs = 1 (init) + (traceEnd - traceStart) (transitions) + 1 (query) = traceEnd - traceStart + 2
      int64_t len64 = cexData.traceEnd - cexData.traceStart + 2;
      if (len64 <= 1)
      {
        outs() << "  ERROR: Invalid trace bounds (start=" << cexData.traceStart 
               << ", end=" << cexData.traceEnd << ")\n";
        return indeterminate;
      }
      
      // Check if trace is too long for unrolling-based validation
      // Memory limit: vector<int> with N elements needs ~4N bytes
      // 500M steps = ~2GB memory, which is a reasonable limit
      const int64_t MAX_UNROLL_LENGTH = 5000000000LL; // 5 billion steps max
      if (len64 > MAX_UNROLL_LENGTH)
      {
        outs() << "  ERROR: Trace too long for unrolling (" << len64 << " steps, max " 
               << MAX_UNROLL_LENGTH << ")\n";
        outs() << "  Consider using inductive validation for large traces.\n";
        return indeterminate;
      }
      int64_t len = len64;

      // Get a single trace efficiently (for CEX validation we typically only need one)
      auto traceStart = high_resolution_clock::now();
      vector<int> trace;
      if (!getSingleTrace(src, dst, len, trace)) // TODO: Use the same method for trace extraction as in DL.
      {
        outs() << "  ERROR: Could not find a trace of length " << len << "\n";
        return indeterminate;
      }
      auto traceEnd = high_resolution_clock::now();
      auto traceTime = duration_cast<milliseconds>(traceEnd - traceStart).count();
      
      if (debug)
        outs() << "  Found trace of length " << trace.size() << "\n";

      // Get trace arrays in order (to match bindVars indices)
      ExprVector traceArrays;
      for (auto &kv : cexData.traceValueFuncs)
        traceArrays.push_back(kv.first);

      // Validate the trace
      auto ssaStart = high_resolution_clock::now();
      ExprVector ssa;
      getSSA(trace, ssa);
      auto ssaEnd = high_resolution_clock::now();
      auto ssaTime = duration_cast<milliseconds>(ssaEnd - ssaStart).count();
      
      if (debug)
      {
        outs() << "  Original SSA (" << ssa.size() << " formulas)\n";
        outs() << "  Bind vars: " << bindVars.size() << " steps, "
               << (bindVars.size() > 0 ? bindVars[0].size() : 0) << " vars/step\n";
        outs() << "\n  Validating CEX against trace...\n";
      }

      auto substStart = high_resolution_clock::now();
      ExprMap varToValue = buildSubstitutionMap(cexData, traceArrays);
      auto substEnd = high_resolution_clock::now();
      auto substTime = duration_cast<milliseconds>(substEnd - substStart).count();
      
      auto validateStart = high_resolution_clock::now();
      tribool traceResult = substituteAndValidate(ssa, varToValue); // TODO: optimize by cutting out early.
      auto validateEnd = high_resolution_clock::now();
      auto validateTime = duration_cast<milliseconds>(validateEnd - validateStart).count();
      
      auto totalEnd = high_resolution_clock::now();
      auto totalTime = duration_cast<milliseconds>(totalEnd - totalStart).count();
      
      // Print timing stats
      outs() << "  [Timing] Parse CEX: " << parseTime << "ms, "
             << "Trace: " << traceTime << "ms, "
             << "SSA: " << ssaTime << "ms, "
             << "Subst: " << substTime << "ms, "
             << "Validate: " << validateTime << "ms, "
             << "Total: " << totalTime << "ms\n";
      
      if (traceResult == true)
      {
        outs() << "  CEX VALID: Substituted trace is TRUE\n";
        
        // Report for the last step (Query)
        if (!ssa.empty() && !bindVars.empty())
        {
           // The last SSA formula corresponds to the query
           Expr queryBody = ssa.back();
           // The variables in the last step
           ExprVector &queryVars = bindVars.back();
           
           reportValidCEXVariables(queryBody, varToValue, queryVars, "Unrolled Property");
        }
      }
      else if (traceResult == false)
      {
        outs() << "  CEX INVALID: Substituted trace is FALSE\n";
        identifyFailingVariables(ssa, varToValue);
      }
      else
      {
        outs() << "  CEX UNKNOWN: Substituted trace is INDETERMINATE\n";
      }

      return traceResult;
    }

    // Alternative inductive CEX validation using 3 solver checks:
    // 1. Init check: f(0) satisfies the initial constraint
    // 2. Transition check: f(i) /\ transition => f(i+1) is valid (negation is UNSAT)
    // 3. Property check: f(N) violates the property (reaches error)
    tribool validateCEXInductive(ExprVector ccex)
    {
      using namespace std::chrono;
      auto totalStart = high_resolution_clock::now();
      
      // Parse CEX assertions to extract value functions and bounds
      auto parseStart = high_resolution_clock::now();
      CEXData cexData = parseCEXAssertions(ccex);
      auto parseEnd = high_resolution_clock::now();
      auto parseTime = duration_cast<microseconds>(parseEnd - parseStart).count();
      
      if (debug)
      {
        outs() << "  [Inductive] Extracted bounds: start=" << cexData.traceStart 
               << ", end=" << cexData.traceEnd << "\n";
        outs() << "  [Inductive] Found " << cexData.traceValueFuncs.size() << " trace value functions:\n";
        for (auto &kv : cexData.traceValueFuncs)
          outs() << "    " << *kv.first << " -> " << *kv.second.second << "\n";
      }

      // Get trace arrays in order
      ExprVector traceArrays;
      for (auto &kv : cexData.traceValueFuncs)
        traceArrays.push_back(kv.first);

      if(debug)
      {
        outs() << "  [Inductive] Trace arrays:\n";
        for (auto &arr : traceArrays)
          outs() << "    " << *arr << "\n";
      }

      // Find the Init, Transition, and Property (Query) CHCs
      HornRuleExt* initCHC = nullptr;
      HornRuleExt* transCHC = nullptr;
      HornRuleExt* queryCHC = nullptr;
      
      for (auto &chc : ruleManager.chcs)
      {
        if (chc.isFact && !chc.isQuery)
          initCHC = &chc;
        else if (chc.isInductive)
          transCHC = &chc;
        else if (chc.isQuery && !chc.isFact)
          queryCHC = &chc;
      }

      if (!initCHC || !transCHC || !queryCHC)
      {
        outs() << "  [Inductive] ERROR: Could not identify Init/Trans/Query CHCs\n";
        return indeterminate;
      }

      if (debug)
      {
        outs() << "  [Inductive] Init CHC body: " << *initCHC->body << "\n";
        outs() << "  [Inductive] Trans CHC body: " << *transCHC->body << "\n";
        outs() << "  [Inductive] Query CHC body: " << *queryCHC->body << "\n";
      }

      // Helper to create a step index as the appropriate type (int or bitvector)
      // based on the index variable type from the CCEX
      auto makeStepIndex = [&](int64_t step, Expr indexVar) -> Expr {
        if (!indexVar) return mkTerm<mpz_class>(step, m_efac);
        
        // For bound variables (bvar), check the type directly
        if (bind::isBVar(indexVar))
        {
          Expr varType = bind::typeOf(indexVar);
          if (bv::is_bvsort(varType))
          {
            unsigned width = bv::width(varType);
            return bv::bvnum(mpz_class(step), width, m_efac);
          }
          return mkTerm<mpz_class>(step, m_efac);
        }
        
        // For function applications (constants), check rangeTy
        if (bind::isFapp(indexVar))
        {
          Expr idxType = bind::rangeTy(bind::fname(indexVar));
          if (bv::is_bvsort(idxType))
          {
            unsigned width = bv::width(idxType);
            return bv::bvnum(mpz_class(step), width, m_efac);
          }
        }
        
        return mkTerm<mpz_class>(step, m_efac);
      };
      
      // Helper to check if index is bitvector type
      auto isIndexBvType = [&](Expr indexVar, unsigned &bvWidth) -> bool {
        if (!indexVar) return false;
        
        if (bind::isBVar(indexVar))
        {
          Expr varType = bind::typeOf(indexVar);
          if (bv::is_bvsort(varType))
          {
            bvWidth = bv::width(varType);
            return true;
          }
          return false;
        }
        
        if (bind::isFapp(indexVar))
        {
          Expr idxType = bind::rangeTy(bind::fname(indexVar));
          if (bv::is_bvsort(idxType))
          {
            bvWidth = bv::width(idxType);
            return true;
          }
        }
        
        return false;
      };

      // Helper to build substitution map for a given step (int)
      auto buildStepSubstInt = [&](const ExprVector &vars, int64_t step) -> ExprMap {
        ExprMap subst;
        int varIdx = 0;
        for (auto &arr : traceArrays)
        {
          if (varIdx < (int)vars.size())
          {
            auto it = cexData.traceValueFuncs.find(arr);
            if (it != cexData.traceValueFuncs.end())
            {
              Expr indexVar = it->second.first;
              Expr valueFunc = it->second.second;
              Expr stepIdx = makeStepIndex(step, indexVar);
              Expr concreteValue = replaceAll(valueFunc, indexVar, stepIdx);
              subst[vars[varIdx]] = concreteValue;
            }
          }
          varIdx++;
        }
        return subst;
      };

      // Helper to build substitution map for a given step (Expr)
      auto buildStepSubstExpr = [&](const ExprVector &vars, Expr stepExpr) -> ExprMap {
        ExprMap subst;
        int varIdx = 0;
        for (auto &arr : traceArrays)
        {
          if (varIdx < (int)vars.size())
          {
            auto it = cexData.traceValueFuncs.find(arr);
            if (it != cexData.traceValueFuncs.end())
            {
              Expr indexVar = it->second.first;
              Expr valueFunc = it->second.second;
              Expr concreteValue = replaceAll(valueFunc, indexVar, stepExpr);
              subst[vars[varIdx]] = concreteValue;
            }
          }
          varIdx++;
        }
        return subst;
      };

      // Helper to substitute value functions into an expression
      // Given vars and step index, replace each var with f(step)
      auto substituteStep = [&](Expr expr, const ExprVector &vars, int64_t step) -> Expr {
        ExprMap subst = buildStepSubstInt(vars, step);
        return replaceAll(expr, subst);
      };

      // Version that takes an expression for the step (for large bitvector bounds)
      auto substituteStepExpr = [&](Expr expr, const ExprVector &vars, Expr stepExpr) -> Expr {
        ExprMap subst = buildStepSubstExpr(vars, stepExpr);
        return replaceAll(expr, subst);
      };

      SMTUtils solver(m_efac);

      // [Deep] Optimized: Synthesize valid bound N using Solver Query (Hybrid QF Approach)
      // Strategy: 
      // 1. Find candidate N such that Error(f(N)) is true (Reachability).
      // 2. Verify candidate N by checking if EXISTS k < N . !Trans(f(k), f(k+1)) is UNSAT (Validity).
      {
          bool isBvIndex = false;
          unsigned bvWidth = 0;
          if (!traceArrays.empty()) {
            auto it = cexData.traceValueFuncs.find(traceArrays[0]);
            if (it != cexData.traceValueFuncs.end()) isBvIndex = isIndexBvType(it->second.first, bvWidth);
          }
          
          Expr N;
          if (isBvIndex) N = bv::bvConst(mkTerm<string>("_FH_N_bound", m_efac), bvWidth);
          else N = bind::intConst(mkTerm<string>("_FH_N_bound", m_efac));
          
          // 1. Assert Query(f(N)) aka Error is reached at N
          Expr queryAtN = substituteStepExpr(queryCHC->body, queryCHC->srcVars, N);
          
          solver.push(); // Push context for the search loop
          solver.assertExpr(queryAtN);
          
          // Also enforce N > 0 to avoid trivial 0-length if init is error
          if (isBvIndex) solver.assertExpr(bv::bvugt(N, bv::bvnum(mpz_class(0), bvWidth, m_efac)));
          else solver.assertExpr(mk<GT>(N, mkMPZ(0, m_efac)));

          int attempts = 0;
          const int MAX_ATTEMPTS = 50; 
          bool found = false;

          while(attempts++ < MAX_ATTEMPTS)
          {
             boost::tribool res = solver.solve();
             if (!res) break; // UNSAT

             ExprSet modelVars; modelVars.insert(N);
             ExprMap model;
             solver.getModel(modelVars, model);
             Expr nVal = model[N];
             
             // Extract concrete value
             long long currentN = -1;
             if (nVal) {
                if (isOpX<MPZ>(nVal)) currentN = lexical_cast<long long>(nVal);
                else {
                    if (bv::is_bvnum(nVal)) {
                        mpz_class v = bv::toMpz(nVal);
                        if (v.fits_slong_p()) currentN = v.get_si();
                    }
                }
             }
             
             if (currentN <= 0) {
                 // Block invalid N
                 if (isBvIndex) solver.assertExpr(mk<NEG>(mk<EQ>(N, nVal))); 
                 else solver.assertExpr(mk<NEG>(mk<EQ>(N, nVal)));
                 continue;
             }
             
             if (debug) outs() << "  [Deep] Checking candidate N=" << currentN << "...\n";

             // 2. Verify transition for this N: check UNSAT( exists k < N . !Trans(f(k), f(k+1)) )
             solver.push(); // Scope for verification
             
             Expr k;
             if (isBvIndex) k = bv::bvConst(mkTerm<string>("_FH_k_check", m_efac), bvWidth);
             else k = bind::intConst(mkTerm<string>("_FH_k_check", m_efac));
             
             Expr kNext;
             if (isBvIndex) kNext = bv::bvadd(k, bv::bvnum(mpz_class(1), bvWidth, m_efac));
             else kNext = mk<PLUS>(k, mkTerm<mpz_class>(1, m_efac));
             
             Expr transBody = u.removeRedundantConjuncts(transCHC->body);
             ExprMap srcSubst = buildStepSubstExpr(transCHC->srcVars, k);
             ExprMap dstSubst = buildStepSubstExpr(transCHC->dstVars, kNext);
             Expr transAtK = replaceAll(replaceAll(transBody, srcSubst), dstSubst);
             
             // Condition: 0 <= k < N (use nVal which is concrete/constant expr)
             Expr rangeCond;
             if (isBvIndex) rangeCond = mk<AND>(bv::bvuge(k, bv::bvnum(mpz_class(0), bvWidth, m_efac)), bv::bvult(k, nVal));
             else rangeCond = mk<AND>(mk<GEQ>(k, mkMPZ(0, m_efac)), mk<LT>(k, nVal));
             
             // Assert: exists k in range such that Trans is VIOLATED
             solver.assertExpr(rangeCond);
             solver.assertExpr(mk<NEG>(transAtK)); // !Trans
             
             bool violationOnPath = false;
             boost::tribool vRes = solver.solve();
             if (vRes) violationOnPath = true;
             
             solver.pop(); // Clear verification assertions
             
             if (!violationOnPath) {
                  // UNSAT => No bad transitions => Valid Path!
                  // We only print this if debug is on or if it's a significant find
                  outs() << "  [Deep] Synthesized confirmed bound N = " << currentN << "\n";
                  cexData.traceEnd = currentN;
                  this->validatedTraceBound = currentN;
                  cexData.traceEndExpr = nVal;
                  cexData.boundsFound = true;
                  found = true;
                  break; // Found it
             } else {
                  // Path invalid, block this N and try again
                  if (debug) outs() << "  [Deep] Candidate N=" << currentN << " invalid (transition break). Retrying...\n";
                  solver.assertExpr(mk<NEG>(mk<EQ>(N, nVal)));
             }
          }
          
          if (!found && debug) outs() << "  [Deep] No valid bound N found within attempt limit.\n";
          
          solver.pop(); // Cleanup search context
          solver.reset();
      }

      tribool result = true;
      long long initTime = 0, transTime = 0, propTime = 0;

      auto setupEnd = high_resolution_clock::now();
      auto setupTime = duration_cast<microseconds>(setupEnd - parseEnd).count();

      // === Check 1: Init ===
      // Substitute f(0) into init body and check it's satisfiable (TRUE)
      {
        auto initStart = high_resolution_clock::now();
        Expr initBody = initCHC->body;
        Expr initSubst = substituteStep(initBody, initCHC->dstVars, 0);
        
        if (debug)
          outs() << "  [Inductive] Init check: " << *initSubst << "\n";
        
        Expr initSimpl = u.simplify(initSubst);
        tribool initResult = solver.isSat(initSimpl);
        
        auto initEnd = high_resolution_clock::now();
        initTime = duration_cast<microseconds>(initEnd - initStart).count();
        
        if (initResult == true)
        {
          outs() << "  [Inductive] Init: PASS (f(0) satisfies init)\n";
        }
        else
        {
          outs() << "  [Inductive] Init: FAIL (f(0) does not satisfy init)\n";
          ExprMap initSubstMap = buildStepSubstInt(initCHC->dstVars, 0);
          reportInductiveFailure(initCHC->body, initSubstMap, initCHC->dstVars, "Init");
          result = false;
        }
      }

      // === Check 2: Transition (Inductive Step) ===
      // For validity: check that NOT(substituted_trans) is UNSAT
      // This proves: forall i: f(i) => f(i+1)
      {
        auto transStart = high_resolution_clock::now();
        
        // Determine index type from the first trace value function
        bool isBvIndex = false;
        unsigned bvWidth = 0;
        if (!traceArrays.empty())
        {
          auto it = cexData.traceValueFuncs.find(traceArrays[0]);
          if (it != cexData.traceValueFuncs.end())
          {
            isBvIndex = isIndexBvType(it->second.first, bvWidth);
          }
        }

        // Create symbolic index variable and i+1 expression based on index type
        Expr iVar, iPlusOne, boundsExpr;
        if (isBvIndex)
        {
          iVar = bv::bvConst(mkTerm<string>("_cex_i", m_efac), bvWidth);
          iPlusOne = bv::bvadd(iVar, bv::bvnum(mpz_class(1), bvWidth, m_efac));
          // bounds: 0 <= i <= traceEnd - 1 (as bitvectors)
          // Use expression bounds when available (for values exceeding int64)
          Expr startBound = cexData.traceStartExpr ? cexData.traceStartExpr 
                            : bv::bvnum(mpz_class(cexData.traceStart), bvWidth, m_efac);
          Expr endBound;
          if (cexData.traceEndExpr)
          {
            // traceEnd - 1 for the transition check (we check i and i+1)
            endBound = bv::bvsub(cexData.traceEndExpr, bv::bvnum(mpz_class(1), bvWidth, m_efac));
          }
          else
          {
            // Handle N=0 case to avoid underflow in traceEnd - 1
            endBound = bv::bvnum(mpz_class(cexData.traceEnd > 0 ? cexData.traceEnd - 1 : 0), bvWidth, m_efac);
          }
          
          if (cexData.traceEnd == 0 && !cexData.traceEndExpr)
          {
             // Empty range for N=0, make bounds false
             boundsExpr = mk<FALSE>(m_efac);
          }
          else
          {
             boundsExpr = mk<AND>(
               bv::bvuge(iVar, startBound),
               bv::bvule(iVar, endBound)
             );
          }
        }
        else
        {
          iVar = bind::intConst(mkTerm<string>("_cex_i", m_efac));
          iPlusOne = mk<PLUS>(iVar, mkTerm<mpz_class>(1, m_efac));
          boundsExpr = mk<AND>(
            mk<GEQ>(iVar, mkTerm<mpz_class>(cexData.traceStart, m_efac)),
            mk<LEQ>(iVar, mkTerm<mpz_class>(cexData.traceEnd - 1, m_efac))
          );
        }

        // Substitute f(i) for srcVars and f(i+1) for dstVars
        ExprMap srcSubst, dstSubst;
        
        int varIdx = 0;
        for (auto &arr : traceArrays)
        {
          auto it = cexData.traceValueFuncs.find(arr);
          if (it != cexData.traceValueFuncs.end())
          {
            Expr indexVar = it->second.first;  // Actual index var from CCEX
            Expr valueFunc = it->second.second;
            
            // f(i) for srcVars
            if (varIdx < (int)transCHC->srcVars.size())
            {
              Expr srcValue = replaceAll(valueFunc, indexVar, iVar);
              srcSubst[transCHC->srcVars[varIdx]] = srcValue;
            }
            
            // f(i+1) for dstVars
            if (varIdx < (int)transCHC->dstVars.size())
            {
              Expr dstValue = replaceAll(valueFunc, indexVar, iPlusOne);
              dstSubst[transCHC->dstVars[varIdx]] = dstValue;
            }
          }
          varIdx++;
        }

        // Substitute into transition body
        Expr transBody = u.removeRedundantConjuncts(transCHC->body);
        Expr transWithSrc = replaceAll(transBody, srcSubst);
        Expr transWithBoth = replaceAll(transWithSrc, dstSubst);
        
        if (debug)
        {
          outs() << "  [Inductive] Trans body: " << *transBody << "\n";
          outs() << "  [Inductive] Trans after substitution: " << *transWithBoth << "\n";
        }
        
        // Simplify the formula first - this may reduce int2bv(x+1) = bvadd(int2bv(x), 1) to TRUE
        Expr transSimpl = transWithBoth; 
        // transSimpl = u.simplify(transWithBoth);

        if (debug)
          outs() << "  [Inductive] Trans simplified: " << *transSimpl << "\n";
        
        // First, check if simplification already proved it
        if (isOpX<TRUE>(transSimpl))
        {
          auto transEnd = high_resolution_clock::now();
          transTime = duration_cast<microseconds>(transEnd - transStart).count();
          outs() << "  [Inductive] Transition: PASS (simplified to TRUE)\n";
        }
        else
        {
          // For validity check: (bounds /\ NOT(substituted_trans)) should be UNSAT
          Expr validityCheck = mk<AND>(boundsExpr, mk<NEG>(transSimpl));
          validityCheck = u.simplify(validityCheck);
          if (isOpX<TRUE>(validityCheck))
          {
            auto transEnd = high_resolution_clock::now();
            transTime = duration_cast<microseconds>(transEnd - transStart).count();
            outs() << "  [Inductive] Transition: PASS (simplified to TRUE)\n";
          }
          else 
          {
            if (debug)
              outs() << "  [Inductive] Trans validity check (expect UNSAT): " << *validityCheck << "\n";
            
            tribool transResult = solver.isSat(validityCheck);
            auto transEnd = high_resolution_clock::now();
            transTime = duration_cast<microseconds>(transEnd - transStart).count();
            
            if (transResult == false)
            {
              outs() << "  [Inductive] Transition: PASS (f(i) => f(i+1) is valid)\n";
            }
            else
            {
              outs() << "  [Inductive] Transition: FAIL (f(i) => f(i+1) is not valid)\n";
              
              // Get failing index i from model
              Expr failingI = solver.getModel(iVar);
              if (failingI)
              {
                 outs() << "    Failing step i = " << *failingI << "\n";
                 
                 // Build substitution for this i
                 ExprMap srcSubst = buildStepSubstExpr(transCHC->srcVars, failingI);
                 
                 Expr failingIPlusOne;
                 if (isBvIndex)
                   failingIPlusOne = bv::bvadd(failingI, bv::bvnum(mpz_class(1), bvWidth, m_efac));
                 else
                   failingIPlusOne = mk<PLUS>(failingI, mkTerm<mpz_class>(1, m_efac));
                   
                 ExprMap dstSubst = buildStepSubstExpr(transCHC->dstVars, failingIPlusOne);
                 
                 // Merge maps
                 ExprMap fullSubst = srcSubst;
                 fullSubst.insert(dstSubst.begin(), dstSubst.end());
                 
                 // Combine vars for reporting
                 ExprVector allVars = transCHC->srcVars;
                 allVars.insert(allVars.end(), transCHC->dstVars.begin(), transCHC->dstVars.end());
                 
                 reportInductiveFailure(transCHC->body, fullSubst, allVars, "Transition");
              }
              result = false;
            }

          }

        }
      }

      // === Check 3: Property (Query) ===
      // Substitute f(N) into query body and check it's satisfiable (reaches error)
      // The trace goes from step 0 to step traceEnd, so we check the property at traceEnd
      {
        auto propStart = high_resolution_clock::now();
        Expr queryBody = queryCHC->body;
        
        Expr querySubst;
        if (cexData.traceEndExpr)
        {
          // Use the expression directly for large bitvector bounds
          querySubst = substituteStepExpr(queryBody, queryCHC->srcVars, cexData.traceEndExpr);
          if (debug)
          {
            outs() << "  [Inductive] Property check at step (expr) " << *cexData.traceEndExpr << "\n";
            outs() << "  [Inductive] Query body: " << *queryBody << "\n";
            outs() << "  [Inductive] Query substituted: " << *querySubst << "\n";
          }
        }
        else
        {
          // Use the int64_t value
          int64_t propertyStep = cexData.traceEnd;
          querySubst = substituteStep(queryBody, queryCHC->srcVars, propertyStep);
          if (debug)
          {
            outs() << "  [Inductive] Property check at step " << propertyStep << "\n";
            outs() << "  [Inductive] Query body: " << *queryBody << "\n";
            outs() << "  [Inductive] Query substituted: " << *querySubst << "\n";
          }
        }
        
        Expr querySimpl = u.simplify(querySubst);
        if (debug)
          outs() << "  [Inductive] Query simplified: " << *querySimpl << "\n";
        tribool queryResult = solver.isTrue(querySimpl);
        
        auto propEnd = high_resolution_clock::now();
        propTime = duration_cast<microseconds>(propEnd - propStart).count();
        
        if (queryResult == true)
        {
          outs() << "  [Inductive] Property: PASS (f(N) reaches error state)\n";
          
          // Report variables responsible for the error state
          ExprMap querySubstMap;
          if (cexData.traceEndExpr)
            querySubstMap = buildStepSubstExpr(queryCHC->srcVars, cexData.traceEndExpr);
          else
            querySubstMap = buildStepSubstInt(queryCHC->srcVars, cexData.traceEnd);
            
          reportValidCEXVariables(queryCHC->body, querySubstMap, queryCHC->srcVars, "Property");
        }
        else
        {
          outs() << "  [Inductive] Property: FAIL (f(N) does not reach error)\n";
          ExprMap querySubstMap;
          if (cexData.traceEndExpr)
            querySubstMap = buildStepSubstExpr(queryCHC->srcVars, cexData.traceEndExpr);
          else
            querySubstMap = buildStepSubstInt(queryCHC->srcVars, cexData.traceEnd);
            
          reportInductiveFailure(queryCHC->body, querySubstMap, queryCHC->srcVars, "Property");
          result = false;
        }
      }

      auto totalEnd = high_resolution_clock::now();
      auto totalTime = duration_cast<microseconds>(totalEnd - totalStart).count();
      
      // Print timing stats
      outs() << "  [Inductive Timing] Parse: " << (parseTime/1000.0) << "ms, "
             << "Setup: " << (setupTime/1000.0) << "ms, "
             << "Init: " << (initTime/1000.0) << "ms, "
             << "Trans: " << (transTime/1000.0) << "ms, "
             << "Prop: " << (propTime/1000.0) << "ms, "
             << "Total: " << (totalTime/1000.0) << "ms\n";

      // If standard validation failed, try partial CEX validation via slicing
      if (result == false)
      {
        // Compute cone of influence from property
        set<int> cone = computeConeOfInfluence(queryCHC, transCHC);
        
        // Check if this is a partial CEX (trace has fewer variables than system)
        size_t totalVars = transCHC ? transCHC->srcVars.size() : 0;
        bool isPartialCEX = (traceArrays.size() < totalVars);
        
        if (debug)
        {
          if (isPartialCEX)
            outs() << "  [Slicing] Detected partial CEX: trace has " << traceArrays.size() 
                   << " vars, system has " << totalVars << " vars\n";
          else
             outs() << "  [Slicing] Full CEX detected, checking if slicing can rescue validation...\n";
        }
        
        // Check if trace covers the cone of influence
        bool coversCone = traceCoversCone(traceArrays, cone, transCHC);

        if (coversCone)
        {
          outs() << "  [Slicing] Trace covers cone of influence, attempting partial validation...\n";
          
          // Try partial validation with only cone variables
          tribool partialResult = validatePartialCEXInductive(ccex, cone, initCHC, transCHC, 
                                                               queryCHC, cexData, traceArrays);
          
          if (partialResult == true)
          {
            outs() << "  [Inductive] CEX VALID (Partial): Trace covers cone of influence\n";
            return true;
          }
        }
        else if (isPartialCEX)
        {
          outs() << "  [Slicing] Trace does NOT cover cone of influence\n";
          outs() << "  [Slicing] Cone requires variable indices: {";
          for (int idx : cone) outs() << idx << " ";
          outs() << "}\n";
          outs() << "  [Slicing] Trace provides " << traceArrays.size() << " variables\n";
        }
      }

      // Final result
      if (result == true)
      {
        outs() << "  [Inductive] CEX VALID: All 3 checks passed\n";
      }
      else
      {
        outs() << "  [Inductive] CEX INVALID: One or more checks failed\n";
      }

      return result;
    }

    void guessRandomTrace(vector<int> &trace)
    {
      std::srand(std::time(0));
      Expr curRel = mk<TRUE>(m_efac);

      while (curRel != ruleManager.failDecl)
      {
        int range = ruleManager.outgs[curRel].size();
        int chosen = guessUniformly(range);
        int chcId = ruleManager.outgs[curRel][chosen];
        curRel = ruleManager.chcs[chcId].dstRelation;
        trace.push_back(chcId);
      }
    }

    bool already_unsat(vector<int> &t)
    {
      bool unsat = false;
      for (auto u : unsat_prefs)
      {
        if (u.size() > t.size())
          continue;
        bool found = true;
        for (int j = 0; j < u.size(); j++)
        {
          if (u[j] != t[j])
          {
            found = false;
            break;
          }
        }
        if (found)
        {
          unsat = true;
          break;
        }
      }
      return unsat;
    }

    // Efficiently build a single trace of given length (iterative, not recursive)
    // Returns true if a valid trace was found
    bool getSingleTrace(Expr src, Expr dst, int64_t len, vector<int> &trace)
    {
      trace.clear();
      trace.reserve(static_cast<size_t>(len));
      
      Expr current = src;
      for (int64_t step = 0; step < len; step++)
      {
        bool found = false;
        Expr target = (step == len - 1) ? dst : Expr(nullptr);
        
        for (auto a : ruleManager.outgs[current])
        {
          Expr nextRel = ruleManager.chcs[a].dstRelation;
          
          // On last step, must reach dst; otherwise just pick any valid transition
          if (step == len - 1)
          {
            if (nextRel == dst)
            {
              trace.push_back(a);
              found = true;
              break;
            }
          }
          else
          {
            // Pick the first available transition (typically the loop)
            trace.push_back(a);
            current = nextRel;
            found = true;
            break;
          }
        }
        
        if (!found)
          return false;
      }
      
      return true;
    }

    /**
     * Extract a concrete counterexample trace using solver-verified execution.
     * 
     * This method:
     * 1. Finds a valid trace path to the bad state using bounded exploration
     * 2. Builds the SSA formula for the trace
     * 3. Checks satisfiability and extracts concrete values from the model
     * 4. Returns a vector of (variable -> concrete_value) maps for each step
     * 
     * @param max_steps      Maximum number of steps to explore
     * @param outTrace       Output: vector of state maps, one per step
    /**
     * Incrementally add one step to the SSA and update bindVars.
     * This appends to ssa and bindVars rather than rebuilding from scratch.
     * 
     * @param step        The CHC rule index for this step
     * @param bindVars1   Current variable bindings (input/output - updated to dstVars)
     * @param ssa         SSA formulas (appended to)
     * @param bindVar_index  Counter for unique variable names (input/output)
     * @param locVar_index   Counter for local variable names (input/output)
     */
    void appendSSAStep(int step, ExprVector& bindVars1, ExprVector& ssa, 
                       int64_t& bindVar_index, int64_t& locVar_index)
    {
      ExprVector bindVars2;
      HornRuleExt &hr = ruleManager.chcs[step];
      
      Expr body = hr.body;
      if (!hr.isFact && extraLemmas != NULL)
        body = mk<AND>(extraLemmas, body);
      body = replaceAll(body, hr.srcVars, bindVars1);
      
      for (int i = 0; i < hr.dstVars.size(); i++)
      {
        bool kept = false;
        for (int j = 0; j < hr.srcVars.size(); j++)
        {
          if (hr.dstVars[i] == hr.srcVars[j])
          {
            bindVars2.push_back(bindVars1[i]);
            kept = true;
          }
        }
        if (!kept)
        {
          Expr new_name = mkTerm<string>("__bnd_var_" + to_string(bindVar_index++), m_efac);
          bindVars2.push_back(cloneVar(hr.dstVars[i], new_name));
        }
        
        body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
      }
      
      for (int i = 0; i < hr.locVars.size(); i++)
      {
        Expr new_name = mkTerm<string>("__loc_var_" + to_string(locVar_index++), m_efac);
        Expr var = cloneVar(hr.locVars[i], new_name);
        body = replaceAll(body, hr.locVars[i], var);
      }
      
      ssa.push_back(body);
      bindVars.push_back(bindVars2);
      bindVars1 = bindVars2;
    }

    /**
     * Extract a concrete counterexample trace using incremental SAT solving.
     * 
     * This optimized method:
     * 1. Uses push/pop to avoid resetting the solver between length checks
     * 2. Incrementally adds transition constraints without rebuilding SSA
     * 3. Pushes the property constraint, checks SAT, then pops for next iteration
     * 
     * @param max_steps      Maximum number of steps to explore
     * @param outTrace       Output: vector of state maps, one per step
     * @param outStateVars   Output: the state variables (in order)
     * @param sparse_factor  Optional: sample every Nth point (1 = all points)
     * @return true if a valid trace was found and extracted
     */
    bool extractConcreteTrace(
        int64_t max_steps,
        std::vector<std::map<Expr, Expr>>& outTrace,
        ExprVector& outStateVars,
        int sparse_factor = 1)
    {
      outTrace.clear();
      outStateVars.clear();
      bindVars.clear();
      
      if (debug)
        outs() << "\n=== Extracting Concrete Trace (Incremental) ===\n";
      
      // Check if ruleManager has valid failDecl
      if (ruleManager.failDecl == nullptr)
      {
        if (debug)
          outs() << "  Error: No fail declaration found\n";
        return false;
      }
      
      // Identify the CHC rules we need:
      // - initRule: fact (isFact=true) that establishes initial state
      // - loopRule: inductive (isInductive=true) transition
      // - queryRule: query (isQuery=true) that reaches fail state
      int initRule = -1, loopRule = -1, queryRule = -1;
      
      for (size_t i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto& chc = ruleManager.chcs[i];
        if (chc.isFact) initRule = i;
        if (chc.isInductive) loopRule = i;
        if (chc.isQuery) queryRule = i;
      }
      
      if (initRule < 0 || loopRule < 0 || queryRule < 0)
      {
        if (debug)
          outs() << "  Warning: Could not identify all CHC types, falling back to non-incremental\n";
        return extractConcreteTraceNonIncremental(max_steps, outTrace, outStateVars, sparse_factor);
      }
      
      // Get state variables from the loop rule
      outStateVars = ruleManager.chcs[loopRule].srcVars;
      if (outStateVars.empty())
      {
        outs() << "  Error: Could not identify state variables\n";
        return false;
      }
      
      if (debug)
        outs() << "  State variables: " << outStateVars.size() << "\n";
      
      // Incremental solving with push/pop:
      // We build: Init /\ Trans^k and use push/pop to temporarily check Query
      // This avoids O(L^2) solver resets
      
      ExprVector ssa;
      ExprMap extractedModel;
      bool found = false;
      
      // Initialize with the init rule
      ExprVector currentVars = ruleManager.chcs[initRule].srcVars;
      int64_t bindVar_index = 0;
      int64_t locVar_index = 0;
      
      // Add init constraint to SSA (and bindVars tracking)
      appendSSAStep(initRule, currentVars, ssa, bindVar_index, locVar_index);
      
      // Reset solver and assert init constraint (this stays permanently)
      u.reset();
      u.assertExpr(ssa[0]);
      
      // Now incrementally add loop steps and check with query
      for (int64_t len = 2; len <= max_steps; len++)
      {
        // Add one more loop iteration
        appendSSAStep(loopRule, currentVars, ssa, bindVar_index, locVar_index);
        
        // Assert the new transition constraint (stays in solver permanently)
        u.assertExpr(ssa.back());
        
        // Build the query constraint: substitute currentVars into queryRule's srcVars
        HornRuleExt& qr = ruleManager.chcs[queryRule];
        Expr queryBody = qr.body;
        queryBody = replaceAll(queryBody, qr.srcVars, currentVars);
        
        // Use push/pop to temporarily check the query
        u.push();
        u.assertExpr(queryBody);
        tribool satResult = u.solve();
        
        if (debug)
        {
          outs() << "\r  Trying length " << len << " ... " 
                 << (satResult == true ? "SAT   " : (satResult == false ? "UNSAT " : "UNKNOWN")) 
                 << "          ";
          outs().flush();
        }
        
        if (satResult == true)
        {
          // Found a satisfying trace - extract model before popping
          found = true;
          if (debug)
            outs() << "\n  Found satisfiable trace of length " << len << "\n";
          
          // Collect ONLY variables for sparse points to save massive memory
          ExprSet sparseVars;
          for (size_t step = 0; step < bindVars.size(); step++)
          {
            if (sparse_factor > 1 && step % sparse_factor != 0 && step != bindVars.size() - 1)
              continue;
              
            for (const auto& var : bindVars[step])
            {
              if (var != nullptr) sparseVars.insert(var);
            }
          }
          
          u.getModel(sparseVars, extractedModel);
          
          if (debug)
            outs() << "  Extracted sparse model has " << extractedModel.size() << " entries\n";
          
          u.pop();  // Clean up
          break;
        }
        
        // UNSAT or UNKNOWN: pop to remove the query constraint
        // The transition constraints remain in the solver
        u.pop();
      }
      
      if (!found)
      {
        if (debug)
          outs() << "\n  No satisfiable trace found within " << max_steps << " steps\n";
        return false;
      }
      
      // Extract trace values from bindVars
      for (size_t step = 0; step < bindVars.size(); step++)
      {
        if (sparse_factor > 1 && step % sparse_factor != 0 && step != bindVars.size() - 1)
          continue;
          
        std::map<Expr, Expr> stepState;
        const ExprVector& stepVars = bindVars[step];
        
        if (debug)
          outs() << "  Step " << step << ": bindVars has " << stepVars.size() << " vars\n";
        
        for (size_t i = 0; i < stepVars.size() && i < outStateVars.size(); i++)
        {
          Expr var = stepVars[i];
          if (var == nullptr) continue;
          
          Expr val = nullptr;
          auto it = extractedModel.find(var);
          if (it != extractedModel.end())
          {
            val = it->second;
            if (debug)
              outs() << "    Found value for " << *var << " = " << *val << "\n";
          }
          
          if (val == nullptr || val == var)
          {
            Expr vtype = bind::typeOf(var);
            if (vtype != nullptr && bv::is_bvsort(vtype))
              val = bv::bvnum(mpz_class(0), bv::width(vtype), m_efac);
            else
              val = mkTerm(mpz_class(0), m_efac);
            if (debug)
              outs() << "    Warning: Using default 0 for " << *var << "\n";
          }
          
          stepState[outStateVars[i]] = val;
        }
        
        outTrace.push_back(stepState);
        
        if (debug && step % 100 == 0)
          outs() << "    Extracted step " << step << "\n";
      }
      
      if (debug)
        outs() << "  Extracted " << outTrace.size() << " trace points\n";
      
      return true;
    }
    
    /**
     * Non-incremental version of extractConcreteTrace (fallback).
     * Used when the CHC structure doesn't fit the simple init/loop/query pattern.
     */
    bool extractConcreteTraceNonIncremental(
        int64_t max_steps,
        std::vector<std::map<Expr, Expr>>& outTrace,
        ExprVector& outStateVars,
        int sparse_factor = 1)
    {
      outTrace.clear();
      outStateVars.clear();
      
      if (debug)
        outs() << "\n=== Extracting Concrete Trace (Non-Incremental Fallback) ===\n";
      
      ExprMap extractedModel;
      vector<int> trace;
      bool found = false;
      
      for (int64_t len = 2; len <= max_steps; len++)
      {
        if (!getSingleTrace(mk<TRUE>(m_efac), ruleManager.failDecl, len, trace))
          continue;
        
        ExprVector ssa;
        getSSA(trace, ssa);
        
        tribool satResult = u.isSat(ssa);
        
        if (debug)
        {
          outs() << "\r  Trying length " << len << " ... " 
                 << (satResult == true ? "SAT   " : (satResult == false ? "UNSAT " : "UNKNOWN")) 
                 << "          ";
          outs().flush();
        }
        
        if (satResult == true)
        {
          found = true;
          if (debug)
            outs() << "\n  Found satisfiable trace of length " << len << "\n";
          
          ExprSet allVars;
          for (const auto& stepVars : bindVars)
          {
            for (const auto& var : stepVars)
            {
              if (var != nullptr) allVars.insert(var);
            }
          }
          
          u.getModel(allVars, extractedModel);
          
          if (debug)
            outs() << "  Extracted model has " << extractedModel.size() << " entries\n";
          
          break;
        }
      }
      
      if (!found)
      {
        if (debug)
          outs() << "\n  No satisfiable trace found within " << max_steps << " steps\n";
        return false;
      }
      
      for (auto& chc : ruleManager.chcs)
      {
        if (chc.isInductive)
        {
          outStateVars = chc.srcVars;
          break;
        }
      }
      
      if (outStateVars.empty())
      {
        outs() << "  Error: Could not identify state variables\n";
        return false;
      }
      
      for (size_t step = 0; step < bindVars.size(); step++)
      {
        if (sparse_factor > 1 && step % sparse_factor != 0 && step != bindVars.size() - 1)
          continue;
          
        std::map<Expr, Expr> stepState;
        const ExprVector& stepVars = bindVars[step];
        
        for (size_t i = 0; i < stepVars.size() && i < outStateVars.size(); i++)
        {
          Expr var = stepVars[i];
          if (var == nullptr) continue;
          
          Expr val = nullptr;
          auto it = extractedModel.find(var);
          if (it != extractedModel.end())
            val = it->second;
          
          if (val == nullptr || val == var)
          {
            Expr vtype = bind::typeOf(var);
            if (vtype != nullptr && bv::is_bvsort(vtype))
              val = bv::bvnum(mpz_class(0), bv::width(vtype), m_efac);
            else
              val = mkTerm(mpz_class(0), m_efac);
          }
          
          stepState[outStateVars[i]] = val;
        }
        
        outTrace.push_back(stepState);
      }
      
      if (debug)
        outs() << "  Extracted " << outTrace.size() << " trace points\n";
      
      return true;
    }

    /**
     * Extract Model-Based Projection (MBP) guards from CHC cycles.
     * MBPs represent phase conditions that distinguish different behaviors.
     * These can be used to seed the SyGuS grammar with meaningful conditionals.
     * 
     * For BV CHCs, translates to LIA, computes MBPs, then translates back.
     * 
     * @param outGuards  Output vector of guard expressions (in BV if input was BV)
     * @return true if any guards were extracted
     */
    bool extractMBPGuards(ExprVector& outGuards)
    {
      outGuards.clear();
      
      // Skip if no cycles in the CHC system
      if (!ruleManager.hasCycles())
      {
        if (debug)
          outs() << "  [MBP] No cycles found, skipping MBP extraction\n";
        return false;
      }
      
      if (debug)
        outs() << "\n=== Extracting MBP Guards ===\n";
      
      // For BV CHCs, we need to translate to LIA first since MBP works on LIA
      bool needsTranslation = ruleManager.hasBV;
      unsigned originalBvWidth = 0;
      
      // Determine BV width if we have bitvectors
      if (needsTranslation)
      {
        for (auto& chc : ruleManager.chcs)
        {
          for (auto& v : chc.srcVars)
          {
            Expr vtype = bind::typeOf(v);
            if (bv::is_bvsort(vtype))
            {
              originalBvWidth = std::max(originalBvWidth, bv::width(vtype));
            }
          }
        }
        if (originalBvWidth == 0) originalBvWidth = 32;
        
        if (debug)
          outs() << "  [MBP] BV CHCs detected, width=" << originalBvWidth << ", translating to LIA\n";
      }
      
      try
      {
        // Get a reference to working CHCs (translated if needed)
        CHCs* workingCHCs = &ruleManager;
        std::unique_ptr<Bv2LiaTranslator> bv2lia;
        CHCs liaCHCs(m_efac, ruleManager.m_z3, debug ? 1 : 0);
        
        if (needsTranslation)
        {
          bv2lia.reset(new Bv2LiaTranslator(m_efac, ruleManager.m_z3, originalBvWidth, debug ? 1 : 0));
          liaCHCs = bv2lia->translate(ruleManager, false);
          workingCHCs = &liaCHCs;
          
          if (debug)
            outs() << "  [MBP] Translated to LIA, " << liaCHCs.chcs.size() << " CHCs\n";
        }
        
        // Process each cycle to extract MBPs
        ExprVector liaGuards;
        
        for (auto& dcl : workingCHCs->wtoDecls)
        {
          if (workingCHCs->cycles.find(dcl) == workingCHCs->cycles.end())
            continue;
          
          for (size_t cycleNum = 0; cycleNum < workingCHCs->cycles[dcl].size(); cycleNum++)
          {
            std::vector<int>& cycle = workingCHCs->cycles[dcl][cycleNum];
            if (cycle.empty()) continue;
            
            if (debug)
              outs() << "  [MBP] Processing cycle " << cycleNum << " for " << *dcl << "\n";
            
            // Build SSA formula for the cycle
            BndExpl cycleBnd(*workingCHCs, debug);
            Expr ssa = cycleBnd.toExpr(cycle);
            
            if (debug)
              outs() << "  [MBP] SSA: " << *ssa << "\n";
            
            // Get source and destination variables
            ExprVector& srcVars = workingCHCs->chcs[cycle[0]].srcVars;
            ExprVector& dstVars = workingCHCs->chcs[cycle.back()].dstVars;
            
            // Variables to keep in projection (source vars)
            ExprVector vars2keep;
            for (auto& v : srcVars)
            {
              vars2keep.push_back(v);
            }
            
            // Use SMTUtils to compute MBPs via lazy DNF
            SMTUtils mbpUtils(m_efac);
            ExprVector prjcts;
            
            // Identity function for QE (no quantifier elimination, just projection)
            auto identityQE = [](Expr a, ExprVector& vars) { return a; };
            
            bool flattenOk = mbpUtils.flatten(ssa, prjcts, false, vars2keep, identityQE);
            
            if (!flattenOk || prjcts.empty())
            {
              if (debug)
                outs() << "  [MBP] No projections found for cycle " << cycleNum << "\n";
              continue;
            }
            
            if (debug)
              outs() << "  [MBP] Found " << prjcts.size() << " projections\n";
            
            // Process each projection
            for (auto& prj : prjcts)
            {
              // Weaken by removing constraints that only mention destination vars
              ExprSet cnjs;
              getConj(prj, cnjs);
              
              ExprSet srcVarSet(srcVars.begin(), srcVars.end());
              ExprSet filteredCnjs;
              
              for (auto& cnj : cnjs)
              {
                // Check if this conjunct mentions any source variable
                ExprSet vars;
                filter(cnj, bind::IsConst(), std::inserter(vars, vars.begin()));
                
                bool mentionsSrc = false;
                for (auto& v : vars)
                {
                  if (srcVarSet.count(v) > 0)
                  {
                    mentionsSrc = true;
                    break;
                  }
                }
                
                if (mentionsSrc)
                  filteredCnjs.insert(cnj);
              }
              
              // Extract atomic predicates (comparisons) from the filtered conjuncts
              // instead of using the full conjunction
              for (auto& cnj : filteredCnjs)
              {
                // Only keep atomic comparison predicates, not complex formulas
                // Check if this is an atomic comparison (not an AND/OR/etc)
                bool isAtomicComparison = 
                    isOpX<LT>(cnj) || isOpX<LEQ>(cnj) || isOpX<GT>(cnj) || isOpX<GEQ>(cnj) ||
                    isOpX<EQ>(cnj) || isOpX<NEQ>(cnj) ||
                    isOpX<BULT>(cnj) || isOpX<BULE>(cnj) || isOpX<BUGT>(cnj) || isOpX<BUGE>(cnj) ||
                    isOpX<BSLT>(cnj) || isOpX<BSLE>(cnj) || isOpX<BSGT>(cnj) || isOpX<BSGE>(cnj);
                
                if (!isAtomicComparison) continue;
                
                // Skip trivial comparisons like x = x or x < x
                if (cnj->arity() == 2 && cnj->left() == cnj->right()) continue;
                
                // Check we haven't already added this guard
                bool isDuplicate = false;
                for (auto& existing : liaGuards)
                {
                  if (cnj == existing)
                  {
                    isDuplicate = true;
                    break;
                  }
                }
                
                if (!isDuplicate)
                {
                  liaGuards.push_back(cnj);
                  if (debug)
                    outs() << "  [MBP] Atomic guard: " << *cnj << "\n";
                }
              }
            }
          }
        }
        
        if (liaGuards.empty())
        {
          if (debug)
            outs() << "  [MBP] No guards extracted\n";
          return false;
        }
        
        // Translate guards back to BV if needed
        if (needsTranslation)
        {
          if (debug)
            outs() << "  [MBP] Translating " << liaGuards.size() << " guards back to BV\n";
          
          Lia2BvTranslator lia2bv(m_efac, ruleManager.m_z3, originalBvWidth, debug ? 1 : 0);
          
          for (auto& guard : liaGuards)
          {
            Expr bvGuard = lia2bv.translateExpr(guard);
            if (bvGuard != nullptr)
            {
              outGuards.push_back(bvGuard);
              if (debug)
                outs() << "  [MBP] BV Guard: " << *bvGuard << "\n";
            }
          }
        }
        else
        {
          outGuards = liaGuards;
        }
        
        if (debug)
          outs() << "  [MBP] Extracted " << outGuards.size() << " MBP guards\n";
        
        return !outGuards.empty();
      }
      catch (const std::exception& e)
      {
        if (debug)
          outs() << "  [MBP] Error during extraction: " << e.what() << "\n";
        return false;
      }
    }

    /**
     * Extract invariants via Houdini-style bootstrapping on LIA-translated CHCs.
     * For BV CHCs, translates to LIA, runs lightweight invariant learning,
     * then translates learned invariants back to BV.
     * 
     * These invariants can be used to seed the SyGuS grammar with meaningful
     * relational constraints that hold at the loop head.
     * 
     * @param outInvariants  Output vector of invariant expressions (in BV if input was BV)
     * @return true if any invariants were learned
     */
    bool extractBootstrapInvariants(ExprVector& outInvariants)
    {
      outInvariants.clear();
      
      // Skip if no cycles in the CHC system
      if (!ruleManager.hasCycles())
      {
        if (debug)
          outs() << "  [Bootstrap] No cycles found, skipping invariant extraction\n";
        return false;
      }
      
      if (debug)
        outs() << "\n=== Extracting Bootstrap Invariants ===\n";
      
      // For BV CHCs, we need to translate to LIA first since invariant learning works on LIA
      bool needsTranslation = ruleManager.hasBV;
      unsigned originalBvWidth = 0;
      
      // Determine BV width if we have bitvectors
      if (needsTranslation)
      {
        for (auto& chc : ruleManager.chcs)
        {
          for (auto& v : chc.srcVars)
          {
            Expr vtype = bind::typeOf(v);
            if (bv::is_bvsort(vtype))
            {
              originalBvWidth = std::max(originalBvWidth, bv::width(vtype));
            }
          }
        }
        if (originalBvWidth == 0) originalBvWidth = 32;
        
        if (debug)
          outs() << "  [Bootstrap] BV CHCs detected, width=" << originalBvWidth << ", translating to LIA\n";
      }
      
      try
      {
        // Get a reference to working CHCs (translated if needed)
        CHCs* workingCHCs = &ruleManager;
        std::unique_ptr<Bv2LiaTranslator> bv2lia;
        CHCs liaCHCs(m_efac, ruleManager.m_z3, debug ? 1 : 0);
        
        if (needsTranslation)
        {
          bv2lia.reset(new Bv2LiaTranslator(m_efac, ruleManager.m_z3, originalBvWidth, debug ? 1 : 0));
          liaCHCs = bv2lia->translate(ruleManager, false);
          workingCHCs = &liaCHCs;
          
          if (debug)
            outs() << "  [Bootstrap] Translated to LIA, " << liaCHCs.chcs.size() << " CHCs\n";
        }
        
        // Collect candidate invariants from CHC bodies (seed mining style)
        ExprVector liaInvariants;
        
        for (auto& dcl : workingCHCs->wtoDecls)
        {
          if (debug)
            outs() << "  [Bootstrap] Processing declaration: " << *dcl << "\n";
          
          ExprVector& invVarVec = workingCHCs->invVars[dcl];
          
          // Collect constraints from CHC bodies that only mention invariant variables
          for (auto& chc : workingCHCs->chcs)
          {
            if (chc.dstRelation != dcl) continue;
            
            ExprSet cnjs;
            getConj(chc.body, cnjs);
            
            for (auto& cnj : cnjs)
            {
              // Check if conjunct only mentions destination variables
              ExprSet vars;
              filter(cnj, bind::IsConst(), std::inserter(vars, vars.begin()));
              
              bool onlyDstVars = true;
              for (auto& v : vars)
              {
                bool foundInDst = false;
                for (auto& dv : chc.dstVars)
                {
                  if (v == dv)
                  {
                    foundInDst = true;
                    break;
                  }
                }
                if (!foundInDst)
                {
                  onlyDstVars = false;
                  break;
                }
              }
              
              if (onlyDstVars && !vars.empty())
              {
                // Rename to canonical invariant variables
                Expr inv = cnj;
                for (size_t i = 0; i < chc.dstVars.size() && i < workingCHCs->invVars[dcl].size(); i++)
                {
                  inv = replaceAll(inv, chc.dstVars[i], workingCHCs->invVars[dcl][i]);
                }
                
                // Only add comparison constraints (likely invariants)
                if (isOp<ComparissonOp>(inv) || isOpX<EQ>(inv))
                {
                  // Check for duplicates
                  bool isDup = false;
                  for (auto& existing : liaInvariants)
                  {
                    if (inv == existing)
                    {
                      isDup = true;
                      break;
                    }
                  }
                  if (!isDup)
                  {
                    liaInvariants.push_back(inv);
                    if (debug)
                      outs() << "  [Bootstrap] Candidate: " << *inv << "\n";
                  }
                }
              }
            }
          }
          
          // Also extract from transition relations (inductive candidates)
          for (auto& chc : workingCHCs->chcs)
          {
            if (chc.srcRelation != dcl || chc.dstRelation != dcl) continue;
            
            ExprSet cnjs;
            getConj(chc.body, cnjs);
            
            for (auto& cnj : cnjs)
            {
              // Look for equality constraints that relate src to dst
              if (!isOpX<EQ>(cnj)) continue;
              
              Expr lhs = cnj->left();
              Expr rhs = cnj->right();
              
              // Check if this is a "variable unchanged" constraint: v' = v
              for (size_t i = 0; i < chc.srcVars.size() && i < chc.dstVars.size(); i++)
              {
                if ((lhs == chc.dstVars[i] && rhs == chc.srcVars[i]) ||
                    (rhs == chc.dstVars[i] && lhs == chc.srcVars[i]))
                {
                  // This variable is preserved - not useful as invariant seed
                  continue;
                }
                
                // Check for incremental patterns: v' = v + c or v' = v - c
                if (lhs == chc.dstVars[i])
                {
                  if (isOpX<PLUS>(rhs) || isOpX<MINUS>(rhs))
                  {
                    Expr base = rhs->left();
                    Expr delta = rhs->right();
                    if (base == chc.srcVars[i] && isOpX<MPZ>(delta))
                    {
                      // Found incremental variable - extract sign constraint as invariant seed
                      // e.g., if delta > 0, then v grows, so "v >= initial" might be invariant
                      if (debug)
                        outs() << "  [Bootstrap] Incremental: " << *chc.srcVars[i] 
                               << (isOpX<PLUS>(rhs) ? " +=" : " -=") << " " << *delta << "\n";
                    }
                  }
                }
              }
            }
          }
        }
        
        if (liaInvariants.empty())
        {
          if (debug)
            outs() << "  [Bootstrap] No invariant candidates found\n";
          return false;
        }
        
        if (debug)
          outs() << "  [Bootstrap] Found " << liaInvariants.size() << " candidate invariants\n";
        
        // Translate invariants back to BV if needed
        if (needsTranslation)
        {
          if (debug)
            outs() << "  [Bootstrap] Translating " << liaInvariants.size() << " invariants back to BV\n";
          
          Lia2BvTranslator lia2bv(m_efac, ruleManager.m_z3, originalBvWidth, debug ? 1 : 0);
          
          for (auto& inv : liaInvariants)
          {
            Expr bvInv = lia2bv.translateExpr(inv);
            if (bvInv != nullptr)
            {
              outInvariants.push_back(bvInv);
              if (debug)
                outs() << "  [Bootstrap] BV Invariant: " << *bvInv << "\n";
            }
          }
        }
        else
        {
          outInvariants = liaInvariants;
        }
        
        if (debug)
          outs() << "  [Bootstrap] Extracted " << outInvariants.size() << " invariants\n";
        
        return !outInvariants.empty();
      }
      catch (const std::exception& e)
      {
        if (debug)
          outs() << "  [Bootstrap] Error during extraction: " << e.what() << "\n";
        return false;
      }
    }

    /**
     * Write a SyGuS file from a concrete trace.
     * 
     * @param filename       Output filename
     * @param trace          Vector of (variable -> value) maps per step
     * @param state_vars     State variables in order
     * @param step_bitwidth  Bit-width for the step parameter
     * @param seedConstants  Optional set of constants to include in grammar
     * @param mbpGuards      Optional MBP guards for boolean production
     * @param bootstrapInvariants Optional invariants to seed the grammar
     * @return true if successful
     */
    bool writeSyGuSFromTrace(
        const std::string& filename,
        const std::vector<std::map<Expr, Expr>>& trace,
        const ExprVector& state_vars,
        int step_bitwidth,
        const ExprSet& seedConstants = ExprSet(),
        const ExprVector& mbpGuards = ExprVector(),
        const ExprVector& bootstrapInvariants = ExprVector())
    {
      if (trace.empty() || state_vars.empty())
      {
        outs() << "Error: Empty trace or no state variables\n";
        return false;
      }
      
      std::ofstream out(filename);
      if (!out.is_open())
      {
        outs() << "Error: Could not open file " << filename << " for writing\n";
        return false;
      }
      
      // Determine variable bit-widths
      std::map<Expr, unsigned> var_bw;
      for (auto& v : state_vars)
      {
        Expr vtype = bind::typeOf(v);
        if (bv::is_bvsort(vtype))
        {
          var_bw[v] = bv::width(vtype);
        }
        else
        {
          // For non-BV types (Int), compute required bit-width from max value in trace
          mpz_class maxVal = 0;
          for (auto& stepState : trace)
          {
            auto it = stepState.find(v);
            if (it != stepState.end())
            {
              mpz_class val = 0;
              if (bv::is_bvnum(it->second))
              {
                val = bv::toMpz(it->second);
              }
              else if (isOpX<MPZ>(it->second))
              {
                val = lexical_cast<mpz_class>(it->second);
              }
              if (val < 0) val = -val;  // abs value
              if (val > maxVal) maxVal = val;
            }
          }
          
          // Compute bits needed to represent maxVal + 1 for sign bit
          unsigned bits_needed = 8;  // minimum
          while ((mpz_class(1) << bits_needed) <= maxVal && bits_needed < 64)
          {
            bits_needed += 8;
          }
          var_bw[v] = bits_needed;
          
          if (debug)
            outs() << "  Variable " << *v << " max value: " << maxVal << ", using " << bits_needed << " bits\n";
        }
      }
      
      // Collect ESSENTIAL constants only - NOT all trace values!
      // Including all trace constants causes combinatorial explosion in CVC5.
      // We only need: 0, 1, and boundary values (first/last/important state values).
      std::set<mpz_class> traceConstants;
      
      // Always include 0 and 1
      traceConstants.insert(0);
      traceConstants.insert(1);
      
      // Include initial state values (step 0)
      if (!trace.empty())
      {
        for (auto& kv : trace[0])
        {
          if (bv::is_bvnum(kv.second))
          {
            traceConstants.insert(bv::toMpz(kv.second));
          }
          else if (isOpX<MPZ>(kv.second))
          {
            traceConstants.insert(lexical_cast<mpz_class>(kv.second));
          }
        }
      }
      
      // Include final state values (last step)
      if (trace.size() > 1)
      {
        for (auto& kv : trace.back())
        {
          if (bv::is_bvnum(kv.second))
          {
            traceConstants.insert(bv::toMpz(kv.second));
          }
          else if (isOpX<MPZ>(kv.second))
          {
            traceConstants.insert(lexical_cast<mpz_class>(kv.second));
          }
        }
      }
      
      // Include trace length as it's often a key constant
      traceConstants.insert(mpz_class(trace.size()));
      traceConstants.insert(mpz_class(trace.size() - 1));
      
      // Add seed constants (from user or MBP analysis)
      for (auto& c : seedConstants)
      {
        if (bv::is_bvnum(c))
        {
          traceConstants.insert(bv::toMpz(c));
        }
        else if (isOpX<MPZ>(c))
        {
          traceConstants.insert(lexical_cast<mpz_class>(c));
        }
      }
      
      if (debug)
        outs() << "  Grammar constants: " << traceConstants.size() << " (optimized from full trace)\n";
      
      // Header
      out << "; SyGuS file generated from BndExpl concrete trace\n";
      out << "; Trace points: " << trace.size() << "\n";
      out << "; State variables: " << state_vars.size() << "\n";
      out << "\n(set-logic BV)\n\n";
      
      // Generate synth-fun for each state variable
      for (size_t varIdx = 0; varIdx < state_vars.size(); varIdx++)
      {
        Expr v = state_vars[varIdx];
        if (var_bw.find(v) == var_bw.end()) continue;
        
        unsigned vwidth = var_bw[v];
        std::string fun_name = "f" + lexical_cast<string>(v);
        // Clean up function name (remove special chars)
        for (char& c : fun_name)
        {
          if (!isalnum(c) && c != '_') c = '_';
        }
        
        out << "; Function for variable " << *v << "\n";
        out << "(synth-fun " << fun_name << " ((n (_ BitVec " << step_bitwidth << "))) ";
        out << "(_ BitVec " << vwidth << ")\n";
        
        // Grammar
        out << "  ((Start (_ BitVec " << vwidth << ")) (MyBool Bool))\n";
        out << "  ((Start (_ BitVec " << vwidth << ") (\n";
        
        // Step variable (with extraction if needed)
        if ((unsigned)step_bitwidth > vwidth)
        {
          out << "    ((_ extract " << (vwidth - 1) << " 0) n)\n";
        }
        else if ((unsigned)step_bitwidth < vwidth)
        {
          out << "    ((_ zero_extend " << (vwidth - step_bitwidth) << ") n)\n";
        }
        else
        {
          out << "    n\n";
        }
        
        // Constants
        std::set<std::string> seenHex;
        for (auto& c : traceConstants)
        {
          // Convert to hex with proper width
          std::stringstream ss;
          ss << std::hex << std::setfill('0') << std::setw(vwidth / 4);
          mpz_class masked = c & ((mpz_class(1) << vwidth) - 1);
          ss << masked;
          std::string hexStr = ss.str();
          
          if (seenHex.find(hexStr) == seenHex.end())
          {
            out << "    #x" << hexStr << "\n";
            seenHex.insert(hexStr);
          }
        }
        
        // Add constants from bootstrap invariants
        for (auto& inv : bootstrapInvariants)
        {
          ExprVector consts;
          filter(inv, bind::IsConst(), std::inserter(consts, consts.begin()));
          
          for (auto& c : consts)
          {
            if (bv::is_bvnum(c))
            {
              mpz_class val = bv::toMpz(c);
              mpz_class masked = val & ((mpz_class(1) << vwidth) - 1);
              std::stringstream ss;
              ss << std::hex << std::setfill('0') << std::setw(vwidth / 4) << masked;
              std::string hexStr = ss.str();
              if (seenHex.find(hexStr) == seenHex.end())
              {
                out << "    #x" << hexStr << "  ; from invariant\n";
                seenHex.insert(hexStr);
              }
            }
            else if (isOpX<MPZ>(c))
            {
              mpz_class val = lexical_cast<mpz_class>(c);
              mpz_class masked = val & ((mpz_class(1) << vwidth) - 1);
              std::stringstream ss;
              ss << std::hex << std::setfill('0') << std::setw(vwidth / 4) << masked;
              std::string hexStr = ss.str();
              if (seenHex.find(hexStr) == seenHex.end())
              {
                out << "    #x" << hexStr << "  ; from invariant\n";
                seenHex.insert(hexStr);
              }
            }
          }
        }
        
        // BV operations
        out << "    (bvadd Start Start)\n";
        out << "    (bvsub Start Start)\n";
        out << "    (bvmul Start Start)\n";
        out << "    (bvshl Start Start)\n";
        out << "    (bvlshr Start Start)\n";
        // Power-of-2 patterns (useful for exponential growth)
        std::stringstream one_ss;
        one_ss << std::hex << std::setfill('0') << std::setw(vwidth / 4) << 1;
        out << "    (bvshl #x" << one_ss.str() << " Start)\n";  // 1 << Start = 2^Start
        out << "    (ite MyBool Start Start)\n";
        out << "  ))\n";
        
        // Boolean production
        out << "  (MyBool Bool (\n";
        if (!mbpGuards.empty())
        {
          // Use provided MBP guards - convert to SyGuS format
          for (auto& guard : mbpGuards)
          {
            // Convert the guard expression to SyGuS-compatible string
            std::string guardStr = exprToSyGuS(guard, vwidth, step_bitwidth);
            if (!guardStr.empty())
            {
              out << "    " << guardStr << "\n";
            }
          }
          // Add bootstrap invariants as boolean conditions
          for (auto& inv : bootstrapInvariants)
          {
            std::string invStr = exprToSyGuS(inv, vwidth, step_bitwidth);
            if (!invStr.empty())
            {
              out << "    " << invStr << "  ; invariant\n";
            }
          }
          // Also add generic comparisons as fallback
          out << "    (bvult Start Start)\n";
          out << "    (bvuge Start Start)\n";
          out << "    (= Start Start)\n";
        }
        else if (!bootstrapInvariants.empty())
        {
          // Only bootstrap invariants, no MBP
          for (auto& inv : bootstrapInvariants)
          {
            std::string invStr = exprToSyGuS(inv, vwidth, step_bitwidth);
            if (!invStr.empty())
            {
              out << "    " << invStr << "  ; invariant\n";
            }
          }
          // Also add generic comparisons
          out << "    (bvult Start Start)\n";
          out << "    (bvuge Start Start)\n";
          out << "    (= Start Start)\n";
        }
        else
        {
          // Generic boolean comparisons
          out << "    (bvult Start Start)\n";
          out << "    (bvuge Start Start)\n";
          out << "    (= Start Start)\n";
        }
        out << "  ))))\n\n";
      }
      
      // Generate constraints from trace
      out << "; Constraints from concrete trace\n";
      size_t stepIdx = 0;
      for (auto& stepState : trace)
      {
        for (size_t varIdx = 0; varIdx < state_vars.size(); varIdx++)
        {
          Expr v = state_vars[varIdx];
          if (var_bw.find(v) == var_bw.end()) continue;
          
          auto it = stepState.find(v);
          if (it == stepState.end()) continue;
          
          unsigned vwidth = var_bw[v];
          std::string fun_name = "f" + lexical_cast<string>(v);
          for (char& c : fun_name)
          {
            if (!isalnum(c) && c != '_') c = '_';
          }
          
          // Step hex
          std::stringstream step_ss;
          step_ss << std::hex << std::setfill('0') << std::setw(step_bitwidth / 4) << stepIdx;
          
          // Value hex
          std::string val_hex;
          if (bv::is_bvnum(it->second))
          {
            mpz_class valMpz = bv::toMpz(it->second);
            mpz_class masked = valMpz & ((mpz_class(1) << vwidth) - 1);
            std::stringstream val_ss;
            val_ss << std::hex << std::setfill('0') << std::setw(vwidth / 4) << masked;
            val_hex = val_ss.str();
          }
          else if (isOpX<MPZ>(it->second))
          {
            // Integer value - convert to bitvector representation
            mpz_class valMpz = lexical_cast<mpz_class>(it->second);
            mpz_class masked = valMpz & ((mpz_class(1) << vwidth) - 1);
            std::stringstream val_ss;
            val_ss << std::hex << std::setfill('0') << std::setw(vwidth / 4) << masked;
            val_hex = val_ss.str();
          }
          else
          {
            val_hex = std::string(vwidth / 4, '0');
          }
          
          out << "(constraint (= (" << fun_name << " #x" << step_ss.str() << ") #x" << val_hex << "))\n";
        }
        stepIdx++;
      }
      
      out << "\n(check-synth)\n";
      out.close();
      
      if (debug)
        outs() << "  Wrote SyGuS file: " << filename << "\n";
      
      return true;
    }

    void getAllTraces(Expr src, Expr dst, int len, vector<int> trace, vector<vector<int>> &traces)
    {
      if (len == 1)
      {
        for (auto a : ruleManager.outgs[src])
        {
          if (ruleManager.chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        if (already_unsat(trace))
          return;
        for (auto a : ruleManager.outgs[src])
        {
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(ruleManager.chcs[a].dstRelation, dst, len - 1, newtrace, traces);
        }
      }
    }

    Expr compactPrefix(Expr rel, int num, int unr = 0)
    {
      vector<int> pr = ruleManager.prefixes[rel][num];
      if (pr.size() == 0)
        return mk<TRUE>(m_efac);

      for (int j = pr.size() - 1; j >= 0; j--)
      {
        vector<int> &tmp = ruleManager.getCycleForRel(pr[j]);
        for (int i = 0; i < unr; i++)
          pr.insert(pr.begin() + j, tmp.begin(), tmp.end());
      }
      pr.push_back(ruleManager.cycles[rel][num][0]); // we are interested in prefixes, s.t.
                                                     // the cycle is reachable
      ExprVector ssa;
      getSSA(pr, ssa);
      if (!(bool)u.isSat(ssa))
      {
        if (unr > 10)
        {
          do
          {
            ssa.erase(ssa.begin());
          } while (!(bool)u.isSat(ssa));
        }
        else
          return compactPrefix(rel, num, unr + 1);
      }

      if (ssa.empty())
        return mk<TRUE>(m_efac);

      ssa.pop_back();      // remove the cycle from the formula
      bindVars.pop_back(); // and its variables
      Expr pref = conjoin(ssa, m_efac);
      pref = rewriteSelectStore(pref);
      pref = keepQuantifiersRepl(pref, bindVars.back());
      return replaceAll(pref, bindVars.back(), ruleManager.chcs[ruleManager.cycles[rel][num][0]].srcVars);
    }

    Expr toExpr(vector<int> &trace)
    {
      ExprVector ssa;
      getSSA(trace, ssa);
      return conjoin(ssa, m_efac);
    }

    void getSSA(vector<int> &trace, ExprVector &ssa)
    {
      ExprVector bindVars2;
      bindVars.clear();
      ExprVector bindVars1 = ruleManager.chcs[trace[0]].srcVars;
      int64_t bindVar_index = 0;
      int64_t locVar_index = 0;

      for (size_t s = 0; s < trace.size(); s++)
      {
        auto &step = trace[s];
        bindVars2.clear();
        HornRuleExt &hr = ruleManager.chcs[step];
        assert(hr.srcVars.size() == bindVars1.size());

        Expr body = hr.body;
        if (!hr.isFact && extraLemmas != NULL)
          body = mk<AND>(extraLemmas, body);
        body = replaceAll(body, hr.srcVars, bindVars1);

        for (int i = 0; i < hr.dstVars.size(); i++)
        {
          bool kept = false;
          for (int j = 0; j < hr.srcVars.size(); j++)
          {
            if (hr.dstVars[i] == hr.srcVars[j])
            {
              bindVars2.push_back(bindVars1[i]);
              kept = true;
            }
          }
          if (!kept)
          {
            Expr new_name = mkTerm<string>("__bnd_var_" + to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr.dstVars[i], new_name));
          }

          body = replaceAll(body, hr.dstVars[i], bindVars2[i]);
        }

        for (int i = 0; i < hr.locVars.size(); i++)
        {
          Expr new_name = mkTerm<string>("__loc_var_" + to_string(locVar_index++), m_efac);
          Expr var = cloneVar(hr.locVars[i], new_name);

          body = replaceAll(body, hr.locVars[i], var);
        }

        ssa.push_back(body);
        bindVars.push_back(bindVars2);
        bindVars1 = bindVars2;
      }
    }

    tribool exploreTraces(int cur_bnd, int bnd, bool print = false)
    {
      if (ruleManager.chcs.size() == 0)
      {
        if (debug)
          outs() << "CHC system is empty\n";
        if (print)
          outs() << "Success after complete unrolling\n";
        return false;
      }
      if (!ruleManager.hasCycles())
      {
        if (debug)
          outs() << "CHC system does not have cycles\n";
        bnd = ruleManager.chcs.size();
      }
      tribool res = indeterminate;
      while (cur_bnd <= bnd)
      {
        if (debug)
        {
          outs() << ".";
          outs().flush();
        }
        vector<vector<int>> traces;
        getAllTraces(mk<TRUE>(m_efac), ruleManager.failDecl, cur_bnd++, vector<int>(), traces);
        bool toBreak = false;
        for (auto &a : traces)
        {
          ExprVector ssa;
          getSSA(a, ssa);
          int sz;
          res = u.isSatIncrem(ssa, sz);

          if (res || indeterminate(res))
          {
            if (debug)
            {
              outs() << "\ntrue";
              for (auto &b : a)
                outs() << " (" << b << ") -> " << ruleManager.chcs[b].dstRelation;
              outs() << "\n";
            }
            toBreak = true;
            break;
          }
          else
          {
            a.resize(sz);
            unsat_prefs.insert(a);
          }
        }
        if (toBreak)
          break;
      }

      if (debug || print)
      {
        if (indeterminate(res))
          outs() << "unknown\n";
        else if (res)
          outs() << "Counterexample of length " << (cur_bnd - 1) << " found\n";
        else if (ruleManager.hasCycles())
          outs() << "No counterexample found up to length " << cur_bnd << "\n";
        else
          outs() << "Success after complete unrolling\n";
      }
      return res;
    }

    bool kIndIter(int bnd1, int bnd2)
    {
      assert(bnd1 <= bnd2);
      assert(bnd2 > 1);
      if (!exploreTraces(bnd1, bnd2))
      {
        outs() << "Base check failed at step " << bnd2 << "\n";
        exit(0);
      }

      k_ind = ruleManager.chcs.size(); // == 3

      for (int i = 0; i < k_ind; i++)
      {
        auto &r = ruleManager.chcs[i];
        if (r.isInductive)
          tr_ind = i;
        if (r.isQuery)
          pr_ind = i;
      }

      ruleManager.chcs.push_back(HornRuleExt()); // trick for now: a new artificial CHC
      HornRuleExt &hr = ruleManager.chcs[k_ind];
      HornRuleExt &tr = ruleManager.chcs[tr_ind];
      HornRuleExt &pr = ruleManager.chcs[pr_ind];

      hr.srcVars = tr.srcVars;
      hr.dstVars = tr.dstVars;
      hr.locVars = tr.locVars;

      hr.body = mk<AND>(tr.body, mkNeg(pr.body));

      if (extraLemmas != NULL)
        hr.body = mk<AND>(extraLemmas, hr.body);

      for (int i = 0; i < hr.srcVars.size(); i++)
      {
        hr.body = replaceAll(hr.body, pr.srcVars[i], hr.srcVars[i]);
      }

      vector<int> gen_trace;
      for (int i = 1; i < bnd2; i++)
        gen_trace.push_back(k_ind);
      gen_trace.push_back(pr_ind);
      Expr q = toExpr(gen_trace);
      bool res = bool(!u.isSat(q));

      if (bnd2 == 2)
        inv = mkNeg(pr.body);

      // prepare for the next iteration
      ruleManager.chcs.erase(ruleManager.chcs.begin() + k_ind);

      return res;
    }

    Expr getInv() { return inv; }

    Expr getBoundedItp(int k)
    {
      assert(k >= 0);

      int fc_ind;
      for (int i = 0; i < ruleManager.chcs.size(); i++)
      {
        auto &r = ruleManager.chcs[i];
        if (r.isInductive)
          tr_ind = i;
        if (r.isQuery)
          pr_ind = i;
        if (r.isFact)
          fc_ind = i;
      }

      HornRuleExt &fc = ruleManager.chcs[fc_ind];
      HornRuleExt &tr = ruleManager.chcs[tr_ind];
      HornRuleExt &pr = ruleManager.chcs[pr_ind];

      Expr prop = pr.body;
      Expr init = fc.body;
      for (int i = 0; i < tr.srcVars.size(); i++)
      {
        init = replaceAll(init, tr.dstVars[i], tr.srcVars[i]);
      }

      Expr itp;

      if (k == 0)
      {
        itp = getItp(init, prop);
      }
      else
      {
        vector<int> trace;
        for (int i = 0; i < k; i++)
          trace.push_back(tr_ind);

        Expr unr = toExpr(trace);
        for (int i = 0; i < pr.srcVars.size(); i++)
        {
          prop = replaceAll(prop, pr.srcVars[i], bindVars.back()[i]);
        }
        itp = getItp(unr, prop);
        if (itp != NULL)
        {
          for (int i = 0; i < pr.srcVars.size(); i++)
          {
            itp = replaceAll(itp, bindVars.back()[i], pr.srcVars[i]);
          }
        }
        else
        {
          itp = getItp(init, mk<AND>(unr, prop));
        }
      }
      return itp;
    }

    void fillVars(Expr srcRel, ExprVector &srcVars, ExprVector &vars, int l, int s, vector<int> &mainInds, vector<ExprVector> &versVars, ExprSet &allVars)
    {
      for (int l1 = l; l1 < bindVars.size(); l1 = l1 + s)
      {
        ExprVector vers;
        int ai = 0;

        for (int i = 0; i < vars.size(); i++)
        {
          int var = mainInds[i];
          Expr bvar;
          if (var >= 0)
          {
            if (ruleManager.hasArrays[srcRel])
              bvar = bindVars[l1 - 1][var];
            else
              bvar = bindVars[l1][var];
          }
          else
          {
            bvar = replaceAll(vars[i], srcVars, bindVars[l1 - 1]);
            bvar = replaceAll(bvar, bindVars[l1 - 1][-var - 1], bindVars[l1][-var - 1]);
            allVars.insert(bindVars[l1][-var - 1]);
            ai++;
          }
          vers.push_back(bvar);
        }
        versVars.push_back(vers);
        allVars.insert(vers.begin(), vers.end());
      }
    }

    void getOptimConstr(vector<ExprVector> &versVars, int vs, ExprVector &srcVars,
                        ExprSet &constr, Expr phaseGuard, ExprVector &diseqs)
    {
      for (auto v : versVars)
        for (int i = 0; i < v.size(); i++)
          for (int j = i + 1; j < v.size(); j++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(v[i], v[j]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));

      for (int i = 0; i < vs; i++)
        for (int j = 0; j < versVars.size(); j++)
          for (int k = j + 1; k < versVars.size(); k++)
            diseqs.push_back(mk<ITE>(mk<NEQ>(versVars[j][i], versVars[k][i]), mkMPZ(1, m_efac), mkMPZ(0, m_efac)));

      Expr extr = disjoin(constr, m_efac);
      if (debug)
        outs() << "Adding extra constraints to every iteration: " << extr << "\n";
      for (auto &bv : bindVars)
      {
        diseqs.push_back(mk<ITE>(replaceAll(extr, srcVars, bv), mkMPZ(0, m_efac), mkMPZ(1, m_efac)));
      }
      if (phaseGuard != NULL)
        for (auto &bv : bindVars)
          diseqs.push_back(mk<ITE>(replaceAll(phaseGuard, srcVars, bv), mkMPZ(0, m_efac), mkMPZ(1, m_efac)));
    }

    Expr findSelect(int t, int i)
    {
      Expr tr = ruleManager.chcs[t].body;
      ExprVector &srcVars = ruleManager.chcs[t].srcVars;
      ExprVector st;
      filter(tr, IsStore(), inserter(st, st.begin()));
      for (auto &s : st)
      {
        if (!contains(s->left(), srcVars[i]))
          continue;
        if (!isOpX<INT_TY>(typeOf(s)->last()))
          continue;
        if (!hasOnlyVars(s, srcVars))
          continue;
        return mk<SELECT>(s->left(), s->right());
      }
      st.clear();
      filter(tr, IsSelect(), inserter(st, st.begin()));
      for (auto &s : st)
      {
        if (!contains(s->left(), srcVars[i]))
          continue;
        if (!isOpX<INT_TY>(typeOf(s->left())->last()))
          continue;
        if (!hasOnlyVars(s, srcVars))
          continue;
        return s;
      }
      return NULL;
    }

    // used for a loop and a phaseGuard
    bool unrollAndExecuteSplitter(
        Expr srcRel,
        ExprVector &invVars,
        vector<vector<double>> &models,
        Expr phaseGuard, Expr invs, bool fwd, ExprSet &constr, int k = 10)
    {
      assert(phaseGuard != NULL);

      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      for (auto &c : ruleManager.cycles)
      {
        Expr invRel = c.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;
          if (srcRel != ruleManager.chcs[loop[0]].srcRelation)
            continue;
          if (models.size() > 0)
            continue;

          ExprVector vars, varsMask;
          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr t = typeOf(srcVars[i]);
            if (isOpX<INT_TY>(t))
            {
              mainInds.push_back(i);
              vars.push_back(srcVars[i]);
              varsMask.push_back(srcVars[i]);
            }
            else if (isOpX<ARRAY_TY>(t) && ruleManager.hasArrays[srcRel])
            {
              Expr v = findSelect(loop[0], i);
              if (v != NULL)
              {
                vars.push_back(v);
                mainInds.push_back(-i - 1); // to be on the negative side
                varsMask.push_back(srcVars[i]);
              }
            }
          }

          if (vars.size() < 2 && cyc == ruleManager.cycles[invRel].size() - 1)
            continue; // does not make much sense to run with only one var when it is the last cycle
          invVars = vars;

          auto &prefix = ruleManager.prefixes[invRel][cyc];
          vector<int> trace;
          int l = 0; // starting index (before the loop)
          if (ruleManager.hasArrays[srcRel])
            l++; // first iter is usually useless

          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          ExprVector ssa;
          getSSA(trace, ssa);
          if (fwd)
          {
            ssa.push_back(invs);
            ssa.push_back(replaceAll(phaseGuard, srcVars, bindVars[loop.size() - 1]));
          }
          else
          {
            ssa.push_back(phaseGuard);
            ssa.push_back(replaceAll(invs, srcVars, bindVars[loop.size() - 1]));
          }
          bindVars.pop_back();

          if(debug)
          {
            outs() << "SSA: \n";
            for (auto &s : ssa)
              outs() << *s << " /\\ ";
            outs() << "\n";
          }

          // compute vars for opt constraint
          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, vars, l, loop.size(), mainInds, versVars, allVars);
          getOptimConstr(versVars, vars.size(), srcVars, constr, phaseGuard, diseqs);

          Expr cntvar = bind::intConst(mkTerm<string>("_FH_cnt", m_efac));
          allVars.insert(cntvar);
          allVars.insert(bindVars.back().begin(), bindVars.back().end());
          ssa.push_back(mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

          auto res = u.isSat(ssa);
          if (indeterminate(res) || !res)
          {
            if (debug)
              outs() << "Unable to solve the BMC formula for " << srcRel << " and phase guard " << phaseGuard << "\n";
            continue;
          }
          ExprMap allModels;
          u.getOptModel<GT>(allVars, allModels, cntvar);

          ExprSet phaseGuardVars;
          set<int> phaseGuardVarsIndex; // Get phaseGuard vars here
          filter(phaseGuard, bind::IsConst(), inserter(phaseGuardVars, phaseGuardVars.begin()));
          for (auto &a : phaseGuardVars)
          {
            int i = getVarIndex(a, varsMask);
            assert(i >= 0);
            phaseGuardVarsIndex.insert(i);
          }

          if (debug)
            outs() << "\nUnroll and execute the cycle for " << srcRel << " and phase guard " << phaseGuard << "\n";

          for (int j = 0; j < versVars.size(); j++)
          {
            vector<double> model;
            if (debug)
              outs() << "  model for " << j << ": [";
            bool toSkip = false;
            SMTUtils u2(m_efac);
            ExprSet equalities;

            for (auto i : phaseGuardVarsIndex)
            {
              Expr srcVar = varsMask[i];
              Expr bvar = versVars[j][i];
              if (isOpX<SELECT>(bvar))
                bvar = bvar->left();
              Expr m = allModels[bvar];
              if (m == NULL)
              {
                toSkip = true;
                break;
              }
              equalities.insert(mk<EQ>(srcVar, m));
            }
            if (toSkip)
              continue;
            equalities.insert(phaseGuard);

            if (u2.isSat(equalities)) // exclude models that don't satisfy phaseGuard
            {
              vector<double> model;

              for (int i = 0; i < vars.size(); i++)
              {
                Expr bvar = versVars[j][i];
                Expr m = allModels[bvar];
                double value;
                if (m != NULL && isOpX<MPZ>(m))
                {
                  if (lexical_cast<cpp_int>(m) > max_double ||
                      lexical_cast<cpp_int>(m) < -max_double)
                  {
                    toSkip = true;
                    break;
                  }
                  value = lexical_cast<double>(m);
                }
                else
                {
                  toSkip = true;
                  break;
                }
                model.push_back(value);
                if (debug)
                  outs() << *bvar << " = " << *m << ", ";
                if (j == 0)
                {
                  Expr arr = bvar;
                  while (isOpX<SELECT>(arr) || isOpX<STORE>(arr))
                    arr = arr->left();
                  if (arr != bvar)
                    concrInvs[srcRel].insert(mk<EQ>(vars[i]->left(), allModels[arr]));
                  else
                    concrInvs[srcRel].insert(mk<EQ>(vars[i], m));
                }
              }
              if (!toSkip)
                models.push_back(model);
            }
            else
            {
              if (debug)
                outs() << "   <  skipping  >      ";
            }
            if (debug)
              outs() << "\b\b]\n";
          }
        }
      }

      return true;
    }

    bool unrollAndExecuteSplitterBv(
        Bv2LiaTranslator &translator,
        Expr srcRel,
        ExprVector &liaInvVars,
        ExprVector &bvInvVars,
        vector<vector<double>> &models,
        Expr phaseGuard,
        Expr invs,
        bool fwd,
        ExprSet &constr,
        const ExprVector &mbpGuides,
        int k = 10)
    {
      assert(phaseGuard != NULL);

      if (debug >= 2)
      {
        outs() << "\n--- unrollAndExecuteSplitterBv ---\n";
        outs() << "  srcRel: " << *srcRel << "\n";
        outs() << "  phaseGuard: " << *phaseGuard << "\n";
        outs() << "  invs: ";
        if (invs) outs() << *invs; else outs() << "NULL";
        outs() << "\n";
        outs() << "  fwd: " << fwd << "\n";
        outs() << "  mbpGuides:\n";
        for (auto &g : mbpGuides)
          outs() << "    " << *g << "\n";
      }

      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      bool res = false;

      for (auto &cycleEntry : ruleManager.cycles)
      {
        Expr invRel = cycleEntry.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;
          if (srcRel != ruleManager.chcs[loop[0]].srcRelation)
            continue;
          if (models.size() > 0)
            continue;

          ExprVector varsMask;
          ExprVector bvVarsLocal;
          ExprVector liaVarsLocal;

          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr ty = typeOf(srcVars[i]);

            if (isOpX<INT_TY>(ty))
            {
              mainInds.push_back(i);
              bvVarsLocal.push_back(srcVars[i]);
              liaVarsLocal.push_back(srcVars[i]);
              varsMask.push_back(srcVars[i]);
              continue;
            }

            if (isOpX<ARRAY_TY>(ty) && ruleManager.hasArrays[srcRel])
            {
              Expr selectExpr = findSelect(loop[0], i);
              if (selectExpr != NULL)
              {
                Expr liaSelect = translator.translateExpr(selectExpr);
                if (liaSelect != NULL)
                {
                  bvVarsLocal.push_back(selectExpr);
                  liaVarsLocal.push_back(liaSelect);
                  mainInds.push_back(-i - 1);
                  varsMask.push_back(srcVars[i]);
                }
              }
              continue;
            }

            if (isOpX<BVSORT>(ty))
            {
              Expr liaVar = translator.translateExpr(srcVars[i]);
              if (liaVar != NULL)
              {
                mainInds.push_back(i);
                bvVarsLocal.push_back(srcVars[i]);
                liaVarsLocal.push_back(liaVar);
                varsMask.push_back(srcVars[i]);
              }
            }
          }

          if (bvVarsLocal.empty())
            continue;

          bvInvVars = bvVarsLocal;
          liaInvVars = liaVarsLocal;

          vector<int> trace;
          int l = 0;
          if (ruleManager.hasArrays[srcRel])
            l++;

          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          ExprVector ssa;
          getSSA(trace, ssa);
          ExprVector guideInstances;
          if (!mbpGuides.empty() && !bindVars.empty())
          {
            size_t limit = std::min(mbpGuides.size(), bindVars.size());
            for (size_t idx = 0; idx < limit; idx++)
            {
              Expr inst = replaceAll(mbpGuides[idx], srcVars, bindVars[idx]);
              if (inst != NULL && !isOpX<TRUE>(inst) && mbpGuides[idx] != phaseGuard)
              {
                if (debug)
                  outs() << "Applying MBP guide (prefix " << idx << "): " << *mbpGuides[idx] << "\n";
                guideInstances.push_back(inst);
              }
            }
            for (size_t idx = limit; idx < mbpGuides.size(); idx++)
            {
              Expr inst = replaceAll(mbpGuides[idx], srcVars, bindVars.back());
              if (inst != NULL && !isOpX<TRUE>(inst) && mbpGuides[idx] != phaseGuard)
              {
                if (debug)
                  outs() << "Applying MBP guide (tail " << idx << "): " << *mbpGuides[idx] << "\n";
                guideInstances.push_back(inst);
              }
            }
          }

          Expr phaseGuardInst = fwd ? replaceAll(phaseGuard, srcVars, bindVars[loop.size() - 1])
                                    : phaseGuard;
          Expr invsInst = NULL;
          if (invs != NULL)
          {
            invsInst = fwd ? invs
                           : replaceAll(invs, srcVars, bindVars[loop.size() - 1]);
          }

          if (fwd)
          {
            if (invsInst != NULL)
              ssa.push_back(invsInst);
            ssa.push_back(phaseGuardInst);
          }
          else
          {
            ssa.push_back(phaseGuardInst);
            if (invsInst != NULL)
              ssa.push_back(invsInst);
          }

          ssa.insert(ssa.end(), guideInstances.begin(), guideInstances.end());

          if (debug)
          {
            outs() << "SSA:\n";
            for (auto &s : ssa)
              outs() << "  " << *s << "\n";
            outs() << "\n";
          }

          bindVars.pop_back();

          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, bvVarsLocal, l, loop.size(), mainInds, versVars, allVars);
          getOptimConstr(versVars, bvVarsLocal.size(), srcVars, constr, phaseGuard, diseqs);

          Expr cntvar = bind::intConst(mkTerm<string>("_FH_cnt", m_efac));
          allVars.insert(cntvar);
          allVars.insert(bindVars.back().begin(), bindVars.back().end());
          ssa.push_back(mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

          auto resSat = u.isSat(ssa);
          if (indeterminate(resSat) || !resSat)
          {
            if (debug)
              outs() << "Unable to solve the BV splitter formula for " << srcRel << " and phase guard " << phaseGuard << "\n";
            continue;
          }

          res = true;

          ExprMap allModels;
          u.getOptModel<GT>(allVars, allModels, cntvar);

          ExprSet phaseGuardVars;
          set<int> phaseGuardVarsIndex;
          filter(phaseGuard, bind::IsConst(), inserter(phaseGuardVars, phaseGuardVars.begin()));
          for (auto &a : phaseGuardVars)
          {
            int idx = getVarIndex(a, varsMask);
            assert(idx >= 0);
            phaseGuardVarsIndex.insert(idx);
          }

          if (debug)
            outs() << "\nUnroll and execute the BV splitter for " << srcRel << "\n";

          map<int, ExprSet> ms;

          for (int j = 0; j < versVars.size(); j++)
          {
            vector<double> model;
            bool toSkip = false;
            if (debug)
              outs() << "  model for " << j << ": [";

            SMTUtils u2(m_efac);
            ExprSet equalities;

            for (auto idx : phaseGuardVarsIndex)
            {
              Expr srcVar = varsMask[idx];
              Expr bvar = versVars[j][idx];
              if (isOpX<SELECT>(bvar))
                bvar = bvar->left();
              Expr m = allModels[bvar];
              if (m == NULL)
              {
                toSkip = true;
                break;
              }
              equalities.insert(mk<EQ>(srcVar, m));
            }

            if (toSkip)
              continue;

            equalities.insert(phaseGuard);

            if (!u2.isSat(equalities))
            {
              if (debug)
                outs() << "   <  skipping  >      ";
              continue;
            }

            for (int i = 0; i < bvVarsLocal.size(); i++)
            {
              Expr bvar = versVars[j][i];
              Expr value = allModels[bvar];
              double numericValue = 0.0;
              Expr exactExpr = toIntegerExpr(value, numericValue, max_double);
              if (exactExpr == NULL)
              {
                toSkip = true;
                break;
              }

              model.push_back(numericValue);
              if (debug)
                outs() << *bvar << " = " << *exactExpr << ", ";
              if (!containsOp<ARRAY_TY>(bvar) && i < liaVarsLocal.size())
                ms[i].insert(mk<EQ>(liaVarsLocal[i], exactExpr));
            }

            if (toSkip)
            {
              if (debug)
                outs() << "\b\b   <  skipping  >      ]\n";
              continue;
            }

            models.push_back(model);

            if (debug)
              outs() << "\b\b]\n";
          }

          for (auto &entry : ms)
            if (!entry.second.empty())
              concrInvs[srcRel].insert(simplifyArithm(disjoin(entry.second, m_efac)));
        }
      }

      if (debug >= 2)
        outs() << "  Total models collected: " << models.size() << "\n";

      return res;
    }

    bool unrollAndExecuteGhost(
        Expr src, Expr dst,
        Expr srcRel,
        ExprVector &invVars,
        vector<vector<double>> &models,
        Expr phaseGuard, Expr invs, bool fwd, ExprSet &constr, int k = 3)
    {
      assert(phaseGuard != NULL);

      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      for (auto &c : ruleManager.cycles)
      {
        Expr invRel = c.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;
          if (srcRel != ruleManager.chcs[loop[0]].srcRelation)
            continue;
          if (models.size() > 0)
            continue;

          ExprVector vars, varsMask;
          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr t = typeOf(srcVars[i]);
            if (isOpX<INT_TY>(t))
            {
              mainInds.push_back(i);
              vars.push_back(srcVars[i]);
              varsMask.push_back(srcVars[i]);
            }
            else if (isOpX<ARRAY_TY>(t) && ruleManager.hasArrays[srcRel])
            {
              Expr v = findSelect(loop[0], i);
              if (v != NULL)
              {
                vars.push_back(v);
                mainInds.push_back(-i - 1); // to be on the negative side
                varsMask.push_back(srcVars[i]);
              }
            }
          }

          if (vars.size() < 2 && cyc == ruleManager.cycles[invRel].size() - 1)
            continue; // does not make much sense to run with only one var when it is the last cycle
          invVars = vars;

          auto &prefix = ruleManager.prefixes[invRel][cyc];
          vector<int> trace;
          int l = 0; // starting index (before the loop)
          if (ruleManager.hasArrays[srcRel])
            l++; // first iter is usually useless

          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          ExprVector ssa;
          getSSA(trace, ssa);
          if (fwd)
          {
            ssa.push_back(src);
            ssa.push_back(invs);
            ssa.push_back(replaceAll(phaseGuard, srcVars, bindVars[loop.size() - 1]));
            ssa.push_back(replaceAll(dst, srcVars, bindVars[bindVars.size() - 1]));
          }
          else
          {
            ssa.push_back(src);
            ssa.push_back(phaseGuard);
            ssa.push_back(replaceAll(invs, srcVars, bindVars[loop.size() - 1]));
            ssa.push_back(replaceAll(dst, srcVars, bindVars[bindVars.size() - 1]));
          }
          bindVars.pop_back();

          // compute vars for opt constraint
          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, vars, l, loop.size(), mainInds, versVars, allVars);
          getOptimConstr(versVars, vars.size(), srcVars, constr, phaseGuard, diseqs);

          Expr cntvar = bind::intConst(mkTerm<string>("_FH_cnt", m_efac));
          allVars.insert(cntvar);
          allVars.insert(bindVars.back().begin(), bindVars.back().end());
          ssa.push_back(mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

          auto res = u.isSat(ssa);
          if (indeterminate(res) || !res)
          {
            if (debug)
              outs() << "Unable to solve the BMC formula for " << srcRel << " and phase guard " << phaseGuard << "\n";
            continue;
          }
          ExprMap allModels;
          u.getOptModel<GT>(allVars, allModels, cntvar);

          ExprSet phaseGuardVars;
          set<int> phaseGuardVarsIndex; // Get phaseGuard vars here
          filter(phaseGuard, bind::IsConst(), inserter(phaseGuardVars, phaseGuardVars.begin()));
          for (auto &a : phaseGuardVars)
          {
            int i = getVarIndex(a, varsMask);
            assert(i >= 0);
            phaseGuardVarsIndex.insert(i);
          }

          if (debug)
            outs() << "\nUnroll and execute the cycle for " << srcRel << " and phase guard " << phaseGuard << "\n";

          for (int j = 0; j < versVars.size(); j++)
          {
            vector<double> model;
            if (debug)
              outs() << "  model for " << j << ": [";
            bool toSkip = false;
            SMTUtils u2(m_efac);
            ExprSet equalities;

            for (auto i : phaseGuardVarsIndex)
            {
              Expr srcVar = varsMask[i];
              Expr bvar = versVars[j][i];
              if (isOpX<SELECT>(bvar))
                bvar = bvar->left();
              Expr m = allModels[bvar];
              if (m == NULL)
              {
                toSkip = true;
                break;
              }
              equalities.insert(mk<EQ>(srcVar, m));
            }
            if (toSkip)
              continue;
            equalities.insert(phaseGuard);

            if (u2.isSat(equalities)) // exclude models that don't satisfy phaseGuard
            {
              vector<double> model;

              for (int i = 0; i < vars.size(); i++)
              {
                Expr bvar = versVars[j][i];
                Expr m = allModels[bvar];
                double value;
                if (m != NULL && isOpX<MPZ>(m))
                {
                  if (lexical_cast<cpp_int>(m) > max_double ||
                      lexical_cast<cpp_int>(m) < -max_double)
                  {
                    toSkip = true;
                    break;
                  }
                  value = lexical_cast<double>(m);
                }
                else
                {
                  toSkip = true;
                  break;
                }
                model.push_back(value);
                if (debug)
                  outs() << *bvar << " = " << *m << ", ";
                if (j == 0)
                {
                  Expr arr = bvar;
                  while (isOpX<SELECT>(arr) || isOpX<STORE>(arr))
                    arr = arr->left();
                  if (arr != bvar)
                    concrInvs[srcRel].insert(mk<EQ>(vars[i]->left(), allModels[arr]));
                  else
                    concrInvs[srcRel].insert(mk<EQ>(vars[i], m));
                }
              }
              if (!toSkip)
                models.push_back(model);
            }
            else
            {
              if (debug)
                outs() << "   <  skipping  >      ";
            }
            if (debug)
              outs() << "\b\b]\n";
          }
        }
      }

      return true;
    }

    boost::tribool unrollAndExecuteTermPhase(
        Expr src, Expr dst,
        Expr srcRel,
        ExprVector &dtVars,
        vector<vector<double>> &models,
        Expr gh_cond, // Expr invs, Expr preCond,
        int k = 3)
    {
      assert(gh_cond != NULL);

      gh_cond = simplifyArithm(gh_cond);
      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      for (auto &c : ruleManager.cycles)
      {
        Expr invRel = c.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          vector<int> arrInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          if (srcRel != ruleManager.chcs[loop[0]].srcRelation)
          {
            if (debug)
              outs() << "continuing\n";
            continue;
          }
          if (models.size() > 0)
          {
            if (debug)
              outs() << "continuing\n";
            continue;
          }
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;

          ExprVector vars;
          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr var = srcVars[i];
            if (bind::isIntConst(var))
            {
              mainInds.push_back(i);
              vars.push_back(var);
            }
            else if (isConst<ARRAY_TY>(var) && ruleManager.hasAnyArrays)
            {
              /*
              Expr v = findSelect(loop[0], i);
              if (v != NULL)
              {
                vars.push_back(v);
                mainInds.push_back(-i - 1);  // to be on the negative side
                //              varsMask.push_back(srcVars[i]);
              }*/
            }
          }
          if (vars.size() < 2 && cyc == ruleManager.cycles[invRel].size() - 1)
          {
            if (debug)
            {
              outs() << "continuing because of vars size\n";
              outs() << "Vars size: " << vars.size() << "\n";
            }
            continue; // does not make much sense to run with only one var when it is the last cycle
          }
          dtVars = vars;

          auto &prefix = ruleManager.prefixes[invRel][cyc];
          vector<int> trace;
          int l = 0; // starting index (before the loop)
          if (ruleManager.hasAnyArrays)
            l++; // first iter is usually useless

          // if(isOpX<TRUE>(gh_cond)) trace.push_back(0);
          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          ExprVector ssa;
          ssa.push_back(src);
          ssa.push_back(gh_cond);
          getSSA(trace, ssa);
          // for(int i = 0; i < bindVars.size() ; i++)
          // {
          //   ssa.push_back(replaceAll(gh_cond, srcVars, bindVars[i]));
          // }
          ssa.push_back(replaceAll(dst, srcVars, bindVars[bindVars.size() - 1]));
          if (debug)
          {
            outs() << "SSA BND: ";
            pprint(ssa, 2);
          }

          int traceSz = trace.size();
          // compute vars for opt constraint
          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, vars, l, loop.size(), mainInds, versVars, allVars);
          bool toContinue = false;
          bool noopt = true;

          if (!u.isSat(ssa))
          {
            if (debug)
            {
              outs() << "  BMC formula unsat\n";
              // pprint(ssa,2);
            }
            return false;
          }

          ExprMap allModels;
          u.getModel(allVars, allModels);
          // pprint(u.getModel());
          vector<double> _model;
          for (int d = 0; d < srcVars.size(); d++)
          {

            _model.push_back(lexical_cast<double>(u.getModel(srcVars[d])));
            // outs() << "Model value: " << srcVars[d] << " = " << _model.back() << "\n";
          }
          models.push_back(_model);

          ExprSet gh_condVars;
          set<int> gh_condVarsIndex; // Get gh_cond vars here
          filter(gh_cond, bind::IsConst(), inserter(gh_condVars, gh_condVars.begin()));
          for (auto &a : gh_condVars)
            gh_condVarsIndex.insert(getVarIndex(a, srcVars));

          if (debug)
            outs() << "\n  Unroll and execute the cycle for " << srcRel
                   << " and TERM " << gh_cond << "\n  - - - - - \n";
          for (int j = 0; j < versVars.size(); j++)
          {
            if (j >= trace.size())
              break;
            if (debug)
              outs() << "     MODEL for " << j + 1 << ":\t[";
            bool toSkip = false;
            vector<double> model;
            for (int i = 0; i < vars.size(); i++)
            {
              Expr bvar = versVars[j][i];
              Expr m = allModels[bvar];
              double value;
              if (m != NULL && isOpX<MPZ>(m))
              {
                if (lexical_cast<cpp_int>(m) > max_double ||
                    lexical_cast<cpp_int>(m) < -max_double)
                {
                  toSkip = true;
                  break;
                }
                value = lexical_cast<double>(m);
              }
              else
              {
                value = 132; // hack just to produce "some" matrix (could have any constant here)
                // toSkip = true;
                // break;
              }
              model.push_back(value);
              if (debug)
                outs() << *bvar << " = " << (int)value << ", ";
            }
            if (!toSkip)
              models.push_back(model);
            if (debug)
              outs() << "\b\b]\n";
          }
          if (debug)
            outs() << "  - - - - - \n\n";
        }
      }

      if (models.size() > 0)
        return true;
      return false;
    }

    // used for multiple loops to unroll inductive clauses k times and collect corresponding models
    bool unrollAndExecuteMultipleBv(
        Bv2LiaTranslator &translator,
        map<Expr, ExprVector> &liaInvVars,
        map<Expr, vector<vector<double>>> &models,
        map<Expr, ExprVector> &arrRanges,
        map<Expr, ExprSet> &constr,
        map<Expr, ExprVector> &bvInvVars,
        int k = 10)
    {
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      map<int, bool> chcsConsidered;
      map<int, Expr> exprModels;
      bool res = false;

      for (auto &cycleEntry : ruleManager.cycles)
      {
        Expr invRel = cycleEntry.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          Expr srcRel = invRel;
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;

          if (models[srcRel].size() > 0)
            continue;

          ExprVector bvVars;
          ExprVector liaVarsLocal;
          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr ty = typeOf(srcVars[i]);

            if (isOpX<ARRAY_TY>(ty) && ruleManager.hasArrays[srcRel])
            {
              Expr selectExpr = findSelect(loop[0], i);
              if (selectExpr != NULL)
              {
                Expr liaSelect = translator.translateExpr(selectExpr);
                if (liaSelect != NULL)
                {
                  bvVars.push_back(selectExpr);
                  liaVarsLocal.push_back(liaSelect);
                  mainInds.push_back(-i - 1);
                }
              }
              continue;
            }

            if (isOpX<INT_TY>(ty))
            {
              bvVars.push_back(srcVars[i]);
              liaVarsLocal.push_back(srcVars[i]);
              mainInds.push_back(i);
              continue;
            }

            if (isOpX<BVSORT>(ty))
            {
              Expr liaVar = translator.translateExpr(srcVars[i]);
              if (liaVar != NULL)
              {
                bvVars.push_back(srcVars[i]);
                liaVarsLocal.push_back(liaVar);
                mainInds.push_back(i);
              }
            }
          }

          if (bvVars.empty())
            continue;

          liaInvVars[srcRel] = liaVarsLocal;
          bvInvVars[srcRel] = bvVars;

          auto &prefix = ruleManager.prefixes[invRel][cyc];
          vector<int> trace;
          Expr lastModel = mk<TRUE>(m_efac);

          for (int p = 0; p < prefix.size(); p++)
          {
            if (chcsConsidered[prefix[p]])
            {
              Expr lastModelTmp = exprModels[prefix[p]];
              if (lastModelTmp != NULL)
                lastModel = lastModelTmp;
              trace.clear();
            }
            trace.push_back(prefix[p]);
          }

          int l = trace.size() - 1;
          if (ruleManager.hasArrays[srcRel])
            l++;

          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          int backCHC = -1;
          for (int i = 0; i < ruleManager.chcs.size(); i++)
          {
            auto &r = ruleManager.chcs[i];
            if (i != loop[0] && !r.isQuery && r.srcRelation == srcRel)
            {
              backCHC = i;
              chcsConsidered[i] = true;
              trace.push_back(i);
              break;
            }
          }

          ExprVector ssa;
          getSSA(trace, ssa);
          bindVars.pop_back();
          int traceSz = trace.size();
          assert(bindVars.size() == traceSz - 1);

          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, bvVars, l, loop.size(), mainInds, versVars, allVars);
          getOptimConstr(versVars, bvVars.size(), srcVars, constr[srcRel], NULL, diseqs);

          Expr cntvar = bind::intConst(mkTerm<string>("_FH_cnt", m_efac));
          allVars.insert(cntvar);
          allVars.insert(bindVars.back().begin(), bindVars.back().end());
          ssa.insert(ssa.begin(), mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

          for (auto &rangeExpr : arrRanges[srcRel])
            ssa.insert(ssa.begin(), replaceAll(mk<GT>(rangeExpr, mkMPZ(k, m_efac)), srcVars, bindVars[0]));

          bool toContinue = false;
          bool noopt = false;
          while (true)
          {
            if (bindVars.size() <= 1)
            {
              if (debug)
                outs() << "Unable to find a suitable BV unrolling for " << *srcRel << "\n";
              toContinue = true;
              break;
            }

            if (u.isSat(lastModel, conjoin(ssa, m_efac)))
            {
              if (backCHC != -1 && trace.back() != backCHC && trace.size() != traceSz - 1)
              {
                trace.push_back(backCHC);
                ssa.clear();
                getSSA(trace, ssa);
                bindVars.pop_back();
                noopt = true;
              }
              else
                break;
            }
            else
            {
              noopt = true;
              if (trace.size() == traceSz)
              {
                trace.pop_back();
                ssa.pop_back();
                bindVars.pop_back();
              }
              else
              {
                trace.resize(trace.size() - loop.size());
                ssa.resize(ssa.size() - loop.size());
                bindVars.resize(bindVars.size() - loop.size());
              }
            }
          }

          if (toContinue)
            continue;

          res = true;
          map<int, ExprSet> ms;

          ExprMap allModels;
          if (noopt)
            u.getModel(allVars, allModels);
          else
            u.getOptModel<GT>(allVars, allModels, cntvar);

          if (debug)
            outs() << "\nUnroll and execute the BV cycle for " << srcRel << "\n";
          for (int j = 0; j < versVars.size(); j++)
          {
            vector<double> model;
            bool toSkip = false;
            if (debug)
              outs() << "  model for " << j << ": [";

            for (int i = 0; i < bvVars.size(); i++)
            {
              Expr bvar = versVars[j][i];
              Expr value = allModels[bvar];
              double numericValue = 0.0;
              Expr exactExpr = toIntegerExpr(value, numericValue, max_double);
              if (exactExpr == NULL)
              {
                toSkip = true;
                break;
              }

              model.push_back(numericValue);
              if (debug)
                outs() << *bvar << " = " << *exactExpr << ", ";
              if (!containsOp<ARRAY_TY>(bvar) && i < liaVarsLocal.size())
                ms[i].insert(mk<EQ>(liaVarsLocal[i], exactExpr));
            }

            if (toSkip)
            {
              if (debug)
                outs() << "\b\b   <  skipping  >      ]\n";
              continue;
            }

            models[srcRel].push_back(model);
            if (debug)
              outs() << "\b\b]\n";
          }

          for (auto &a : ms)
            concrInvs[srcRel].insert(simplifyArithm(disjoin(a.second, m_efac)));

          if (chcsConsidered[trace.back()])
          {
            ExprSet mdls;
            for (auto &a : bindVars.back())
            {
              Expr mdl = allModels[a];
              if (mdl != NULL)
                mdls.insert(mk<EQ>(a, mdl));
            }
            exprModels[trace.back()] = replaceAll(conjoin(mdls, m_efac),
                                                  bindVars.back(), ruleManager.chcs[trace.back()].srcVars);
          }
        }
      }

      return res;
    }

    bool unrollAndExecuteMultiple(
        map<Expr, ExprVector> &invVars,
        map<Expr, vector<vector<double>>> &models,
        map<Expr, ExprVector> &arrRanges,
        map<Expr, ExprSet> &constr,
        int k = 10)
    {
      // helper var
      string str = to_string(numeric_limits<double>::max());
      str = str.substr(0, str.find('.'));
      cpp_int max_double = lexical_cast<cpp_int>(str);

      map<int, bool> chcsConsidered;
      map<int, Expr> exprModels;
      bool res = false;

      for (auto &c : ruleManager.cycles)
      {
        Expr invRel = c.first;
        for (int cyc = 0; cyc < ruleManager.cycles[invRel].size(); cyc++)
        {
          vector<int> mainInds;
          auto &loop = ruleManager.cycles[invRel][cyc];
          Expr srcRel = invRel;
          // Expr srcRel = ruleManager.chcs[loop[0]].srcRelation;
          ExprVector &srcVars = ruleManager.chcs[loop[0]].srcVars;
          if (models[srcRel].size() > 0)
            continue;

          ExprVector vars;
          for (int i = 0; i < srcVars.size(); i++)
          {
            Expr t = typeOf(srcVars[i]);
            if (isOpX<INT_TY>(t))
            {
              mainInds.push_back(i);
              vars.push_back(srcVars[i]);
            }
            else if (isOpX<ARRAY_TY>(t) && ruleManager.hasArrays[srcRel])
            {
              Expr v = findSelect(loop[0], i);
              if (v != NULL)
              {
                vars.push_back(v);
                mainInds.push_back(-i - 1); // to be on the negative side
              }
            }
          }

          // Find another check to make to skip some unrollings DR
          // if (vars.size() < 2 && cyc == ruleManager.cycles[invRel].size() - 1)
          // continue; // does not make much sense to run with only one var when it is the last cycle
          invVars[srcRel] = vars;

          auto &prefix = ruleManager.prefixes[invRel][cyc];
          vector<int> trace;
          Expr lastModel = mk<TRUE>(m_efac);

          for (int p = 0; p < prefix.size(); p++)
          {
            if (chcsConsidered[prefix[p]] == true)
            {
              Expr lastModelTmp = exprModels[prefix[p]];
              if (lastModelTmp != NULL)
                lastModel = lastModelTmp;
              trace.clear(); // to avoid CHCs at the beginning
            }
            trace.push_back(prefix[p]);
          }

          int l = trace.size() - 1; // starting index (before the loop)
          if (ruleManager.hasArrays[srcRel])
            l++; // first iter is usually useless

          for (int j = 0; j < k; j++)
            for (int m = 0; m < loop.size(); m++)
              trace.push_back(loop[m]);

          int backCHC = -1;
          for (int i = 0; i < ruleManager.chcs.size(); i++)
          {
            auto &r = ruleManager.chcs[i];
            if (i != loop[0] && !r.isQuery && r.srcRelation == srcRel)
            {
              backCHC = i;
              chcsConsidered[i] = true; // entry condition for the next loop
              trace.push_back(i);
              break;
            }
          }

          ExprVector ssa;
          getSSA(trace, ssa);
          bindVars.pop_back();
          int traceSz = trace.size();
          assert(bindVars.size() == traceSz - 1);

          // compute vars for opt constraint
          vector<ExprVector> versVars;
          ExprSet allVars;
          ExprVector diseqs;
          fillVars(srcRel, srcVars, vars, l, loop.size(), mainInds, versVars, allVars);
          getOptimConstr(versVars, vars.size(), srcVars, constr[srcRel], NULL, diseqs);

          Expr cntvar = bind::intConst(mkTerm<string>("_FH_cnt", m_efac));
          allVars.insert(cntvar);
          allVars.insert(bindVars.back().begin(), bindVars.back().end());
          ssa.insert(ssa.begin(), mk<EQ>(cntvar, mkplus(diseqs, m_efac)));

          // for arrays, make sure the ranges are large enough
          for (auto &v : arrRanges[srcRel])
            ssa.insert(ssa.begin(), replaceAll(mk<GT>(v, mkMPZ(k, m_efac)), srcVars, bindVars[0]));

          bool toContinue = false;
          bool noopt = false;
          while (true)
          {
            if (bindVars.size() <= 1)
            {
              if (debug)
                outs() << "Unable to find a suitable unrolling for " << *srcRel << "\n";
              toContinue = true;
              break;
            }

            if (u.isSat(lastModel, conjoin(ssa, m_efac)))
            {
              if (backCHC != -1 && trace.back() != backCHC &&
                  trace.size() != traceSz - 1) // finalizing the unrolling (exit CHC)
              {
                trace.push_back(backCHC);
                ssa.clear(); // encode from scratch
                getSSA(trace, ssa);
                bindVars.pop_back();
                noopt = true; // TODO: support optimization queries
              }
              else
                break;
            }
            else
            {
              noopt = true; // TODO: support
              if (trace.size() == traceSz)
              {
                trace.pop_back();
                ssa.pop_back();
                bindVars.pop_back();
              }
              else
              {
                trace.resize(trace.size() - loop.size());
                ssa.resize(ssa.size() - loop.size());
                bindVars.resize(bindVars.size() - loop.size());
              }
            }
          }

          if (toContinue)
            continue;
          res = true;
          map<int, ExprSet> ms;

          ExprMap allModels;
          if (noopt)
            u.getModel(allVars, allModels);
          else
            u.getOptModel<GT>(allVars, allModels, cntvar);

          if (debug)
            outs() << "\nUnroll and execute the cycle for " << srcRel << "\n";
          for (int j = 0; j < versVars.size(); j++)
          {
            vector<double> model;
            bool toSkip = false;
            if (debug)
              outs() << "  model for " << j << ": [";

            for (int i = 0; i < vars.size(); i++)
            {
              Expr bvar = versVars[j][i];
              Expr m = allModels[bvar];
              double value;
              if (m != NULL && isOpX<MPZ>(m))
              {
                if (lexical_cast<cpp_int>(m) > max_double ||
                    lexical_cast<cpp_int>(m) < -max_double)
                {
                  toSkip = true;
                  break;
                }
                value = lexical_cast<double>(m);
              }
              else
              {
                toSkip = true;
                break;
              }
              model.push_back(value);
              if (debug)
                outs() << *bvar << " = " << *m << ", ";
              if (!containsOp<ARRAY_TY>(bvar))
                ms[i].insert(mk<EQ>(vars[i], m));
            }
            if (toSkip)
            {
              if (debug)
                outs() << "\b\b   <  skipping  >      ]\n";
            }
            else
            {
              models[srcRel].push_back(model);
              if (debug)
                outs() << "\b\b]\n";
            }
          }

          for (auto &a : ms)
            concrInvs[srcRel].insert(simplifyArithm(disjoin(a.second, m_efac)));

          // although we care only about integer variables for the matrix above,
          // we still keep the entire model to bootstrap the model generation for the next loop
          if (chcsConsidered[trace.back()])
          {
            ExprSet mdls;
            for (auto &a : bindVars.back())
              if (allModels[a] != NULL)
                mdls.insert(mk<EQ>(a, allModels[a]));
            exprModels[trace.back()] = replaceAll(conjoin(mdls, m_efac),
                                                  bindVars.back(), ruleManager.chcs[trace.back()].srcVars);
          }
        }
      }

      return res;
    }
  };

  inline void unrollAndCheck(string smt, int bnd1, int bnd2, int to, bool skip_elim, int debug)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);
    if (!ruleManager.parse(smt, !skip_elim))
      return;
    BndExpl bnd(ruleManager, to, debug);
    bnd.exploreTraces(bnd1, bnd2, true);
  };

  inline bool kInduction(CHCs &ruleManager, int bnd)
  {
    if (ruleManager.chcs.size() != 3)
    {
      outs() << "currently not supported\n";
      return false;
    }

    BndExpl ds(ruleManager, false);

    bool success = false;
    int i;
    for (i = 2; i < bnd; i++)
    {
      if (ds.kIndIter(i, i))
      {
        success = true;
        break;
      }
    }

    outs() << "\n"
           << (success ? "K-induction succeeded " : "Unknown result ") << "after " << (i - 1) << " iterations\n";

    return success;
  };

  inline void kInduction(string smt, int bnd)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    kInduction(ruleManager, bnd);
  };
}

#endif