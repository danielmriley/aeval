#ifndef BVCOM__HPP__
#define BVCOM__HPP__

#include <algorithm>
#include <cassert>
#include <map>
#include <set>
#include <string>
#include <vector>

#include <boost/lexical_cast.hpp>
#include <boost/multiprecision/cpp_int.hpp>

#include "ae/ExprSimpl.hpp"
#include "ae/ExprSimplBv.hpp"
#include "deep/Distribution.hpp"
#include "deep/Horn.hpp"
#include "ufo/Expr.hpp"
#include "ufo/ExprBv.hh"

namespace ufo
{
  using namespace expr;
  using namespace expr::op;
  using namespace expr::op::bv;
  using namespace expr::op::bind;

  using boost::lexical_cast;
  using boost::multiprecision::cpp_int;

  constexpr unsigned DEFAULT_WIDTH = 4;
  constexpr unsigned MAX_BUCKET = 64;

  enum class BVCoefScheme
  {
    PlusMinusOne,
    PlusMinusOneTwo,
    PowersOfTwo,
    SeededFallback
  };

  enum class BVComparatorKind
  {
    Eq,
    Neq,
    Ult,
    Ule,
    Ugt,
    Uge
  };

  struct BVFactoryConfig
  {
    unsigned width = DEFAULT_WIDTH;
    bool normalizeConstants = true;
    BVCoefScheme coefScheme = BVCoefScheme::PlusMinusOne;
    std::vector<cpp_int> maskCatalog;
    std::map<int, int> shapeSeeds;
  };

  enum class BVTermShape : int
  {
    MaskEquality = 0,
    Range = 1,
    ModularSum = 2,
    Unary = 3,
    BinaryExpr = 4,
    BinaryCmp = 5,
    NaryExpr = 6
  };

  enum class BVUnaryOp : int
  {
    Not = 0,
    Neg = 1
  };

  enum class BVBinaryOp : int
  {
    Add = 0,
    Sub = 1,
    And = 2,
    Or = 3,
    Xor = 4
  };

  enum class BVNaryOp : int
  {
    And = 0,
    Or = 1,
    Xor = 2
  };

  struct BVRangeInfo
  {
    bool signedSemantics = false;
    int lowerConst = -1;
    int upperConst = -1;
  };

  struct BVUnaryInfo
  {
    BVUnaryOp op = BVUnaryOp::Not;
    unsigned param0 = 0;
    unsigned param1 = 0;
    int constIndex = -1;
  };

  struct BVVarCoef
  {
    int varIndex = -1;
    int coefKind = -1;
  };

  struct BVterm
  {
    BVTermShape shape = BVTermShape::MaskEquality;
    unsigned width = DEFAULT_WIDTH;
    int varIndex = -1;
    int maskIndex = -1;
    int valueIndex = -1;
    int comparator = -1;
    int constIndex = -1;
    std::vector<BVVarCoef> varCoefs;
    BVRangeInfo rangeInfo;
    BVUnaryInfo unaryInfo;
    int binaryOp = -1;
    int binaryCmp = -1;
    int varIndex2 = -1;
    int naryOp = -1;
    std::vector<int> varIndices;

    BVterm() = default;
    explicit BVterm(unsigned w) : width(w) {}
  };

  class BVdisj
  {
  public:
    int arity = 0;
    std::vector<BVterm> dstate;

    bool empty() const
    {
      return arity == 0;
    }

    BVterm &newDisj(unsigned widthHint = DEFAULT_WIDTH)
    {
      dstate.emplace_back(widthHint);
      arity = static_cast<int>(dstate.size());
      return dstate.back();
    }

    void addDisj(const BVterm &term)
    {
      dstate.push_back(term);
      arity = static_cast<int>(dstate.size());
    }

    void normalizePlus() {}

    void clear()
    {
      dstate.clear();
      arity = 0;
    }
  };

  struct BVComparatorInfo
  {
    Expr templ;
    BVComparatorKind kind;
  };

  class BVfactory
  {
  public:
    ExprMap nonlinVars;
    ExprSet nonlinVarsSet;
    unsigned width = DEFAULT_WIDTH;
    const std::vector<HornRuleExt> *m_chcs = nullptr;

    std::map<int, int> chcBinaryOpFreq;
    std::map<int, int> chcBinaryCmpFreq;
    std::map<int, int> chcNaryOpFreq;
    std::set<cpp_int> chcConsts;
    std::map<int, int> chcArities;

    explicit BVfactory(ExprFactory &efac, bool, const std::vector<HornRuleExt> &chcs) : m_efac(efac), m_chcs(&chcs) {}

    void reset()
    {
      vars.clear();
      varIndexCache.clear();
      intConsts.clear();
      constIndexCache.clear();
      intConstsE.clear();
      intCoefs.clear();
      coefIndexCache.clear();
      intCoefsE.clear();
      maskCatalog.clear();
      maskIndexCache.clear();
      maskCatalogE.clear();
      comparatorInfo.clear();
      shapeWeights.clear();
      maskVarWeights.clear();
      maskMaskWeights.clear();
      maskValueWeights.clear();
      rangeVarWeights.clear();
      rangeLowerWeights.clear();
      rangeUpperWeights.clear();
      rangeSignWeights.clear();
      modularVarComboWeights.clear();
      modularCoefWeights.clear();
      modularConstWeights.clear();
      modularComparatorWeights.clear();
      unaryVarWeights.clear();
      unaryOpWeights.clear();
      binaryOpWeights.clear();
      binaryCmpWeights.clear();
      varCombinations.clear();
      cachedBuckets.clear();
      nonlinVars.clear();
      nonlinVarsSet.clear();
      _initialized = false;
    }

    void addVar(Expr var)
    {
      if (varIndexCache.count(var) > 0)
      {
        return;
      }
      int index = static_cast<int>(vars.size());
      vars.push_back(var);
      varIndexCache[var] = index;
    }

    void addIntCoef(const cpp_int &coef)
    {
      ensureCoefCached(coef);
    }

    void configure(const BVFactoryConfig &cfg)
    {
      _config = cfg;
      width = (_config.width == 0 ? width : _config.width);
    }

    void initialize(unsigned widthHint = 0)
    {
      if (widthHint > 0)
      {
        _config.width = widthHint;
      }
      width = bitWidth();
      rebuildConstExpressions();
      buildCoefficientCatalog();
      ensureConstCached(cpp_int(0));
      buildMaskCatalog();
      buildComparatorTemplates();
      initVarCombinations();
      nonlinVarsSet.clear();
      for (auto &kv : nonlinVars)
      {
        nonlinVarsSet.insert(kv.second);
      }
      computeDefaultWeights();
      analyzeCHC();
      _initialized = true;
    }

    bool initialized() const
    {
      return _initialized;
    }

    ExprVector &getVars()
    {
      return vars;
    }

    std::vector<cpp_int> &getConsts()
    {
      return intConsts;
    }

    Expr buildExpr(const BVterm &term) const
    {
      switch (term.shape)
      {
        case BVTermShape::MaskEquality:
          return buildMaskExpr(term);
        case BVTermShape::Range:
          return buildRangeExpr(term);
        case BVTermShape::ModularSum:
          return buildModularExpr(term);
        case BVTermShape::Unary:
          return buildUnaryExpr(term);
        case BVTermShape::BinaryExpr:
          return buildBinaryExpr(term);
        case BVTermShape::BinaryCmp:
          return buildBinaryCmp(term);
        case BVTermShape::NaryExpr:
        default:
          return buildNaryExpr(term);
      }
    }

    Expr toExpr(const BVterm &term) const
    {
      return buildExpr(term);
    }

    Expr toExpr(const BVdisj &disj) const
    {
      ExprVector clauses;
      for (const BVterm &term : disj.dstate)
      {
        clauses.push_back(buildExpr(term));
      }
      if (clauses.empty())
      {
        return mk<TRUE>(m_efac);
      }
      if (clauses.size() == 1)
      {
        return clauses.front();
      }
      return disjoin(clauses, m_efac);
    }

    void exprToBVdisj(Expr ex, BVdisj &sample)
    {
      if (!ex)
      {
        return;
      }
      if (isOpX<OR>(ex))
      {
        for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it)
        {
          exprToBVdisj(*it, sample);
        }
        return;
      }
      BVterm term(bitWidth());
      if (decodeTerm(ex, term))
      {
        sample.addDisj(term);
      }
    }

    BVterm sampleTerm(BVTermShape desiredShape)
    {
      switch (desiredShape)
      {
        case BVTermShape::MaskEquality:
          return sampleMaskTerm();
        case BVTermShape::Range:
          return sampleRangeTerm();
        case BVTermShape::Unary:
          return sampleUnaryTerm();
        case BVTermShape::ModularSum:
          return sampleModularTerm();
        case BVTermShape::BinaryExpr:
          return sampleBinaryExprTerm();
        case BVTermShape::BinaryCmp:
          return sampleBinaryCmpTerm();
        case BVTermShape::NaryExpr:
        default:
          return sampleNaryExprTerm();
      }
    }

    BVterm sampleTerm()
    {
      int key = chooseByWeight(shapeWeights);
      BVTermShape shape = static_cast<BVTermShape>(key);
      return sampleTerm(shape);
    }

    void cacheTerm(const BVterm &term)
    {
      cachedBuckets[term.shape].push_back(term);
      if (cachedBuckets[term.shape].size() > MAX_BUCKET)
      {
        cachedBuckets[term.shape].erase(cachedBuckets[term.shape].begin());
      }
    }

    const std::map<BVTermShape, std::vector<BVterm>> &getBuckets() const
    {
      return cachedBuckets;
    }

    void clearBuckets()
    {
      cachedBuckets.clear();
    }

    void initDensities(const std::set<int> &)
    {
      computeDefaultWeights();
    }

    void calculateStatistics(const BVdisj &sample, int, bool, bool)
    {
      for (const BVterm &term : sample.dstate)
      {
        cacheTerm(term);
      }
    }

    void stabilizeDensities(int, bool, bool)
    {
      computeDefaultWeights();
    }

    bool guessTerm(BVdisj &sample, int arity, bool)
    {
      if (!_initialized)
      {
        return false;
      }
      if (vars.empty())
      {
        return false;
      }
      sample.clear();
      int disjCount = std::max(1, arity);
      for (int i = 0; i < disjCount; ++i)
      {
        sample.addDisj(sampleTerm());
      }
      return !sample.empty();
    }

    void rewardMaskEquality(const BVterm &term)
    {
      adjustDensity(maskVarWeights, term.varIndex, PRIORITY_REWARD);
      adjustDensity(maskMaskWeights, term.maskIndex, PRIORITY_REWARD);
      adjustDensity(maskValueWeights, term.valueIndex, PRIORITY_REWARD);
    }

    void penalizeMaskEquality(const BVterm &term)
    {
      adjustDensity(maskVarWeights, term.varIndex, -PRIORITY_PENALTY);
      adjustDensity(maskMaskWeights, term.maskIndex, -PRIORITY_PENALTY);
      adjustDensity(maskValueWeights, term.valueIndex, -PRIORITY_PENALTY);
    }

    void dampMaskEquality(const BVterm &term)
    {
      reduceDensity(maskVarWeights, term.varIndex);
      reduceDensity(maskMaskWeights, term.maskIndex);
      reduceDensity(maskValueWeights, term.valueIndex);
    }

    void rewardRange(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, PRIORITY_REWARD);
      adjustDensity(rangeLowerWeights, term.rangeInfo.lowerConst, PRIORITY_REWARD);
      adjustDensity(rangeUpperWeights, term.rangeInfo.upperConst, PRIORITY_REWARD);
      adjustDensity(rangeSignWeights, term.rangeInfo.signedSemantics ? 1 : 0, PRIORITY_REWARD);
    }

    void penalizeRange(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, -PRIORITY_PENALTY);
      adjustDensity(rangeLowerWeights, term.rangeInfo.lowerConst, -PRIORITY_PENALTY);
      adjustDensity(rangeUpperWeights, term.rangeInfo.upperConst, -PRIORITY_PENALTY);
      adjustDensity(rangeSignWeights, term.rangeInfo.signedSemantics ? 1 : 0, -PRIORITY_PENALTY);
    }

    void dampRange(const BVterm &term)
    {
      reduceDensity(rangeVarWeights, term.varIndex);
      reduceDensity(rangeLowerWeights, term.rangeInfo.lowerConst);
      reduceDensity(rangeUpperWeights, term.rangeInfo.upperConst);
      reduceDensity(rangeSignWeights, term.rangeInfo.signedSemantics ? 1 : 0);
    }

    void rewardModularSum(const BVterm &term)
    {
      for (auto &vc : term.varCoefs)
      {
        adjustDensity(rangeVarWeights, vc.varIndex, PRIORITY_REWARD);
        adjustDensity(modularCoefWeights, vc.coefKind, PRIORITY_REWARD);
      }
      adjustDensity(modularConstWeights, term.constIndex, PRIORITY_REWARD);
      adjustDensity(modularComparatorWeights, term.comparator, PRIORITY_REWARD);
    }

    void penalizeModularSum(const BVterm &term)
    {
      for (auto &vc : term.varCoefs)
      {
        adjustDensity(rangeVarWeights, vc.varIndex, -PRIORITY_PENALTY);
        adjustDensity(modularCoefWeights, vc.coefKind, -PRIORITY_PENALTY);
      }
      adjustDensity(modularConstWeights, term.constIndex, -PRIORITY_PENALTY);
      adjustDensity(modularComparatorWeights, term.comparator, -PRIORITY_PENALTY);
    }

    void dampModularSum(const BVterm &term)
    {
      for (auto &vc : term.varCoefs)
      {
        reduceDensity(rangeVarWeights, vc.varIndex);
        reduceDensity(modularCoefWeights, vc.coefKind);
      }
      reduceDensity(modularConstWeights, term.constIndex);
      reduceDensity(modularComparatorWeights, term.comparator);
    }

    void rewardUnary(const BVterm &term)
    {
      adjustDensity(unaryVarWeights, term.varIndex, PRIORITY_REWARD);
      adjustDensity(unaryOpWeights, static_cast<int>(term.unaryInfo.op), PRIORITY_REWARD);
      adjustDensity(maskValueWeights, term.unaryInfo.constIndex, PRIORITY_REWARD);
    }

    void penalizeUnary(const BVterm &term)
    {
      adjustDensity(unaryVarWeights, term.varIndex, -PRIORITY_PENALTY);
      adjustDensity(unaryOpWeights, static_cast<int>(term.unaryInfo.op), -PRIORITY_PENALTY);
      adjustDensity(maskValueWeights, term.unaryInfo.constIndex, -PRIORITY_PENALTY);
    }

    void dampUnary(const BVterm &term)
    {
      reduceDensity(unaryVarWeights, term.varIndex);
      reduceDensity(unaryOpWeights, static_cast<int>(term.unaryInfo.op));
      reduceDensity(maskValueWeights, term.unaryInfo.constIndex);
    }

    void rewardBinaryExpr(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, PRIORITY_REWARD);
      adjustDensity(rangeVarWeights, term.varIndex2, PRIORITY_REWARD);
      adjustDensity(binaryOpWeights, term.binaryOp, PRIORITY_REWARD);
      adjustDensity(maskValueWeights, term.valueIndex, PRIORITY_REWARD);
    }

    void penalizeBinaryExpr(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, -PRIORITY_PENALTY);
      adjustDensity(rangeVarWeights, term.varIndex2, -PRIORITY_PENALTY);
      adjustDensity(binaryOpWeights, term.binaryOp, -PRIORITY_PENALTY);
      adjustDensity(maskValueWeights, term.valueIndex, -PRIORITY_PENALTY);
    }

    void dampBinaryExpr(const BVterm &term)
    {
      reduceDensity(rangeVarWeights, term.varIndex);
      reduceDensity(rangeVarWeights, term.varIndex2);
      reduceDensity(binaryOpWeights, term.binaryOp);
      reduceDensity(maskValueWeights, term.valueIndex);
    }

    void rewardBinaryCmp(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, PRIORITY_REWARD);
      adjustDensity(rangeVarWeights, term.varIndex2, PRIORITY_REWARD);
      adjustDensity(binaryCmpWeights, term.binaryCmp, PRIORITY_REWARD);
    }

    void penalizeBinaryCmp(const BVterm &term)
    {
      adjustDensity(rangeVarWeights, term.varIndex, -PRIORITY_PENALTY);
      adjustDensity(rangeVarWeights, term.varIndex2, -PRIORITY_PENALTY);
      adjustDensity(binaryCmpWeights, term.binaryCmp, -PRIORITY_PENALTY);
    }

    void dampBinaryCmp(const BVterm &term)
    {
      reduceDensity(rangeVarWeights, term.varIndex);
      reduceDensity(rangeVarWeights, term.varIndex2);
      reduceDensity(binaryCmpWeights, term.binaryCmp);
    }

    void rewardNaryExpr(const BVterm &term)
    {
      adjustDensity(naryOpWeights, term.naryOp, PRIORITY_REWARD);
      for (int idx : term.varIndices)
      {
        adjustDensity(rangeVarWeights, idx, PRIORITY_REWARD);
      }
      adjustDensity(maskValueWeights, term.valueIndex, PRIORITY_REWARD);
    }

    void penalizeNaryExpr(const BVterm &term)
    {
      adjustDensity(naryOpWeights, term.naryOp, -PRIORITY_PENALTY);
      for (int idx : term.varIndices)
      {
        adjustDensity(rangeVarWeights, idx, -PRIORITY_PENALTY);
      }
      adjustDensity(maskValueWeights, term.valueIndex, -PRIORITY_PENALTY);
    }

    void dampNaryExpr(const BVterm &term)
    {
      reduceDensity(naryOpWeights, term.naryOp);
      for (int idx : term.varIndices)
      {
        reduceDensity(rangeVarWeights, idx);
      }
      reduceDensity(maskValueWeights, term.valueIndex);
    }

    void addConst(const cpp_int &c)
    {
      ensureConstIndex(c);
    }

    void assignPrioritiesForLearned(BVdisj &learned)
    {
      for (auto &term : learned.dstate)
      {
        switch (term.shape)
        {
          case BVTermShape::MaskEquality:
            rewardMaskEquality(term);
            break;
          case BVTermShape::Range:
            rewardRange(term);
            break;
          case BVTermShape::ModularSum:
            rewardModularSum(term);
            break;
          case BVTermShape::Unary:
            rewardUnary(term);
            break;
          case BVTermShape::BinaryExpr:
            rewardBinaryExpr(term);
            break;
          case BVTermShape::BinaryCmp:
            rewardBinaryCmp(term);
            break;
          case BVTermShape::NaryExpr:
            rewardNaryExpr(term);
            break;
        }
      }
    }

    void assignPrioritiesForFailed(BVdisj &failed)
    {
      for (auto &term : failed.dstate)
      {
        switch (term.shape)
        {
          case BVTermShape::MaskEquality:
            penalizeMaskEquality(term);
            break;
          case BVTermShape::Range:
            penalizeRange(term);
            break;
          case BVTermShape::ModularSum:
            penalizeModularSum(term);
            break;
          case BVTermShape::Unary:
            penalizeUnary(term);
            break;
          case BVTermShape::BinaryExpr:
            penalizeBinaryExpr(term);
            break;
          case BVTermShape::BinaryCmp:
            penalizeBinaryCmp(term);
            break;
          case BVTermShape::NaryExpr:
            penalizeNaryExpr(term);
            break;
        }
      }
    }

    void assignPrioritiesForBlocked(BVdisj &blocked)
    {
      for (auto &term : blocked.dstate)
      {
        switch (term.shape)
        {
          case BVTermShape::MaskEquality:
            dampMaskEquality(term);
            break;
          case BVTermShape::Range:
            dampRange(term);
            break;
          case BVTermShape::ModularSum:
            dampModularSum(term);
            break;
          case BVTermShape::Unary:
            dampUnary(term);
            break;
          case BVTermShape::BinaryExpr:
            dampBinaryExpr(term);
            break;
          case BVTermShape::BinaryCmp:
            dampBinaryCmp(term);
            break;
          case BVTermShape::NaryExpr:
            dampNaryExpr(term);
            break;
        }
      }
    }

    void printCodeStatistics(int ar) const
    {
      outs() << "BV Sampler Statistics (arity " << ar << "):" << ::std::endl;
      outs() << "Shape weights:" << ::std::endl;
      for (auto &kv : shapeWeights)
      {
        outs() << "  Shape " << kv.first << ": " << kv.second << ::std::endl;
      }
    }

  private:
    ExprFactory &m_efac;
    bool _initialized = false;
    BVFactoryConfig _config;
    ExprVector vars;
    std::map<Expr, int> varIndexCache;
    std::vector<cpp_int> intConsts;
    std::map<cpp_int, int> constIndexCache;
    ExprVector intConstsE;
    std::vector<cpp_int> intCoefs;
    std::map<cpp_int, int> coefIndexCache;
    ExprVector intCoefsE;
    std::vector<cpp_int> maskCatalog;
    std::map<cpp_int, int> maskIndexCache;
    ExprVector maskCatalogE;
    Expr auxVarLhs;
    Expr auxVarRhs;
    density shapeWeights;
    density maskVarWeights;
    density maskMaskWeights;
    density maskValueWeights;
    density rangeVarWeights;
    density rangeLowerWeights;
    density rangeUpperWeights;
    density rangeSignWeights;
    density modularVarComboWeights;
    density modularCoefWeights;
    density modularConstWeights;
    density modularComparatorWeights;
    density unaryVarWeights;
    density unaryOpWeights;
    density binaryOpWeights;
    density binaryCmpWeights;
    density naryOpWeights;
    std::vector<std::vector<std::set<int>>> varCombinations;
    std::vector<BVComparatorInfo> comparatorInfo;
    std::map<BVTermShape, std::vector<BVterm>> cachedBuckets;
    static constexpr int PRIORITY_REWARD = 5;
    static constexpr int PRIORITY_PENALTY = 1;

    void adjustDensity(density &den, int key, int delta, int baseline = 1)
    {
      if (den.count(key) == 0) den[key] = baseline;
      den[key] += delta;
      if (den[key] <= 0) den[key] = baseline;
    }

    void reduceDensity(density &den, int key)
    {
      adjustDensity(den, key, -1);
    }

    cpp_int sanitizeMask(const cpp_int &mask) const
    {
      unsigned bw = bitWidth();
      if (bw == 0)
      {
        return mask;
      }
      cpp_int modulus = cpp_int(1) << bw;
      cpp_int normalized = mask % modulus;
      if (normalized < 0)
      {
        normalized += modulus;
      }
      return normalized;
    }

    void ensureConstWeights(int index)
    {
      ensureWeight(maskValueWeights, index);
      ensureWeight(rangeLowerWeights, index);
      ensureWeight(rangeUpperWeights, index);
      ensureWeight(modularConstWeights, index);
    }

    cpp_int randomConstantUnderMask(const cpp_int &mask) const
    {
      cpp_int normalizedMask = sanitizeMask(mask);
      if (normalizedMask == 0)
      {
        return 0;
      }
      cpp_int result = 0;
      unsigned bw = bitWidth();
      std::vector<unsigned> activeBits;
      activeBits.reserve(bw);
      for (unsigned bit = 0; bit < bw; ++bit)
      {
        if (boost::multiprecision::bit_test(normalizedMask, bit))
        {
          activeBits.push_back(bit);
          if (guessUniformly(2) == 1)
          {
            result |= cpp_int(1) << bit;
          }
        }
      }
      if (result == 0 && !activeBits.empty())
      {
        unsigned idx = guessUniformly(static_cast<int>(activeBits.size()));
        unsigned fallbackBit = activeBits[idx];
        result |= cpp_int(1) << fallbackBit;
      }
      return result;
    }

    int pickMaskCompatibleValue(int maskIndex)
    {
      if (maskIndex < 0 || static_cast<size_t>(maskIndex) >= maskCatalog.size())
      {
        int fallback = chooseByWeight(maskValueWeights);
        if (fallback < 0)
        {
          fallback = ensureConstIndex(cpp_int(0));
        }
        return fallback;
      }
      cpp_int mask = maskCatalog[maskIndex];
      for (int attempt = 0; attempt < 3; ++attempt)
      {
        int candidate = chooseByWeight(maskValueWeights);
        if (candidate < 0 || static_cast<size_t>(candidate) >= intConsts.size())
        {
          continue;
        }
        cpp_int value = normalizeConst(intConsts[candidate]);
        if ((value & mask) == value)
        {
          return candidate;
        }
      }
      cpp_int sampled = randomConstantUnderMask(mask);
      int index = ensureConstIndex(sampled);
      ensureConstWeights(index);
      return index;
    }

    bool maskTermSeenRecently(const BVterm &term) const
    {
      auto it = cachedBuckets.find(BVTermShape::MaskEquality);
      if (it == cachedBuckets.end())
      {
        return false;
      }
      for (const BVterm &cached : it->second)
      {
        if (cached.varIndex == term.varIndex &&
            cached.maskIndex == term.maskIndex &&
            cached.valueIndex == term.valueIndex)
        {
          return true;
        }
      }
      return false;
    }

    void nudgeMaskWeights(const BVterm &term)
    {
      reduceDensity(maskMaskWeights, term.maskIndex);
      reduceDensity(maskValueWeights, term.valueIndex);
    }

    int findVarIndex(Expr var) const
    {
      auto it = varIndexCache.find(var);
      if (it != varIndexCache.end())
      {
        return it->second;
      }
      return -1;
    }

    int ensureConstIndex(const cpp_int &value)
    {
      cpp_int normalized = normalizeConst(value);
      ensureConstCached(normalized);
      return constIndexCache[normalized];
    }

    int ensureCoefIndex(const cpp_int &value)
    {
      ensureCoefCached(value);
      return coefIndexCache[value];
    }

    int ensureMaskIndex(const cpp_int &value)
    {
      ensureMaskCached(value);
      return maskIndexCache[value];
    }

    int comparatorIndexForKind(BVComparatorKind kind) const
    {
      for (unsigned i = 0; i < comparatorInfo.size(); i++)
      {
        if (comparatorInfo[i].kind == kind)
        {
          return static_cast<int>(i);
        }
      }
      return -1;
    }

    int comparatorIndexFromExpr(Expr cmp) const
    {
      if (isOpX<EQ>(cmp)) return comparatorIndexForKind(BVComparatorKind::Eq);
      if (isOpX<NEQ>(cmp)) return comparatorIndexForKind(BVComparatorKind::Neq);
      if (isOpX<BULT>(cmp)) return comparatorIndexForKind(BVComparatorKind::Ult);
      if (isOpX<BULE>(cmp)) return comparatorIndexForKind(BVComparatorKind::Ule);
      if (isOpX<BUGT>(cmp)) return comparatorIndexForKind(BVComparatorKind::Ugt);
      if (isOpX<BUGE>(cmp)) return comparatorIndexForKind(BVComparatorKind::Uge);
      return -1;
    }

    cpp_int exprToInt(Expr e) const
    {
      if (!is_bvnum(e))
      {
        return cpp_int(0);
      }
      return lexical_cast<cpp_int>(toMpz(e));
    }

    bool decodeMaskTerm(Expr ex, BVterm &term)
    {
      if (!isOpX<EQ>(ex))
      {
        return false;
      }
      Expr lhs = ex->left();
      Expr rhs = ex->right();

      auto tryDecode = [&](Expr maskSide, Expr valueSide) -> bool
      {
        if (!isOpX<BAND>(maskSide)) return false;
        if (!is_bvnum(valueSide)) return false;
        Expr var;
        Expr maskExpr;
        for (auto ait = maskSide->args_begin(), aend = maskSide->args_end(); ait != aend; ++ait)
        {
          Expr arg = *ait;
          if (is_bvnum(arg))
          {
            maskExpr = arg;
          }
          else
          {
            var = arg;
          }
        }
        if (!var || !maskExpr)
        {
          return false;
        }
        int varIdx = findVarIndex(var);
        if (varIdx < 0)
        {
          return false;
        }
        cpp_int maskVal = exprToInt(maskExpr);
        cpp_int valueVal = exprToInt(valueSide);
        term.shape = BVTermShape::MaskEquality;
        term.varIndex = varIdx;
        term.maskIndex = ensureMaskIndex(maskVal);
        term.valueIndex = ensureConstIndex(valueVal);
        term.width = bitWidth();
        return true;
      };

      if (tryDecode(lhs, rhs)) return true;
      if (tryDecode(rhs, lhs)) return true;
      return false;
    }

    bool decodeRangeTerm(Expr ex, BVterm &term)
    {
      if (!isOpX<AND>(ex))
      {
        return false;
      }
      Expr varExpr;
      cpp_int lowerVal = 0;
      cpp_int upperVal = 0;
      bool hasLower = false;
      bool hasUpper = false;
      bool signedSemantics = false;

      for (auto it = ex->args_begin(), end = ex->args_end(); it != end; ++it)
      {
        Expr arg = *it;
        bool isSignedCmp = isOpX<BSGE>(arg) || isOpX<BSLE>(arg) || isOpX<BSGT>(arg) || isOpX<BSLT>(arg);
        if (isSignedCmp)
        {
          signedSemantics = true;
        }
        if (!(isOpX<BUGE>(arg) || isOpX<BULE>(arg) || isOpX<BSGE>(arg) || isOpX<BSLE>(arg)))
        {
          return false;
        }
        Expr lhs = arg->left();
        Expr rhs = arg->right();
        bool swapped = false;
        if (is_bvnum(lhs) && !is_bvnum(rhs))
        {
          std::swap(lhs, rhs);
          swapped = true;
        }
        if (!is_bvnum(rhs))
        {
          return false;
        }
        if (!varExpr)
        {
          varExpr = lhs;
        }
        else if (varExpr != lhs)
        {
          return false;
        }

        cpp_int bound = exprToInt(rhs);
        if (isOpX<BUGE>(arg) || isOpX<BSGE>(arg))
        {
          if (swapped)
          {
            return false;
          }
          lowerVal = bound;
          hasLower = true;
        }
        else if (isOpX<BULE>(arg) || isOpX<BSLE>(arg))
        {
          if (swapped)
          {
            return false;
          }
          upperVal = bound;
          hasUpper = true;
        }
      }

      if (!hasLower || !hasUpper || !varExpr)
      {
        return false;
      }

      int varIdx = findVarIndex(varExpr);
      if (varIdx < 0)
      {
        return false;
      }

      term.shape = BVTermShape::Range;
      term.width = bitWidth();
      term.varIndex = varIdx;
      term.rangeInfo.signedSemantics = signedSemantics;
      term.rangeInfo.lowerConst = ensureConstIndex(lowerVal);
      term.rangeInfo.upperConst = ensureConstIndex(upperVal);
      return true;
    }

    bool decodeUnaryTerm(Expr ex, BVterm &term)
    {
      if (!isOpX<EQ>(ex))
      {
        return false;
      }
      Expr lhs = ex->left();
      Expr rhs = ex->right();
      auto tryDecode = [&](Expr opSide, Expr valueSide) -> bool
      {
        if (!is_bvnum(valueSide)) return false;
        Expr var;
        BVUnaryOp op = BVUnaryOp::Not;
        unsigned param0 = 0;
        unsigned param1 = 0;
        if (isOpX<BNOT>(opSide))
        {
          op = BVUnaryOp::Not;
          var = opSide->left();
        }
        else if (isOpX<BNEG>(opSide))
        {
          op = BVUnaryOp::Neg;
          var = opSide->left();
        }
        else
        {
          return false;
        }
        int varIdx = findVarIndex(var);
        if (varIdx < 0)
        {
          return false;
        }
        term.shape = BVTermShape::Unary;
        term.width = bitWidth();
        term.varIndex = varIdx;
        term.unaryInfo.op = op;
        term.unaryInfo.param0 = param0;
        term.unaryInfo.param1 = param1;
        term.unaryInfo.constIndex = ensureConstIndex(exprToInt(valueSide));
        return true;
      };

      if (tryDecode(lhs, rhs)) return true;
      if (tryDecode(rhs, lhs)) return true;
      return false;
    }

    bool decodeModularTerm(Expr ex, BVterm &term)
    {
      int cmpIndex = comparatorIndexFromExpr(ex);
      if (cmpIndex < 0)
      {
        return false;
      }

      Expr lhs = ex->left();
      Expr rhs = ex->right();

      if (!is_bvnum(rhs) && is_bvnum(lhs))
      {
        std::swap(lhs, rhs);
        cmpIndex = comparatorIndexForKind(comparatorInfo[cmpIndex].kind);
      }

      if (!is_bvnum(rhs))
      {
        return false;
      }

      cpp_int rhsVal = exprToInt(rhs);
      cpp_int accum = 0;

      ExprVector addTerms;
      getAddTermBV(lhs, addTerms);
      if (addTerms.empty())
      {
        addTerms.push_back(lhs);
      }

      for (Expr summand : addTerms)
      {
        if (is_bvnum(summand))
        {
          accum += exprToInt(summand);
          continue;
        }

        ExprVector factors;
        getMultOpsBV(summand, factors);
        if (factors.empty())
        {
          factors.push_back(summand);
        }

        Expr varExpr;
        cpp_int coef = 1;
        bool hasCoef = false;

        for (Expr f : factors)
        {
          if (is_bvnum(f))
          {
            coef = exprToInt(f);
            hasCoef = true;
          }
          else if (!varExpr)
          {
            varExpr = f;
          }
        }

        if (!varExpr)
        {
          accum += coef;
          continue;
        }

        int varIdx = findVarIndex(varExpr);
        if (varIdx < 0)
        {
          return false;
        }

        if (!hasCoef)
        {
          coef = 1;
        }

        BVVarCoef vc;
        vc.varIndex = varIdx;
        vc.coefKind = ensureCoefIndex(coef);
        term.varCoefs.push_back(vc);
      }

      cpp_int adjustedConst = rhsVal - accum;
      term.shape = BVTermShape::ModularSum;
      term.width = bitWidth();
      term.comparator = cmpIndex;
      term.constIndex = ensureConstIndex(adjustedConst);
      return true;
    }

    bool decodeTerm(Expr ex, BVterm &term)
    {
      term = BVterm(bitWidth());
      if (decodeMaskTerm(ex, term)) return true;
      if (decodeRangeTerm(ex, term)) return true;
      if (decodeUnaryTerm(ex, term)) return true;
      if (decodeModularTerm(ex, term)) return true;
      return false;
    }

    unsigned bitWidth() const
    {
      if (_config.width != 0)
      {
        return _config.width;
      }
      if (width != 0)
      {
        return width;
      }
      return DEFAULT_WIDTH;
    }

    cpp_int normalizeConst(const cpp_int &value) const
    {
      if (!_config.normalizeConstants) return value;
      unsigned bw = bitWidth();
      if (bw == 0) return value;
      cpp_int modulus = cpp_int(1) << bw;
      cpp_int modded = value % modulus;
      if (modded < 0) modded += modulus;
      cpp_int alternative = modded - modulus;
      if (boost::multiprecision::abs(alternative) < boost::multiprecision::abs(modded))
      {
        return alternative;
      }
      return modded;
    }

    void ensureConstCached(const cpp_int &value)
    {
      if (constIndexCache.count(value) > 0)
      {
        return;
      }
      int index = static_cast<int>(intConsts.size());
      intConsts.push_back(value);
      constIndexCache[value] = index;
      unsigned bw = bitWidth();
      Expr constExpr = bvnum(lexical_cast<mpz_class>(value), bw, m_efac);
      intConstsE.push_back(constExpr);
      ensureConstWeights(index);
    }

    void rebuildConstExpressions()
    {
      intConstsE.clear();
      if (intConsts.empty())
      {
        return;
      }
      unsigned bw = bitWidth();
      for (const cpp_int &value : intConsts)
      {
        Expr constExpr = bvnum(lexical_cast<mpz_class>(value), bw, m_efac);
        intConstsE.push_back(constExpr);
      }
    }

    void ensureCoefCached(const cpp_int &value)
    {
      if (coefIndexCache.count(value) > 0)
      {
        return;
      }
      int index = static_cast<int>(intCoefs.size());
      intCoefs.push_back(value);
      coefIndexCache[value] = index;
      unsigned bw = bitWidth();
      Expr coefExpr = bvnum(lexical_cast<mpz_class>(value), bw, m_efac);
      intCoefsE.push_back(coefExpr);
    }

    void ensureMaskCached(const cpp_int &mask)
    {
      cpp_int normalized = sanitizeMask(mask);
      if (normalized == 0)
      {
        return;
      }
      if (maskIndexCache.count(normalized) > 0)
      {
        return;
      }
      int index = static_cast<int>(maskCatalog.size());
      maskCatalog.push_back(normalized);
      maskIndexCache[normalized] = index;
      unsigned bw = bitWidth();
      Expr maskExpr = bvnum(lexical_cast<mpz_class>(normalized), bw, m_efac);
      maskCatalogE.push_back(maskExpr);
      ensureWeight(maskMaskWeights, index);
    }

    void buildCoefficientCatalog()
    {
      coefIndexCache.clear();
      std::vector<cpp_int> seeds = intCoefs;
      intCoefs.clear();
      intCoefsE.clear();

      auto addCoef = [&](const cpp_int &c)
      {
        ensureCoefCached(c);
      };

      addCoef(cpp_int(1));
      addCoef(cpp_int(-1));

      if (_config.coefScheme == BVCoefScheme::PlusMinusOneTwo ||
          _config.coefScheme == BVCoefScheme::SeededFallback)
      {
        addCoef(cpp_int(2));
        addCoef(cpp_int(-2));
      }

      if (_config.coefScheme == BVCoefScheme::PowersOfTwo ||
          _config.coefScheme == BVCoefScheme::SeededFallback)
      {
        unsigned maxPow = std::max(1u, bitWidth());
        for (unsigned p = 1; p < maxPow; p++)
        {
          cpp_int val = cpp_int(1) << p;
          addCoef(val);
          addCoef(-val);
        }
      }

      for (auto &seed : seeds)
      {
        addCoef(seed);
      }
    }

    void buildMaskCatalog()
    {
      maskIndexCache.clear();
      maskCatalog.clear();
      maskCatalogE.clear();
      if (_config.maskCatalog.empty())
      {
        unsigned bw = bitWidth();
        if (bw == 0)
        {
          ensureMaskCached(cpp_int(1));
          return;
        }
        cpp_int fullMask = (cpp_int(1) << bw) - 1;
        ensureMaskCached(fullMask);
        unsigned singleLimit = std::min(bw, 8u);
        for (unsigned bit = 0; bit < singleLimit; ++bit)
        {
          ensureMaskCached(cpp_int(1) << bit);
        }
        std::vector<unsigned> blockSizes = {2u, 4u, 8u};
        for (unsigned block : blockSizes)
        {
          if (block > bw)
          {
            continue;
          }
          unsigned maxOffset = (bw > block) ? std::min(bw - block + 1, 8u) : 1u;
          for (unsigned offset = 0; offset < maxOffset; ++offset)
          {
            cpp_int blockMask = ((cpp_int(1) << block) - 1) << offset;
            ensureMaskCached(blockMask);
          }
        }
        if (bw > 1)
        {
          cpp_int evenMask = 0;
          cpp_int oddMask = 0;
          for (unsigned bit = 0; bit < bw; ++bit)
          {
            if (bit % 2 == 0)
            {
              evenMask |= cpp_int(1) << bit;
            }
            else
            {
              oddMask |= cpp_int(1) << bit;
            }
          }
          ensureMaskCached(evenMask);
          ensureMaskCached(oddMask);
        }
        return;
      }
      for (auto &mask : _config.maskCatalog)
      {
        ensureMaskCached(mask);
      }
    }

    void buildComparatorTemplates()
    {
      comparatorInfo.clear();
      unsigned bw = bitWidth();
      auxVarLhs = bind::mkConst(mkTerm<std::string>("__deephorn_bv_lhs", m_efac),
                                bv::bvsort(bw, m_efac));
      auxVarRhs = bind::mkConst(mkTerm<std::string>("__deephorn_bv_rhs", m_efac),
                                bv::bvsort(bw, m_efac));

      auto addCmp = [&](Expr templ, BVComparatorKind kind)
      {
        comparatorInfo.push_back({templ, kind});
      };

      addCmp(mk<EQ>(auxVarLhs, auxVarRhs), BVComparatorKind::Eq);
      addCmp(mk<NEQ>(auxVarLhs, auxVarRhs), BVComparatorKind::Neq);
      addCmp(mk<BULT>(auxVarLhs, auxVarRhs), BVComparatorKind::Ult);
      addCmp(mk<BULE>(auxVarLhs, auxVarRhs), BVComparatorKind::Ule);
      addCmp(mk<BUGT>(auxVarLhs, auxVarRhs), BVComparatorKind::Ugt);
      addCmp(mk<BUGE>(auxVarLhs, auxVarRhs), BVComparatorKind::Uge);
    }

    void initVarCombinations()
    {
      varCombinations.clear();
      varCombinations.push_back(std::vector<std::set<int>>());
      if (vars.empty()) return;
      std::vector<int> indexes;
      for (unsigned i = 0; i < vars.size(); i++)
      {
        indexes.push_back(static_cast<int>(i));
      }
      for (unsigned size = 1; size <= vars.size(); size++)
      {
        std::vector<std::set<int>> combs;
        getCombinations(indexes, 0, size, combs);
        varCombinations.push_back(combs);
      }
    }

    Expr mkComparator(const BVterm &term, Expr lhs, Expr rhs) const
    {
      assert(term.comparator >= 0);
      assert(static_cast<size_t>(term.comparator) < comparatorInfo.size());
      Expr templ = comparatorInfo[term.comparator].templ;
      Expr res = templ;
      res = replaceAll(res, auxVarLhs, lhs);
      res = replaceAll(res, auxVarRhs, rhs);
      return res;
    }

    Expr buildModularExpr(const BVterm &term) const
    {
      ExprVector summands;
      for (auto &vc : term.varCoefs)
      {
        assert(vc.varIndex >= 0 && static_cast<size_t>(vc.varIndex) < vars.size());
        assert(vc.coefKind >= 0 && static_cast<size_t>(vc.coefKind) < intCoefsE.size());
        Expr coefExpr = intCoefsE[vc.coefKind];
        Expr varExpr = vars[vc.varIndex];
        summands.push_back(mk<BMUL>(coefExpr, varExpr));
      }
      Expr zero = bvnum(mpz_class(0), bitWidth(), m_efac);
      Expr lhs = summands.empty() ? zero : mkb<BADD>(summands, zero);
      Expr rhs = zero;
      if (term.constIndex >= 0 && static_cast<size_t>(term.constIndex) < intConstsE.size())
      {
        rhs = intConstsE[term.constIndex];
      }
      return mkComparator(term, lhs, rhs);
    }

    Expr buildMaskExpr(const BVterm &term) const
    {
      assert(term.varIndex >= 0 && static_cast<size_t>(term.varIndex) < vars.size());
      assert(term.maskIndex >= 0 && static_cast<size_t>(term.maskIndex) < maskCatalogE.size());
      assert(term.valueIndex >= 0 && static_cast<size_t>(term.valueIndex) < intConstsE.size());
      Expr varExpr = vars[term.varIndex];
      Expr maskExpr = maskCatalogE[term.maskIndex];
      Expr valueExpr = intConstsE[term.valueIndex];
      Expr masked = mk<BAND>(varExpr, maskExpr);
      return mk<EQ>(masked, valueExpr);
    }

    Expr buildRangeExpr(const BVterm &term) const
    {
      assert(term.varIndex >= 0 && static_cast<size_t>(term.varIndex) < vars.size());
      Expr varExpr = vars[term.varIndex];
      Expr lower = term.rangeInfo.lowerConst >= 0 && static_cast<size_t>(term.rangeInfo.lowerConst) < intConstsE.size()
                     ? intConstsE[term.rangeInfo.lowerConst]
                     : bvnum(mpz_class(0), bitWidth(), m_efac);
      Expr upper = term.rangeInfo.upperConst >= 0 && static_cast<size_t>(term.rangeInfo.upperConst) < intConstsE.size()
                     ? intConstsE[term.rangeInfo.upperConst]
                     : bvnum(mpz_class(0), bitWidth(), m_efac);
      Expr lowerCmp;
      Expr upperCmp;
      if (term.rangeInfo.signedSemantics)
      {
        lowerCmp = mk<BSGE>(varExpr, lower);
        upperCmp = mk<BSLE>(varExpr, upper);
      }
      else
      {
        lowerCmp = mk<BUGE>(varExpr, lower);
        upperCmp = mk<BULE>(varExpr, upper);
      }
      return mk<AND>(lowerCmp, upperCmp);
    }

    Expr buildUnaryExpr(const BVterm &term) const
    {
      assert(term.varIndex >= 0 && static_cast<size_t>(term.varIndex) < vars.size());
      Expr base = vars[term.varIndex];
      Expr transformed = base;
      switch (term.unaryInfo.op)
      {
        case BVUnaryOp::Not:
          transformed = bv::bvnot(base);
          break;
        case BVUnaryOp::Neg:
          transformed = mk<BNEG>(base);
          break;
        default:
          break;
      }
      Expr value = term.unaryInfo.constIndex >= 0 && static_cast<size_t>(term.unaryInfo.constIndex) < intConstsE.size()
                     ? intConstsE[term.unaryInfo.constIndex]
                     : bvnum(mpz_class(0), bitWidth(), m_efac);
      return mk<EQ>(transformed, value);
    }

    Expr buildBinaryExpr(const BVterm &term) const
    {
      assert(term.varIndex >= 0 && static_cast<size_t>(term.varIndex) < vars.size());
      assert(term.varIndex2 >= 0 && static_cast<size_t>(term.varIndex2) < vars.size());
      assert(term.binaryOp >= 0);
      assert(term.valueIndex >= 0 && static_cast<size_t>(term.valueIndex) < intConstsE.size());
      Expr var1 = vars[term.varIndex];
      Expr var2 = vars[term.varIndex2];
      Expr opExpr;
      switch (static_cast<BVBinaryOp>(term.binaryOp))
      {
        case BVBinaryOp::Add:
          opExpr = mk<BADD>(var1, var2);
          break;
        case BVBinaryOp::Sub:
          opExpr = mk<BSUB>(var1, var2);
          break;
        case BVBinaryOp::And:
          opExpr = mk<BAND>(var1, var2);
          break;
        case BVBinaryOp::Or:
          opExpr = mk<BOR>(var1, var2);
          break;
        case BVBinaryOp::Xor:
          opExpr = mk<BXOR>(var1, var2);
          break;
      }
      Expr value = intConstsE[term.valueIndex];
      return mk<EQ>(opExpr, value);
    }

    Expr buildBinaryCmp(const BVterm &term) const
    {
      assert(term.varIndex >= 0 && static_cast<size_t>(term.varIndex) < vars.size());
      assert(term.varIndex2 >= 0 && static_cast<size_t>(term.varIndex2) < vars.size());
      assert(term.binaryCmp >= 0);
      Expr var1 = vars[term.varIndex];
      Expr var2 = vars[term.varIndex2];
      switch (term.binaryCmp)
      {
        case 0:
          return mk<BULT>(var1, var2);
        case 1:
          return mk<BULE>(var1, var2);
        case 2:
          return mk<BUGT>(var1, var2);
        case 3:
          return mk<BUGE>(var1, var2);
      }
      return mk<TRUE>(m_efac);
    }

    Expr buildNaryExpr(const BVterm &term) const
    {
      assert(term.naryOp >= 0);
      assert(!term.varIndices.empty());
      ExprVector operands;
      for (int idx : term.varIndices)
      {
        assert(idx >= 0 && static_cast<size_t>(idx) < vars.size());
        operands.push_back(vars[idx]);
      }
      Expr opExpr;
      switch (static_cast<BVNaryOp>(term.naryOp))
      {
        case BVNaryOp::And:
          opExpr = mkb<BAND>(operands, bvnum(mpz_class(0), bitWidth(), m_efac));
          break;
        case BVNaryOp::Or:
          opExpr = mkb<BOR>(operands, bvnum(mpz_class(0), bitWidth(), m_efac));
          break;
        case BVNaryOp::Xor:
          opExpr = mkb<BXOR>(operands, bvnum(mpz_class(0), bitWidth(), m_efac));
          break;
      }
      assert(term.valueIndex >= 0 && static_cast<size_t>(term.valueIndex) < intConstsE.size());
      Expr value = intConstsE[term.valueIndex];
      return mk<EQ>(opExpr, value);
    }

    BVterm sampleMaskTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::MaskEquality;
      for (int attempt = 0; attempt < 4; ++attempt)
      {
        term.varIndex = chooseByWeight(maskVarWeights);
        term.maskIndex = chooseByWeight(maskMaskWeights);
        term.valueIndex = pickMaskCompatibleValue(term.maskIndex);
        if (!maskTermSeenRecently(term))
        {
          break;
        }
        nudgeMaskWeights(term);
      }
      shapeWeights[static_cast<int>(BVTermShape::MaskEquality)]++;
      return term;
    }

    BVterm sampleRangeTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::Range;
      term.varIndex = chooseByWeight(rangeVarWeights);
      term.rangeInfo.signedSemantics = chooseByWeight(rangeSignWeights) == 1;
      term.rangeInfo.lowerConst = chooseByWeight(rangeLowerWeights);
      term.rangeInfo.upperConst = chooseByWeight(rangeUpperWeights);
      shapeWeights[static_cast<int>(BVTermShape::Range)]++;
      return term;
    }

    BVterm sampleModularTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::ModularSum;
      if (vars.empty())
      {
        return term;
      }
      int comboSize = chooseByWeight(modularVarComboWeights);
      if (comboSize < 1 || static_cast<size_t>(comboSize) >= varCombinations.size())
      {
        comboSize = 1;
      }
      auto &combSet = varCombinations[comboSize];
      if (combSet.empty())
      {
        BVVarCoef vc;
        vc.varIndex = chooseByWeight(rangeVarWeights);
        vc.coefKind = chooseByWeight(modularCoefWeights);
        term.varCoefs.push_back(vc);
      }
      else
      {
        int combIndex = guessUniformly(static_cast<int>(combSet.size()));
        const std::set<int> &varsChosen = combSet[combIndex];
        for (int v : varsChosen)
        {
          BVVarCoef vc;
          vc.varIndex = v;
          vc.coefKind = chooseByWeight(modularCoefWeights);
          term.varCoefs.push_back(vc);
        }
      }
      term.constIndex = chooseByWeight(modularConstWeights);
      term.comparator = chooseByWeight(modularComparatorWeights);
      shapeWeights[static_cast<int>(BVTermShape::ModularSum)]++;
      return term;
    }

    BVterm sampleUnaryTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::Unary;
      term.varIndex = chooseByWeight(unaryVarWeights);
      int opKey = chooseByWeight(unaryOpWeights);
      term.unaryInfo.op = (opKey == 0) ? BVUnaryOp::Not : BVUnaryOp::Neg;
      term.unaryInfo.constIndex = chooseByWeight(maskValueWeights);
      shapeWeights[static_cast<int>(BVTermShape::Unary)]++;
      return term;
    }

    BVterm sampleBinaryExprTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::BinaryExpr;
      term.varIndex = chooseByWeight(rangeVarWeights);
      do
      {
        term.varIndex2 = chooseByWeight(rangeVarWeights);
      } while (term.varIndex2 == term.varIndex && vars.size() > 1);
      term.binaryOp = chooseByWeight(binaryOpWeights);
      term.valueIndex = chooseByWeight(maskValueWeights);
      shapeWeights[static_cast<int>(BVTermShape::BinaryExpr)]++;
      return term;
    }

    BVterm sampleBinaryCmpTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::BinaryCmp;
      term.varIndex = chooseByWeight(rangeVarWeights);
      do
      {
        term.varIndex2 = chooseByWeight(rangeVarWeights);
      } while (term.varIndex2 == term.varIndex && vars.size() > 1);
      term.binaryCmp = chooseByWeight(binaryCmpWeights);
      shapeWeights[static_cast<int>(BVTermShape::BinaryCmp)]++;
      return term;
    }

    BVterm sampleNaryExprTerm()
    {
      BVterm term(bitWidth());
      term.shape = BVTermShape::NaryExpr;
      int numVars = guessUniformly(3) + 3; // 3 to 5 vars
      numVars = std::min(numVars, static_cast<int>(vars.size()));
      std::set<int> chosen;
      while (static_cast<int>(chosen.size()) < numVars)
      {
        int idx = chooseByWeight(rangeVarWeights);
        chosen.insert(idx);
      }
      for (int idx : chosen)
      {
        term.varIndices.push_back(idx);
      }
      term.naryOp = chooseByWeight(naryOpWeights);
      term.valueIndex = chooseByWeight(maskValueWeights);
      shapeWeights[static_cast<int>(BVTermShape::NaryExpr)]++;
      return term;
    }

    void ensureWeight(density &den, int key)
    {
      if (den.count(key) == 0 || den[key] <= 0)
      {
        den[key] = 1;
      }
    }

    void visitExpr(Expr e)
    {
      if (!e) return;
      if (isOpX<BULT>(e)) {
        chcBinaryCmpFreq[0]++;
      } else if (isOpX<BULE>(e)) {
        chcBinaryCmpFreq[1]++;
      } else if (isOpX<BUGT>(e)) {
        chcBinaryCmpFreq[2]++;
      } else if (isOpX<BUGE>(e)) {
        chcBinaryCmpFreq[3]++;
      } else if (isOpX<BADD>(e)) {
        chcBinaryOpFreq[0]++;
        chcArities[e->arity()]++;
      } else if (isOpX<BSUB>(e)) {
        chcBinaryOpFreq[1]++;
        chcArities[e->arity()]++;
      } else if (isOpX<BAND>(e)) {
        chcBinaryOpFreq[2]++;
        chcArities[e->arity()]++;
      } else if (isOpX<BOR>(e)) {
        chcBinaryOpFreq[3]++;
        chcArities[e->arity()]++;
      } else if (isOpX<BXOR>(e)) {
        chcBinaryOpFreq[4]++;
        chcArities[e->arity()]++;
      } else if (isOpX<AND>(e) || isOpX<OR>(e) || isOpX<XOR>(e)) {
        if (isOpX<AND>(e)) chcNaryOpFreq[0]++;
        else if (isOpX<OR>(e)) chcNaryOpFreq[1]++;
        else if (isOpX<XOR>(e)) chcNaryOpFreq[2]++;
        chcArities[e->arity()]++;
      }
      if (is_bvnum(e)) {
        chcConsts.insert(exprToInt(e));
      }
      for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it) {
        visitExpr(*it);
      }
    }

    void analyzeCHC()
    {
      if (!m_chcs) return;
      for (auto &rule : *m_chcs) {
        visitExpr(rule.body);
      }
    }

    void computeDefaultWeights()
    {
      if (shapeWeights.empty())
      {
        shapeWeights[static_cast<int>(BVTermShape::MaskEquality)] = 0;
        shapeWeights[static_cast<int>(BVTermShape::Range)] = 1;
        shapeWeights[static_cast<int>(BVTermShape::ModularSum)] = 1;
        shapeWeights[static_cast<int>(BVTermShape::Unary)] = 1;
        shapeWeights[static_cast<int>(BVTermShape::BinaryExpr)] = 4;
        shapeWeights[static_cast<int>(BVTermShape::BinaryCmp)] = 4;
        shapeWeights[static_cast<int>(BVTermShape::NaryExpr)] = 4;
      }
      if (!_config.shapeSeeds.empty())
      {
        for (auto &kv : _config.shapeSeeds)
        {
          shapeWeights[kv.first] += kv.second;
        }
      }
      for (unsigned i = 0; i < vars.size(); i++)
      {
        ensureWeight(maskVarWeights, static_cast<int>(i));
        ensureWeight(rangeVarWeights, static_cast<int>(i));
        ensureWeight(unaryVarWeights, static_cast<int>(i));
      }
      for (unsigned i = 0; i < maskCatalog.size(); i++)
      {
        ensureWeight(maskMaskWeights, static_cast<int>(i));
      }
      for (unsigned i = 0; i < intConsts.size(); i++)
      {
        ensureWeight(maskValueWeights, static_cast<int>(i));
        ensureWeight(rangeLowerWeights, static_cast<int>(i));
        ensureWeight(rangeUpperWeights, static_cast<int>(i));
        ensureWeight(modularConstWeights, static_cast<int>(i));
      }
      for (unsigned i = 0; i < intCoefs.size(); i++)
      {
        ensureWeight(modularCoefWeights, static_cast<int>(i));
      }
      ensureWeight(rangeSignWeights, 0);
      ensureWeight(rangeSignWeights, 1);
      for (unsigned i = 0; i < comparatorInfo.size(); i++)
      {
        ensureWeight(modularComparatorWeights, static_cast<int>(i));
      }
      for (unsigned size = 1; size < varCombinations.size(); size++)
      {
        ensureWeight(modularVarComboWeights, static_cast<int>(size));
      }
  ensureWeight(unaryOpWeights, 0);
  ensureWeight(unaryOpWeights, 1);
  for (int i = 0; i < 5; i++)
  {
    ensureWeight(binaryOpWeights, i);
  }
  binaryOpWeights[0] = 5; // Boost Add
  binaryOpWeights[1] = 5; // Boost Sub
  for (int i = 0; i < 4; i++)
  {
    ensureWeight(binaryCmpWeights, i);
  }
  for (int i = 0; i < 3; i++)
  {
    ensureWeight(naryOpWeights, i);
  }

    // Boost based on CHC analysis
    for (auto &kv : chcBinaryOpFreq) {
      ensureWeight(binaryOpWeights, kv.first);
      binaryOpWeights[kv.first] += kv.second * 2;
    }
    for (auto &kv : chcBinaryCmpFreq) {
      ensureWeight(binaryCmpWeights, kv.first);
      binaryCmpWeights[kv.first] += kv.second * 2;
    }
    for (auto &kv : chcNaryOpFreq) {
      ensureWeight(naryOpWeights, kv.first);
      naryOpWeights[kv.first] += kv.second * 2;
    }
    // For arities, boost shapes
    if (chcArities.count(2) > 0) {
      shapeWeights[static_cast<int>(BVTermShape::BinaryExpr)] += chcArities[2] * 2;
      shapeWeights[static_cast<int>(BVTermShape::BinaryCmp)] += chcArities[2] * 2;
    }
    for (auto &kv : chcArities) {
      if (kv.first > 2) {
        shapeWeights[static_cast<int>(BVTermShape::NaryExpr)] += kv.second * 2;
      }
    }
    // For constants, add them if not present
    for (auto &c : chcConsts) {
      addConst(c);
    }
    }

  };

}

#endif // BVCOM__HPP__
