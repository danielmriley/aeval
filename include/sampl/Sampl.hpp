#ifndef SAMPL__HPP__
#define SAMPL__HPP__

#include "deep/Distribution.hpp"
#include "deep/Horn.hpp"
#include "ae/ExprSimpl.hpp"
#include "LinCom.hpp"
#include "BoolCom.hpp"
#include "ArrCom.hpp"
#include "BvCom.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // wrapper for LinCom.hpp, BoolCom.hpp, etc (in the future)
  class Sampl
  {
    public:

    Bdisj b_part;
    LAdisj l_part;
    BVdisj bv_part;

    int arity()
    {
      return l_part.arity + ((b_part.arity > 0) ? 1 : 0) + bv_part.arity;
    }

    bool empty() { return arity() == 0; }

    Sampl() {}

  };

  class SamplFactory
  {
    private:
    ExprFactory &m_efac;

    vector<Sampl> samples;

    density hasBooleanComb;
    density orAritiesDensity;
    bool hasArrays = false;
    bool hasBV = false;

    public:

    LAfactory lf;
    Bfactory bf;
    ARRfactory af;
    BVfactory bvf;

    ExprSet learnedExprs;

    int initialized = 0;  

    SamplFactory(ExprFactory &_efac, bool aggp, const std::vector<HornRuleExt> &chcs = std::vector<HornRuleExt>()) :
      m_efac(_efac), lf(_efac, aggp), bf(_efac), af(_efac, aggp), bvf(_efac, aggp, chcs) {}

    Expr getAllLemmas()
    {
      return conjoin(learnedExprs, m_efac);
    }
    
    void setHasBV(bool hbv)
    {
      hasBV = hbv;
    }

    bool addVar(Expr var)
    {
      bool added = false;
      if (bind::isBoolConst(var))
      {
        bf.addVar(var);
        added = true;
      }
      else if (bind::isIntConst(var))
      {
        lf.addVar(var);
        added = true;
      }
      else if (is_bvconst(var))
      {
        bvf.addVar(var);
        added = true;
        setHasBV(true);
      }
      else if (bind::isConst<ARRAY_TY> (var))
      {
        af.addVar(var);
        added = true;
        hasArrays = true;
      }
      return added;
    }

    void initialize(ExprSet& arrCands, ExprVector& arrAccessVars, ExprSet& arrRange, int bw = 0)
    {
      if(bw > 0)
      {
        setHasBV(true);
        bvf.initialize(bw);
      }
      else
      {
        setHasBV(false);
        lf.initialize();
      }
      bf.initialize();
      if (hasArrays)
      {
        if (!arrAccessVars.empty() && !arrRange.empty())
        {
          af.initialize(lf.getVars(), arrCands, arrAccessVars, arrRange);
          initialized++;
        }
      }
      initialized++;
    }

    Sampl& exprToSampl(Expr ex)
    {
      samples.push_back(Sampl());
      Bdisj& bcs = samples.back().b_part;
      LAdisj& lcs = samples.back().l_part;
      BVdisj& bvcs = samples.back().bv_part;

      bf.exprToBdisj(ex, bcs);
      lf.exprToLAdisj(ex, lcs);
      bvf.exprToBVdisj(ex, bvcs);

      if (!lcs.empty()) lcs.normalizePlus();
      if (!bcs.empty()) bcs.normalizeOr();
      if (!bvcs.empty()) bvcs.normalizePlus();

      return samples.back();
    }

    Expr sampleToExpr(Sampl& s)
    {
      if (s.l_part.arity == 0 && s.b_part.arity == 0 && s.bv_part.arity == 0)
        return NULL;
      if(s.bv_part.arity > 0)
      {
        return bvf.toExpr(s.bv_part);
      }
      if (s.l_part.arity == 0)
        return bf.toExpr(s.b_part);
      if (s.b_part.arity == 0)
        return lf.toExpr(s.l_part);

      return mk<OR>(bf.toExpr(s.b_part), lf.toExpr(s.l_part));
    }

    void calculateStatistics(bool freqs, bool addepsilon)
    {
      int maxArity = 0;
      set<int> orArities;

      if (lf.getVars().size() > 0 && samples.size() == 0 && !hasBV)
      {
        // artificially add one default sample in case there is nothing here
        // TODO: find a better solution
        exprToSampl (mk<GEQ>(lf.getVars()[0], mkTerm (mpz_class (0), m_efac)));
      }
      else if (bvf.getVars().size() > 0 && samples.size() == 0)
      {
        // artificially add one default sample in case there is nothing here
        // TODO: find a better solution
        exprToSampl(mk<BUGE>(bvf.getVars()[0], bvnum(mpz_class(0), bvf.width, m_efac)));
      }

      // outs() << "samples.size() = " << samples.size() << "\n";
      for (auto &s : samples)
      {
        // outs() << "maxArity = " << maxArity << " s.arity() = " << s.arity() << "\n";
        maxArity = max (maxArity, s.arity());
        orArities.insert(s.arity());
        orAritiesDensity[s.arity()] ++;
      }

      for (int i = 0; i < maxArity; i++)
      {
        if (orAritiesDensity[i] == 0)
          orArities.insert(i);
      }

      if(hasBV)
      {
        bvf.initDensities(orArities);
      }
      else 
      {
        lf.initDensities(orArities);
      }
      bf.initDensities();

      for (auto &s : samples)
      {
        LAdisj& l = s.l_part;
        Bdisj& b = s.b_part;
        BVdisj& bv = s.bv_part;

        if (!l.empty())
        {
          lf.calculateStatistics(l, s.arity(), freqs, addepsilon);
        }
        if(!bv.empty())
        {
          bvf.calculateStatistics(bv, s.arity(), freqs, addepsilon);
        }
        if (!b.empty())
        {
          bf.calculateStatistics(b, freqs);
          hasBooleanComb[1]++;
        }
        else
        {
          // frequency of empty bool combinations
          hasBooleanComb[0]++;
        }
      }

      // now, stabilization:

      if (!freqs)
      {
        for (auto & ar : orAritiesDensity)
        {
          ar.second = 1;
        }
      }

      bf.stabilizeDensities(addepsilon, freqs);

      for (auto & ar : orAritiesDensity)
      {
        if(!hasBV)
        {
          lf.stabilizeDensities(ar.first, addepsilon, freqs);
        }
        else
        {
          bvf.stabilizeDensities(ar.first, addepsilon, freqs);
        }
      }

      if (initialized == 2) af.initializeLAfactories();
    }

    Expr getFreshCandidate()
    {
      // for now, if a CHC system has arrays, we try candidates only with array
      // in the future, we will need arithmetic candidates as well
      if (hasArrays && initialized == 2)
      {
        Expr cand = af.getQCand();
        if (cand != NULL)
        {
          for (auto & v : lf.nonlinVars) cand = replaceAll(cand, v.second, v.first);
          return cand;
        }
      }

      if (orAritiesDensity.empty())
      {
        return NULL;
      } 

      int arity = chooseByWeight(orAritiesDensity);
      int hasBool = chooseByWeight(hasBooleanComb);
      int hasLin = arity - hasBool;
      samples.push_back(Sampl());
      Sampl& curCand = samples.back();

      // outs() << "Trying to get a candidate with arity = " << arity
      //        << ", hasBool = " << hasBool << ", hasLin = " << hasLin
      //        << ", hasBV = " << (hasBV ? "1" : "0") << "\n";

      Expr lExpr;
      if (!hasBV && hasLin > 0)
      {
        if (!lf.guessTerm(curCand.l_part, arity, hasLin)) return NULL;
        curCand.l_part.normalizePlus();
        lExpr = lf.toExpr(curCand.l_part);
      }

      Expr bExpr;
      if (hasBool > 0)
      {
        if (!bf.guessTerm(curCand.b_part)) return NULL;
        bExpr = bf.toExpr(curCand.b_part);
      }

      Expr bvExpr;
      if (hasBV /* && hasLin > 0*/)
      {
        if (!bvf.guessTerm(curCand.bv_part, arity, hasLin)) return NULL;
        curCand.bv_part.normalizePlus();
        bvExpr = bvf.toExpr(curCand.bv_part);
      }

      if (hasBool > 0 && hasLin > 0)
      {
        return mk<OR>(bExpr, lExpr);
      }
      else if (hasBool > 0)
      {
        return bExpr;
      }
      else if(hasBV && hasLin > 0)
      {
        return bvExpr;
      }
      else
      {
        return lExpr;
      }
    }

    void assignPrioritiesForLearned(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForLearned(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);

      if (!s.bv_part.empty())
        bvf.assignPrioritiesForLearned(s.bv_part);
    }

    void assignPrioritiesForFailed(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForFailed(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);

      if (!s.bv_part.empty())
        bvf.assignPrioritiesForFailed(s.bv_part);
    }

    void assignPrioritiesForBlocked(Sampl& s)
    {
      if (s.b_part.empty())
        lf.assignPrioritiesForBlocked(s.l_part);

      if (s.l_part.empty())
        bf.assignPrioritiesForBlocked(s.b_part);

      if (!s.bv_part.empty())
        bvf.assignPrioritiesForBlocked(s.bv_part);
    }

    void assignPrioritiesForLearned()
    {
      assignPrioritiesForLearned(samples.back());
    }

    void assignPrioritiesForFailed()
    {
      assignPrioritiesForFailed(samples.back());
    }

    void assignPrioritiesForBlocked()
    {
      assignPrioritiesForBlocked(samples.back());
    }

    void printStatistics()
    {
      for (auto &a : orAritiesDensity)
      {
        outs() << "OR arity density: " << a.first << " |--> " << a.second << "\n";
      }

      bf.printCodeStatistics();

      if (lf.getConsts().size() > 0)
      {
        outs() << "\nInt consts:\n";
        for (auto &form: lf.getConsts()) outs() << lexical_cast<string>(form) << ", ";
        outs() << "\b\b \n";

        for (auto &ar : orAritiesDensity) lf.printCodeStatistics(ar.first);
      }
   
      if(hasBV)
      {
        outs() << "\nInt consts:\n";
        for (auto &form: bvf.getConsts()) outs() << lexical_cast<string>(form) << ", ";
        outs() << "\b\b \n";
        for (auto &ar : orAritiesDensity) bvf.printCodeStatistics(ar.first);
      }
    }

  };
}

#endif
