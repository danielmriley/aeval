#ifndef BVCOM__HPP__
#define BVCOM__HPP__

#define DEFAULT_WIDTH 4
#define PRIORNOVISIT 0
#define PRIORSTEP 30
#define FREQCOEF 15
#define EPSILONFRACTION 5

#include "deep/Distribution.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  typedef std::vector<std::vector<int>> bvcoms;

  class BVterm
  {
    public:
    std::vector<int> vcs;

    unsigned width; // Bit-width of the bit-vector
    int arity;
    int cmpop;
    int intconst;

    BVterm(unsigned w = DEFAULT_WIDTH) : width(w) {}

    int getSize()
    {
      return 3 + 2 * arity;
    }

    void normalizePlus()
    {
      int j;
      map<int, int> varsM;

      for (j = 0; j < vcs.size(); j += 2)
      {
        varsM[vcs[j]] = vcs[j + 1];
      }

      // fill again
      j = 0;

      for (auto &it : varsM)
      {
        vcs[j++] = it.first;
        vcs[j++] = it.second;
      }
    }

    unsigned getWidth() const { return width; }

    void printBVterm()
    {
      outs() << "=== BVterm ===\n";
      outs() << "Bit Width: " << width << "\n";
      outs() << "arity: " << arity << "\n";
      outs() << "cmpop: " << cmpop << "\n";
      outs() << "intconst: " << intconst << "\n";
      outs() << "===============\n";
    }
  };

  inline bool operator==(const BVterm &a, const BVterm &b)
  {
    if (a.arity != b.arity) return false;
    if (a.cmpop != b.cmpop) return false;
    if (a.intconst != b.intconst) return false;
    if (a.width != b.width) return false;

    for (int i = 0; i < a.vcs.size(); i++)
    {
      if (a.vcs[i] != b.vcs[i]) return false;
    }

    return true;
  }

  class BVdisj
  {
    private:
    bvcoms id;

    public:

    std::vector<BVterm> dstate;
    int arity;
    int width;

    BVdisj(int ar = 0, int w = DEFAULT_WIDTH) : arity(ar), width(w) { dstate.resize(arity); }

    bool empty()
    {
      return arity == 0;
    }

    bvcoms& getId()
    {
      if (id.empty())
      {
        for (const auto &term : dstate)
        {
          id.push_back(term.vcs);
        }
      }
      return id;
    }

    void addDisj(const BVterm &s)
    {
      dstate.push_back(s);
      arity++;
    }

    BVterm &newDisj()
    {
      dstate.push_back(BVterm(width)); // Create a new term with default width
      return dstate.back();
    }

    void printBVdisj()
    {
      outs() << "BVdisj: arity = " << arity << "\n";
      for (const auto &s : dstate)
      {
        outs() << "  ** cmpop: " << s.cmpop << "\n";
        outs() << "  ** const: " << s.intconst << "\n";
        outs() << "  ** width: " << s.width << "\n";

        for (int j = 0; j < s.vcs.size(); )
        {
          outs() << "  ** var: " << s.vcs[j++] << "\n";
          outs() << "  ** coef: " << s.vcs[j++] << "\n";
        }
      }
      outs() << "\n";
    }

    void normalizePlus()
    {
      for (auto &s : dstate)
      {
        s.normalizePlus();
      }
    }

    void clear()
    {
      arity = 0;
      dstate.clear();
      id.clear();
    }
  };

  inline void clone(const BVterm &s, BVterm &t)
  {
    t.vcs = s.vcs;
    t.width = s.width;
    t.arity = s.arity;
    t.cmpop = s.cmpop;
    t.intconst = s.intconst;
  }

  inline void clone(const BVdisj &s, BVdisj &t)
  {
    t.arity = s.arity;
    t.dstate.clear();
    for (const auto &term : s.dstate)
    {
      BVterm newTerm(term.getWidth());
      clone(term, newTerm);
      t.addDisj(newTerm);
    }
  }

  inline void dropDisj(BVdisj &s, int ind)
  {
    if (ind < 0 || ind >= s.arity) return;

    s.dstate.erase(s.dstate.begin() + ind);
    s.arity--;
  }

  class BVfactory
  {
    private:

    ExprFactory &m_efac;
    ExprVector vars;

    std::vector<cpp_int> intConsts;
    std::vector<cpp_int> intCoefs;
    std::vector<int> varInds;

    ExprVector intCoefsE;
    ExprVector intConstsE;
    ExprVector cmpOps; // Comparison operators

    Expr auxVar1;
    Expr auxVar2;

    int indexGT; // Index for greater than operator
    int indexGE; // Index for greater than or equal operator

    ExprSet nonlinVarsSet;

    public:

    ExprMap nonlinVars;

    int width = DEFAULT_WIDTH; // Bit-width of the bit-vector
    int prVarsDistrRange;
    std::set<int> orArities;
    std::map<int, density> plusAritiesDensity;
    std::map<int, density> intConstDensity;
    std::map<int, density> cmpOpDensity;
    std::map<int, std::vector<density>> varDensity;
    std::map<int, std::map<int, density>> coefDensity;
    std::vector<std::vector<std::set<int>>> varCombinations;

    std::map<bvcoms, std::vector<weights>> ineqPriors;
    std::map<bvcoms, std::set<int>> visited;
    bool aggressivepruning;

    BVfactory(ExprFactory &efac, bool aggressive = false)
      : m_efac(efac), aggressivepruning(aggressive) {}

    void addVar(Expr var)
    {
      vars.push_back(var);
    }

    void addConst(cpp_int c)
    {
      if(c >= 0) intConsts.push_back(c);
    }

    void addIntCoef(cpp_int coef)
    {
      intCoefs.push_back(coef);
    }

    void initialize(int bw)  // should be called after addVar, addConst, and addIntCoef
    {
      assert(!intCoefs.empty());
      assert(!intConsts.empty());
      assert(!vars.empty());

      width = bw;

      prVarsDistrRange = 2 * intConsts.size();

      // auxiliary variables for inequations:
      auxVar1 = bind::intVar(mkTerm<string>("aux_deephorn_1", m_efac));
      auxVar2 = bind::intVar(mkTerm<string>("aux_deephorn_2", m_efac));

      for (int i = 0; i < vars.size(); i++) varInds.push_back(i);

      // two comparison operators (> and >=), so indexGT < indexGE
      cmpOps.push_back(mk<BUGT>(auxVar1, auxVar2));
      indexGT = cmpOps.size() - 1;

      cmpOps.push_back(mk<BUGE>(auxVar1, auxVar2));
      indexGE = cmpOps.size() - 1;

      // finally, map values to expressions
      for (auto &a : intCoefs) intCoefsE.push_back(bvnum(lexical_cast<mpz_class>(a), width, m_efac));    // assemble expressions
      for (auto &a : intConsts) intConstsE.push_back(bvnum(lexical_cast<mpz_class>(a), width, m_efac));  //

      for (auto &a : nonlinVars) nonlinVarsSet.insert(a.second);
    }

    std::vector<cpp_int>& getConsts()
    {
      return intConsts;
    }

    ExprVector& getVars()
    {
      return vars;
    }

    int getVar(int ind)
    {
      return varInds[ind];
    }

    int getIndexGT()
    {
      return indexGT;
    }

    int getIndexGE()
    {
      return indexGE;
    }

    int switchCmpOp(int ind)
    {
      return (ind == 0) ? 1 : 0;
    }

    cpp_int getIntCoef(int i)
    {
      return intCoefs[i];
    }

    int getIntCoefsSize()
    {
      return intCoefs.size();
    }

    int getCmpOpsSize()
    {
      return cmpOps.size();
    }

    Expr getAtom(Expr templ, Expr var1, Expr var2)
    {
      Expr res = templ;
      res = replaceAll(res, auxVar1, var1);
      res = replaceAll(res, auxVar2, var2);
      return res;
    }

    Expr getAtom(Expr templ, ExprVector& var1, ExprVector& var2)
    {
      ExprSet res;

      for(int i = 0; i < var1.size(); i++)
      {
        for(int j = 0; j < var2.size(); j++)
        {
          res.insert(getAtom(templ, var1[i], var2[j]));
          res.insert(getAtom(templ, var2[j], var1[i]));
        }
      }

      res.insert(getAtom(templ, bvadd(var1), bvadd(var2)));
      res.insert(getAtom(templ, bvadd(var2), bvadd(var1)));
      res.insert(getAtom(templ, bvsub(var1), bvsub(var2)));
      res.insert(getAtom(templ, bvsub(var2), bvsub(var1)));
      return conjoin(res, m_efac);
    }

    bool assembleBvComb(BVterm &s, ExprVector& lhs, ExprVector& rhs)
    {
      for(int i = 0; i < s.vcs.size(); i = i + 2)
      {
        Expr var = vars[s.vcs[i]];
        Expr coefE = intCoefsE[s.vcs[i + 1]];
        cpp_int coef = lexical_cast<cpp_int>(toMpz(coefE));

        if (coef == 0) continue; // skip zero coefficients
        if(coef > 0)
        {
          Expr coefExpr = bvnum(lexical_cast<mpz_class>(coef), width, m_efac);
          lhs.push_back(mk<BMUL>(coefExpr, var));
        }
        else if(coef < 0)
        {
          Expr coefExpr = bvnum(lexical_cast<mpz_class>(-coef), width, m_efac);
          rhs.push_back(mk<BMUL>(coefExpr, var));
        }
        else if(coef == 0)
        {
          Expr coefExpr = bvnum(lexical_cast<mpz_class>(coef), width, m_efac);
          rhs.push_back(mk<BMUL>(coefExpr, var));
        }
        else
        {
          return false;
        }
      }

      return true;
    }

    Expr toExpr(BVterm &s, bool replaceNonLin = true)
    {
      ExprVector lhs, rhs;
      Expr templ = cmpOps[s.cmpop];
      Expr ic = intConstsE[s.intconst];
      if(lexical_cast<cpp_int>(ic->left()) < 0)
      {
        rhs.push_back(additiveInverseBV(ic));
      }
      else if (lexical_cast<cpp_int>(ic->left()) > 0)
      {
        lhs.push_back(ic);
      }
      else if (lexical_cast<cpp_int>(ic->left()) == 0)
      {
        rhs.push_back(ic);
      }

      assembleBvComb(s, lhs, rhs);

      if (lhs.empty())
      {
        lhs.push_back(bvnum(0, width, m_efac));
      }
      if (rhs.empty())
      {
        rhs.push_back(bvnum(0, width, m_efac));
      }

      if(lhs.empty()) outs() << "  ** lhs is empty\n";
      if(rhs.empty()) outs() << "  ** rhs is empty\n";

      Expr ineq = getAtom(templ, lhs, rhs);

      // We need to do some sort of normalization here

      if(replaceNonLin && !nonlinVarsSet.empty())
      {
        while(!emptyIntersect(ineq, nonlinVarsSet))
        {
          // replace non-linear variables with linear ones
          for (auto &v : nonlinVars)
          {
            ineq = replaceAll(ineq, v.second, v.first);
          }
        }
      }
      return ineq;
    }

    Expr toExpr(BVdisj& curCandCode)
    {
      int arity = curCandCode.arity;
      ExprVector disjuncts;

      for(int i = 0; i < arity; i++)
      {
        disjuncts.push_back(toExpr(curCandCode.dstate[i]));
      }
      return disjoin(disjuncts, m_efac);
    }

    void exprToBVdisj(Expr ex, BVdisj& sample)
    {
      if (isOpX<OR>(ex))
      {
        outs() << "Processing expression for BV disjunction: " << ex << "\n";
        for (auto it = ex->args_begin (), end = ex->args_end (); it != end; ++it)
          exprToBVdisj(*it, sample);
      }
      else if (isOpX<BUGE>(ex) || isOpX<BUGT>(ex))
      {
        BVterm s;
        ExprVector all;
        Expr aux;

        outs() << "ex: " << ex << "\n";

        if (is_bvnum(ex->right()))
        {
          outs() << "Right side of comparison is a bit-vector number: " << ex->right() << "\n";
          getAddTermBV(ex->left(), all);
          aux = reBuildCmpBV(ex, auxVar1, auxVar2);
  
  
          // REVISIT. Needs to handle without the LHS assumption.
          // for(auto e = all.begin(); e != all.end(); )
          // {
          //   if(is_bvnum(*e))
          //   {
          //     outs() << "Removing numeric constant: " << *e << "\n";
          //     e = all.erase(e); // remove numeric constants from the left side
          //   }
          //   else
          //   {
          //     ++e;
          //   }
          // }
        }

        if (is_bvnum(ex->left()))
        {
          outs() << "Left side of comparison is a bit-vector number: " << ex->left() << "\n";
          getAddTermBV(ex->right(), all);
          aux = reBuildCmpBV(ex, auxVar1, auxVar2);

          // REVISIT. Needs to handle without the LHS assumption.
          // for (auto e = all.begin(); e != all.end();)
          // {
          //   if (is_bvnum(*e))
          //   {
          //     outs() << "Removing numeric constant: " << *e << "\n";
          //     e = all.erase(e); // remove numeric constants from the left side
          //   }
          //   else
          //   {
          //     ++e;
          //   }
          // }
        }

        s.arity = all.size();
        s.width = width;
        s.cmpop = getVarIndex(aux, cmpOps);
        
        if(is_bvnum(ex->right()))
        {
          s.intconst = getVarIndex(lexical_cast<cpp_int>(toMpz(ex->right())), intConsts);
        }
        if (is_bvnum(ex->left()))
        {
          s.intconst = getVarIndex(lexical_cast<cpp_int>(toMpz(ex->left())), intConsts);
        }
        else
        {
          s.intconst = getVarIndex(lexical_cast<cpp_int>(0), intConsts);
        }

        if (s.intconst == -1 || s.cmpop == -1) { outs() << "RETURNING3\n"; return; }

        for (auto &e : all)
        {
          Expr curVar = NULL;
          cpp_int curCoef = 1;
          bool hasCoef = false;

          ExprVector ops;
          getMultOpsBV (e, ops);
          for (auto & o : ops)
          {
            if (is_bvnum(o))
            {
              curCoef = lexical_cast<cpp_int>(toMpz(o));
              hasCoef = true;
            } 
            else if (curVar != NULL)
            {
              outs() << "Multiple variables in a term, skipping: " << e << "\n";
              return;
            } 
            else curVar = o;
          }

          // If no coefficient was found, ensure it's 1
          if (!hasCoef)
          {
            curCoef = 1;
          }

          int varind = getVarIndex(curVar, vars);
          int coefind = getVarIndex(curCoef, intCoefs);

          // Fallback: If coefind fails (e.g., curCoef == 0), try defaulting to 1 or skip
          if (coefind == -1)
          {
            if (curCoef == 0)
            {
              outs() << "Continuing due to zero coefficient\n";
              // Skip zero-coefficient terms to avoid invalid combinations
              continue;
            }
            // Otherwise, default to 1 if possible
            coefind = getVarIndex(1, intCoefs);
            if (coefind == -1)
            {
              // Add 1 to intCoefs if missing
              intCoefs.push_back(1);
              intCoefsE.push_back(bvnum(lexical_cast<mpz_class>(1), width, m_efac));
              coefind = intCoefs.size() - 1;
            }
          }

          if (varind == -1 || coefind == -1)
          {
            if(varind != -1)
            {
              coefind = (getVarIndex(lexical_cast<cpp_int>(1), intCoefs));
              if(coefind == -1)
              {
                intCoefs.push_back(1);
                intCoefsE.push_back(bvnum(lexical_cast<mpz_class>(1), width, m_efac));
                coefind = intCoefs.size() - 1;
              }
            }
            else
            {
              outs() << "RETURNING4\n";
              return;
            }
          } 

          s.vcs.push_back(varind);
          s.vcs.push_back(coefind);

        }

        for(int v : s.vcs) if (v < 0) { outs() << "RETURNING1\n"; return; } 
        if (s.vcs.size() != 2*(s.arity)) { outs() << "RETURNING2\n"; return; }

        outs() << "Going to addDisjFilter\n";
        addDisjFilter(s, sample);
      }
    }

    cpp_int equalCoefs(BVterm& s)
    {
      cpp_int res = 0;
      for (int i = 0; i < s.vcs.size(); i += 2)
      {
        res += s.vcs[i + 1];
      }
      return res;
    }

    void invertTerm(BVterm& s, BVterm& t)
    {
      t.vcs.clear();
      t.width = s.width;
      t.arity = s.arity;
      t.cmpop = s.cmpop;
      t.intconst = s.intconst;

      for (int i = 0; i < s.vcs.size(); i += 2)
      {
        t.vcs.push_back(s.vcs[i]);
        t.vcs.push_back(-s.vcs[i + 1]); // invert coefficient
      }
    }

    void invertDisj(BVdisj& s, BVdisj& t, int ind)
    {
      t.clear();
      t.arity = s.arity - 1; // one less disjunct

      for (int i = 0; i < s.arity; i++)
      {
        if (i != ind)
        {
          t.addDisj(s.dstate[i]);
        }
        else
        {
          BVterm newTerm;
          invertTerm(s.dstate[i], newTerm);
          t.addDisj(newTerm);
        }
      }
    }

    bool mergeDisj(BVdisj& s1, BVdisj& s2, BVdisj& t)
    {
      t.clear();
      t.arity = s1.arity + s2.arity;

      for (int i = 0; i < s1.arity; i++)
      {
        t.addDisj(s1.dstate[i]);
      }

      for (int i = 0; i < s2.arity; i++)
      {
        t.addDisj(s2.dstate[i]);
      }

      return true; // Assuming merge is always successful
    }

    bool equivBvCom(BVterm& s1, BVterm& s2)
    {
      if (s1.arity != s2.arity) return false;

      // check equivalence of vars
      for (int i = 0; i < s1.vcs.size(); i += 2)
      {
        if (s1.vcs[i] != s2.vcs[i]) return false;
      }

      if (s1.vcs.size() == 2) return (s1.vcs[1] == s2.vcs[1]);

      // finally, coefficients
      if(s2.vcs[1] == 0) return false; // division by zero
      cpp_int c1 = (cpp_int)s1.vcs[1] / (cpp_int)s2.vcs[1];
      if (c1 < 0) return false;
      for (int i = 3; i < s1.vcs.size(); i += 2)
      {
        if(s2.vcs[i] == 0) return false; // division by zero
        cpp_int c2 = (cpp_int)s1.vcs[i] / (cpp_int)s2.vcs[i];
        if (c2 < 0) return false;

        if(c1 != c2) return false; // Ensure coefficients are equal
      }

      return true;
    }

    bool approxRedund(BVterm& s1, BVterm& s2)
    {
      if (s1.arity != s2.arity) return false;

      // check equivalence of vars
      for (int i = 0; i < s1.vcs.size(); i += 2)
      {
        if (s1.vcs[i] != s2.vcs[i]) return false;
      }

      // coefficients must be equal or one must be zero
      cpp_int c1 = s1.vcs[1];
      cpp_int c2 = s2.vcs[1];

      if (c1 == 0 || c2 == 0) return true; // One term is zero

      return (c1 == c2);
    }

    bool stronger(BVterm& s, BVterm& t)
    {
      if (s.vcs.size() != t.vcs.size()) return false;

      for (int i = 0; i < s.vcs.size(); i++)
      {
        if (s.vcs[i] != t.vcs[i]) return false;
      }

      // Ax > b stronger than Ax >= b
      if (s.intconst == t.intconst)
        return (s.cmpop <= t.cmpop); // the smaller index the stronger formula

      // Ax > / >= b stronger than Ax > / >= c iff b > c
      return (s.intconst > t.intconst);
    }

    bool weaker(BVterm& s, BVterm& t)
    {
      if (s.vcs.size() != t.vcs.size()) return false;

      for (int i = 0; i < s.vcs.size(); i++)
      {
        if (s.vcs[i] != t.vcs[i]) return false;
      }

      if (s.intconst == t.intconst)
        return (s.cmpop >= t.cmpop);

      return (s.intconst < t.intconst);
    }

    void getEquivalentFormulas(BVdisj& sample, std::vector<BVdisj>& equivs)
    {
      equivs.push_back(sample);
      bvcoms& id = sample.getId();

      for(int i = 0; i < sample.arity; i++)
      {
        BVterm& s = sample.dstate[i];
        cpp_int intconst = intConsts[s.intconst];
        cpp_int coef = equalCoefs(s);

        if (coef != 0 && coef == intconst)
        {
          for (int j = 0; j < intCoefs.size(); j++)
          {
            auto thisConst = intCoefs[j];
            if (thisConst == coef) continue;
            if ((thisConst < 0) != (coef < 0)) continue;

            int indProg = getVarIndex(thisConst, intConsts);  // GF?
            if (indProg == -1) continue;

            BVdisj c;
            clone(sample, c);
            c.dstate[i].intconst = indProg;
            for (int k = 0; k < c.dstate[i].vcs.size(); k++)
            {
              if (k % 2 == 1) c.dstate[i].vcs[k] = j;
            }
            equivs.push_back(c);
          }
        }
        else if (coef != 0 && 0 == intconst)
        {
          for (int j = 0; j < intCoefs.size(); j++)
          {
            auto thisConst = intCoefs[j];
            if (thisConst == coef) continue;
            if ((thisConst < 0) != (coef < 0)) continue;

            BVdisj c;
            clone(sample, c);
            for (int k = 0; k < c.dstate[i].vcs.size(); k++)
            {
              if (k % 2 == 1) c.dstate[i].vcs[k] = j;
            }
            equivs.push_back(c);
          }
        }
      }
    }

    bool addDisjFilter(BVterm& s, BVdisj& d)
    {
      d.addDisj(s); // add first, then check for redundancy
      return true;

      int skip = false;
      for (int j = 0; j < d.arity; j++)
      {
        BVterm& t = d.dstate[j];
        if (stronger(s, t))
        {          // disjunction of s and t is equal to t, so s can be ignored
          skip = true;
          outs() << "s is stronger than t\n";
          break;
        }
        else if(weaker(s, t))
        {
          // disjunction of s and t is equal to s, so t can be ignored
          t.cmpop = s.cmpop;
          t.intconst = s.intconst;

          skip = true;
          outs() << "s is weaker than t\n";
          break;
        }
        else 
        {
          BVterm u;
          invertTerm(u, s);
          if (stronger(u, s))
          {
            outs() << "s is redundant due to its inverse\n";
            return false;
          }
        }
      }
      if(!skip)
      {
        outs() << "\n** Adding a disjunct\n";
        d.addDisj(s);
      }
      else
      {
        outs() << "Skipping addition of a disjunct\n";
      }
      return true;
    }

    bool guessTerm (BVdisj& curTerm, int arity, int bvArity)
    {
      if(isEmpty(plusAritiesDensity[arity]))
      {
        outs() << "** PLUSARITIES EMPTY **\n";
        return false;
      } 

      std::vector<std::set<int>> varcombs;
      std::vector<BVterm> terms;

      // first, guess var combinations:
      // outs() << "=== guessTerm ===\n";
      // outs() << "arity: " << arity << "\n";
      // outs() << "bvArity: " << bvArity << "\n";

      for(int i = 0; i < bvArity; i++)
      {
        terms.push_back(BVterm(width));
        BVterm& bv = terms.back();
        bv.arity = chooseByWeight(plusAritiesDensity[arity]);
        // outs() << "bv.arity after choosebyWeight 666: " << bv.arity << std::endl;

        std::vector<std::set<int>>& varCombination = varCombinations[bv.arity];
        int comb = chooseByWeight(varDensity[arity][bv.arity]);
        varcombs.push_back(varCombination[comb]);
      }

      // then, guess coefficients to complete the bv. combination

      for(int i = 0; i < bvArity; i++)
      {
        BVterm& bv = terms[i];
        for(int v : varcombs[i])
        {
          bv.vcs.push_back(v);
          int coef = chooseByWeight(coefDensity[arity][v]);
          bv.vcs.push_back(coef);
        }

        if(i != 0)
        {
          for(int j = 0; j < i; j++)
          {
            if(!aggressivepruning && equivBvCom(terms[i], terms[j]))
            {
              // disjunction of i and j is equal to j, so i can be ignored
              return false;
            }
            else if (aggressivepruning&& approxRedund(bv, curTerm.dstate[j]))
            {
              return false;
            }
          }
        }

        curTerm.addDisj(bv);
      }

      // finally, guess comparison operator and int constant

      if(aggressivepruning && isSampleVisitedWeak(curTerm)) return false;
      if(aggressivepruning && isSampleVisitedStrong(curTerm)) return false;

      bvcoms& id = curTerm.getId();

      for(int i = 0; i < bvArity; i++)
      {
        BVterm& bv = curTerm.dstate[i];
        guessNewInequality(id, i, bv, arity);
      }

      return true;
    }

    void guessNewInequality(bvcoms& id, int disj, BVterm& curBVterm, int ar)
    {
      std::vector<weights>& distrs = ineqPriors[id];
      initDistrs(distrs, id.size(), prVarsDistrRange);

      if(!aggressivepruning)
      {
        reInitialize(id, disj); 
      }

      if(isDefault(distrs[disj]))
      {
        curBVterm.cmpop = chooseByWeight(cmpOpDensity[ar]);
        curBVterm.intconst = chooseByWeight(intConstDensity[ar]);

      }
      else
      {
        int ch = chooseByWeight(distrs[disj]);
        double chd = (double)ch / 2;
        curBVterm.intconst = (int)chd;
        curBVterm.cmpop = (ch % 2 == 0) ? getIndexGE() : getIndexGT(); // even -> GE, odd -> GT
      }
    }

    // revisit
    bool isSampleVisitedWeak(BVdisj& disj)
    {
      bvcoms &id = disj.getId();

      if (visited[id].size() > 0)
      {
        return true;
      }
      return false;
    }

    // revisit
    bool isSampleVisitedStrong(BVdisj &disj)
    {
      bvcoms &id = disj.getId();

      if (visited[id].size() == disj.arity)
      {
        return true;
      }
      return false;
    }

    // revisit
    bool isVisited(bvcoms& id, int disj)
    {
      set<int> &s = visited[id];

      if (std::find(std::begin(s), std::end(s), disj) != std::end(s))
      {
        outs() << "visiteed\n";
        return true;
      }

      weights &d = ineqPriors[id][disj];

      if (ineqPriors[id].size() == 0)
      {
        outs() << "WARNING: Priorities are not set up here\n";
        return false;
      }

      for (int i = 0; i < d.size(); i++)
      {
        if (d[i] != PRIORNOVISIT)
        {
          outs() << "WARNING: Priorities are not set up heree\n";
          return false;
        }
      }
      s.insert(disj);
      outs() << "visited\n";
      return true;
    }

    // revisit
    void reInitialize(bvcoms& id, int disj, int def = 1000)
    {
      set<int>& s = visited[id];

      if (s.find(disj) == s.end()) return;

      weights& d = ineqPriors[id][disj];

      for (int i = 0; i < d.size(); i++) d[i] = def;

    }

    // revisit
    void prioritiesBlocked(BVdisj &failed)
    {
      bvcoms& id = failed.getId();
      std::vector<weights>& distrs = ineqPriors[id];

      initDistrs(distrs, failed.arity, prVarsDistrRange);

      for (int i = 0; i < failed.arity; i++)
      {
        BVterm& s = failed.dstate[i];
        distrs[i][s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0)] = PRIORNOVISIT;
        isVisited(id, i);
      }
    }

    // revisit
    void prioritiesFailed(BVdisj &failed)
    {
      bvcoms& id = failed.getId();
      std::vector<weights> &distrs = ineqPriors[id];

      initDistrs(distrs, failed.arity, prVarsDistrRange);

      for (int i = 0; i < failed.arity; i++)
      {
        BVterm &s = failed.dstate[i];

        int lim = s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0);
        for (int j = 0; j < prVarsDistrRange; j++)
        {
          if (j >= lim)
          {
            // block all constants which are greater or equal than intconst
            distrs[i][j] = PRIORNOVISIT;
          }
          else
          {
            // the farther constant from s.intconst the higher priority to visit it later
            distrs[i][j] = min(distrs[i][j], (lim - j) * PRIORSTEP);
          }
        }

        isVisited(id, i);
      }
    }

    // 
    void prioritiesLearned(BVdisj &learned)
    {
      bvcoms& id = learned.getId();
      std::vector<weights>& distrs = ineqPriors[id];

      initDistrs(distrs, learned.arity, prVarsDistrRange);

      for (int i = 0; i < learned.arity; i++)
      {
        BVterm& s = learned.dstate[i];

        int lim = s.intconst * 2 + (getIndexGT() == s.cmpop ? 1 : 0);
        for (int j = 0; j < prVarsDistrRange; j++)
        {
          if (j < lim)
          {
            // block all constants which are less or equal than intconst
            distrs[i][j] = PRIORNOVISIT;
          }
          else
          {
            // the farther constant from intconst the higher priority to visit it later
            distrs[i][j] = std::min(distrs[i][j], (j - lim) * PRIORSTEP);
          }
        }

        isVisited(id, i);
      }
    }

    // 
    void assignPrioritiesForLearned(BVdisj &learned)
    {
      if (!aggressivepruning) return;

      std::vector<BVdisj> eqs;
      getEquivalentFormulas(learned, eqs);
      for (auto &a : eqs) prioritiesLearned(a);

      if (learned.arity == 1)
      {
        BVdisj t;
        invertDisj(learned, t, 0);  // this is guaranteed to fail
        assignPrioritiesForFailed(t);
      }
    }

    void assignPrioritiesForFailed(BVdisj &failed)
    {
      if (!aggressivepruning) return;

      std::vector<BVdisj> eqs;
      getEquivalentFormulas(failed, eqs);
      for (auto &a : eqs) prioritiesFailed(a);
    }

    void assignPrioritiesForBlocked(BVdisj &failed)
    {
      if (!aggressivepruning) return;

      std::vector<BVdisj> eqs;
      getEquivalentFormulas(failed, eqs);
      for (auto &a : eqs) prioritiesBlocked(a);
    }

    void initDensities(set<int>& arities)
    {
      varCombinations.push_back(std::vector<std::set<int>>());

      for(int i = 1; i <= vars.size(); i++)
      {
        varCombinations.push_back(std::vector<std::set<int>>());
        getCombinations(varInds, 0, i, varCombinations.back());
      }

      for (auto ar : arities) initDensities(ar);
    }

    void initDensities(int ar)
    {
      for (int i = 1; i < vars.size() + 1; i++)
      {
        plusAritiesDensity[ar][i] = 0;

        for (int j = 0; j < intCoefs.size(); j++)
        {
          coefDensity[ar][i - 1][j] = 0;
        }
      }

      // Initialize densities for int constants and comparison operators
      for (int i = 0; i < intConsts.size(); i++)
      {
        intConstDensity[ar][i] = 0;
      }

      for (int i = 0; i < cmpOps.size(); i++)
      {
        cmpOpDensity[ar][i] = 0;
      }

      // preparing var densities;
      varDensity[ar].push_back(density());
      for (int i = 1; i <= vars.size(); i++)
      {
        varDensity[ar].push_back(density());
        for(int j = 0; j < varCombinations[i].size(); j++)
        {
          varDensity[ar][i][j] = 0;
        }
      }
    }

    // revisit
    int getEpsilon(int min_freq, int num_zeros)
    {
      if (num_zeros == 0) return 1;

      return 1 + ((min_freq == INT_MAX) ? 0 : (guessUniformly(min_freq) / num_zeros / EPSILONFRACTION));
    }

    // revisit
    void stabilizeDensities(int ar, bool addEpsilon, bool freqs)
    {
      int freqCoef = freqs ? FREQCOEF : 1;
      int min_freq = INT_MAX;
      int num_zeros = 0;
      int eps = 0;

      for (auto & pl : plusAritiesDensity[ar])
      {
        if (pl.second == 0) num_zeros++;
        else
        {
          pl.second *= freqCoef;
          min_freq = min(min_freq, pl.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == plusAritiesDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & pl : plusAritiesDensity[ar])
      {
        if (pl.second == 0) pl.second = eps;
      }

      for (int i = 0; i < vars.size(); i++)
      {
        min_freq = INT_MAX;
        num_zeros = 0;
        for (auto & c : coefDensity[ar][i])
        {
          if (c.second == 0) num_zeros++;
          else
          {
            c.second *= freqCoef;
            min_freq = min(min_freq, c.second);
          }
        }

        if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
          else if (num_zeros == coefDensity[ar][i].size()) eps = 1;
            else eps = 0;

        for (auto & c : coefDensity[ar][i])
        {
          if (c.second == 0) c.second = eps;
        }
      }

      min_freq = INT_MAX;
      num_zeros = 0;
      for (auto & c : intConstDensity[ar])
      {
        if (c.second == 0) num_zeros++;
        else
        {
          c.second *= freqCoef;
          min_freq = min(min_freq, c.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == intConstDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & c : intConstDensity[ar])
      {
        if (c.second == 0) c.second = eps;
      }

      min_freq = INT_MAX;
      num_zeros = 0;
      for (auto & c : cmpOpDensity[ar])
      {
        if (c.second == 0) num_zeros++;
        else
        {
          c.second *= freqCoef;
          min_freq = min(min_freq, c.second);
        }
      }

      if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
        else if (num_zeros == cmpOpDensity[ar].size()) eps = 1;
          else eps = 0;

      for (auto & c : cmpOpDensity[ar])
      {
        if (c.second == 0) c.second = eps;
      }

      for (int i = 0; i < varDensity[ar].size(); i++)
      {
        min_freq = INT_MAX;
        num_zeros = 0;
        for (auto &b : varDensity[ar][i])
        {
          if (b.second == 0) num_zeros++;
          else
          {
            b.second *= freqCoef;
            min_freq = min(min_freq, b.second);
          }
        }

        if (addEpsilon) eps = getEpsilon(min_freq, num_zeros);
          else if (num_zeros == varDensity[ar][i].size()) eps = 1;
            else eps = 0;

        for (auto &b : varDensity[ar][i])
        {
          if (b.second == 0) b.second = eps;
        }
      }
    }

    void calculateStatistics(BVdisj& bvcs, int ar, bool freqs, bool addepsilon)
    {
      if (freqs)
      {
        bvcs.printBVdisj();
        for (auto & bv : bvcs.dstate)
        {
          plusAritiesDensity[ar][bv.arity] ++;
          intConstDensity[ar][bv.intconst] ++;
          cmpOpDensity[ar][bv.cmpop] ++;

          set<int> varsSet;
          int vars_id = -1;
          for (int i = 0; i < bv.vcs.size(); i += 2)
          {
            varsSet.insert(bv.vcs[i]);
          }
          for(int j = 0; j < varCombinations[bv.arity].size(); j++)
          {
            if (varCombinations[bv.arity][j] == varsSet)
            {
              vars_id = j;
              break;
            }
          }
          assert(vars_id >= 0);

          varDensity[ar][bv.arity][vars_id] += 1;
          for(int j = 1; j < bv.vcs.size(); j += 2)
          {
            coefDensity[ar][bv.vcs[j - 1]][bv.vcs[j]] += 1;
          }
        }
      }
      else
      {
        for (auto & bv : bvcs.dstate)
        {
          plusAritiesDensity[ar][bv.arity] = 1;
          intConstDensity[ar][bv.intconst] = 1;
          cmpOpDensity[ar][bv.cmpop] = 1;

          set<int> varsSet;
          int vars_id = -1;
          for (int j = 0; j < bv.vcs.size(); j = j + 2)
          {
            varsSet.insert(bv.vcs[j]);
          }
          bv.printBVterm();
          for(int j = 0; j < varCombinations[bv.arity].size(); j++)
          {
            if (varCombinations[bv.arity][j] == varsSet)
            {
              vars_id = j;
              break;
            }
          }
          assert(vars_id >= 0);

          varDensity[ar][bv.arity][vars_id] += 1;

          for(int j = 1; j < bv.vcs.size(); j += 2)
          {
            coefDensity[ar][bv.vcs[j - 1]][bv.vcs[j]] += 1;
          }
        }
      }
    }

    void printCodeStatistics(int ar)
    {
      outs() << "(OR arity = " << ar << "):\n";

      for (auto &a : plusAritiesDensity[ar])
      {
        outs() << " Plus arity density: " << a.first << " |--> " << a.second << "\n";
      }

      for (auto &a : intConstDensity[ar])
      {
        outs() << " IntConst density: " << *intConstsE[a.first] << " |--> " << a.second << "\n";
      }

      for (auto &a : cmpOpDensity[ar])
      {
        outs() << " Operator density: " << (a.first == indexGT ? "BUGT" : "BUGE") << " |--> " << a.second << "\n";
      }

      for (int i = 0; i < varDensity[ar].size(); i++)
      {
        for (auto &b : varDensity[ar][i])
        {
          outs() << " Var Combination density: ";

          for (int j : varCombinations[i][b.first])
          {
            outs() << *vars[j] << ", ";
          }

          outs() << "\b\b |--> " << b.second << "\n";
        }
      }

      for (int i = 0; i < vars.size(); i++)
      {
        for (int j = 0; j < getIntCoefsSize(); j++)
        {
          outs() << " Var Coefficient density: [" << *intCoefsE[j] << " * "
                 << *vars[i] << "] : " << coefDensity[ar][i][j] << "\n";
        }
      }
    }
  }; // end of BVfactory

} // namespace ufo

#endif // BVCOM__HPP__