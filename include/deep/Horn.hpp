#ifndef HORN__HPP__
#define HORN__HPP__

#include <fstream>
#include <chrono>
#include <iomanip>
#include <sstream>
#include "ae/AeValSolver.hpp"
#include "ae/ExprSimplBv.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  struct HornRuleExt
  {
    ExprVector srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    ExprSet lin;

    ExprVector origSrc;
    ExprVector origDst;
    ExprMap origSrcVars;

    Expr body;

    Expr srcRelation;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;

    void assignVarsAndRewrite (ExprVector& invSrc, ExprVector& invDst)
    {
      for (int i = 0; i < origSrc.size(); i++)
      {
        srcVars.push_back(invSrc[i]);
        lin.insert(mk<EQ>(origSrc[i], srcVars[i]));
      }

      for (int i = 0; i < origDst.size(); i++)
      {
        dstVars.push_back(invDst[i]);
        lin.insert(mk<EQ>(origDst[i], dstVars[i]));
      }
    }

    void shrinkLocVars()
    {
      for (auto it = locVars.begin(); it != locVars.end();)
        if (contains(body, *it)) ++it;
        else it = locVars.erase(it);
    }

    bool splitBody ()
    {
      getConj (simplifyBool(body), lin);
      for (auto c = lin.begin(); c != lin.end(); )
      {
        Expr cnj = *c;
        if (isOpX<FALSE>(cnj)) return false;
        if (isOpX<FAPP>(cnj) && cnj->arity() > 1 && isOpX<FDECL>(cnj->left()))
        {
          Expr rel = cnj->left();
          if (srcRelation != NULL)
          {
            errs () << "Nonlinear CHC is currently unsupported: ["
                    << srcRelation << " /\\ " << rel->left() << " -> "
                    << dstRelation << "]\n";
            exit(1);
          }
          srcRelation = rel->left();
          for (auto it = cnj->args_begin()+1; it != cnj->args_end(); ++it)
            origSrc.push_back(*it);
          c = lin.erase(c);
        }
        else ++c;
      }
      return true;
    }

  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";
    SMTUtils u;

    void initializeCHC(const CHCs& other) {
      indeces = other.indeces;
      failDecl = other.failDecl;
      chcs = other.chcs;
      allCHCs = other.allCHCs;
      wtoCHCs = other.wtoCHCs;
      dwtoCHCs = other.dwtoCHCs;
      wtoDecls = other.wtoDecls;
      decls = other.decls;
      invVars = other.invVars;
      invVarsPrime = other.invVarsPrime;
      outgs = other.outgs;
      cycleSearchDone = other.cycleSearchDone;
      loopheads = other.loopheads;
      cycles = other.cycles;
      prefixes = other.prefixes;
      acyclic = other.acyclic;  
      seqPoints = other.seqPoints;
      hasArrays = other.hasArrays;
      hasAnyArrays = other.hasAnyArrays;
      hasBV = other.hasBV;
      hasQuery = other.hasQuery;
      debug = other.debug;
      chcsToCheck1 = other.chcsToCheck1;
      chcsToCheck2 = other.chcsToCheck2;
      toEraseChcs = other.toEraseChcs;
      glob_ind = other.glob_ind;
      origVrs = other.origVrs;
      
      // Rebuild outgoing edges map
      outgs.clear();
      for (int i = 0; i < chcs.size(); i++) {
        outgs[chcs[i].srcRelation].push_back(i);
      }
      
      // Reset cycle detection
      cycleSearchDone = false;

      // Clear existing pointers
      wtoCHCs.clear();
      dwtoCHCs.clear();

      // Rebuild wtoCHCs by matching source/destination relations
      for (size_t i = 0; i < chcs.size(); i++) {
        // Try to find corresponding rule in original wtoCHCs
        for (auto wto : other.wtoCHCs) {
          if (wto && wto->srcRelation == chcs[i].srcRelation && 
              wto->dstRelation == chcs[i].dstRelation) {
            wtoCHCs.push_back(&chcs[i]);
            // Also add to dwtoCHCs if not a query
            if (!chcs[i].isQuery) {
              dwtoCHCs.push_back(&chcs[i]);
            }
            break;
          }
        }
      }

      if (debug >= 3) {
        outs() << "Rebuilt wtoCHCs with " << wtoCHCs.size() << " rules\n";
        outs() << "Rebuilt dwtoCHCs with " << dwtoCHCs.size() << " rules\n";
      }
    }

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    Expr failDecl;
    vector<HornRuleExt> chcs;
    vector<HornRuleExt*> allCHCs;
    vector<HornRuleExt*> wtoCHCs, dwtoCHCs;
    ExprVector wtoDecls;
    ExprSet decls;
    map<Expr, ExprVector> invVars,invVarsPrime;
    map<Expr, vector<int>> outgs;
    bool cycleSearchDone = false;
    ExprVector loopheads;
    map<Expr, vector<vector<int>>> cycles, prefixes;
    vector<vector<int>> acyclic;
    ExprVector seqPoints;
    // vector<vector<int>> prefixes, cycles;  // for cycles
    map<Expr, bool> hasArrays;
    bool hasAnyArrays, hasBV = false;
    bool hasQuery = false;
    int debug;
    set<int> chcsToCheck1, chcsToCheck2, toEraseChcs;
    int glob_ind = 0;
    ExprSet origVrs;

    CHCs(ExprFactory &efac, EZ3 &z3, int d = false) :
      u(efac), m_efac(efac), m_z3(z3), hasAnyArrays(false), debug(d) {};
    CHCs(CHCs const &r) : CHCs(r.m_efac, r.m_z3, r.debug) 
    {
      initializeCHC(r);
    };

    CHCs operator=(CHCs const r)
    {
      initializeCHC(r);
      return *this;
    }

    CHCs operator=(CHCs const *r)
    {
      if (r != nullptr) {
        initializeCHC(*r);
      }
      return *this;
    }

    void reinitialize(const CHCs& other) {
      initializeCHC(other);
    }

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->left()))
            if (e->left()->arity() >= 2)
              return true;
      return false;
    }

    Expr getDeclByName (Expr a) const // Add const here
    {
      for (auto & d : decls)
        if (d->left() == a) return d;
      return NULL;
    }

    bool addedDecl (Expr a) const // Add const here too for consistency
    {
      return getDeclByName(a) != NULL;
    }

    void addDecl (Expr a)
    {
      if (invVars[a->left()].size() == 0)
      {
        decls.insert(a);
        int j = 0;
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY>(arg) && !isOpX<REAL_TY>(arg) &&
              !isOpX<BOOL_TY>(arg) && !isOpX<ARRAY_TY>(arg) &&
              !isOpX<BVSORT> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          while (true)
          {
            Expr name = mkTerm<string> (varname + to_string(j), m_efac);
            Expr var = fapp (constDecl (name, arg));
            name = mkTerm<string> (lexical_cast<string>(name) + "'", m_efac);
            Expr varPr = fapp (constDecl (name, arg));
            j++;
            if (find(origVrs.begin(), origVrs.end(), var) != origVrs.end())
              continue;
            if (find(origVrs.begin(), origVrs.end(), varPr) != origVrs.end())
              continue;
            invVars[a->left()].push_back(var);
            invVarsPrime[a->left()].push_back(varPr);
            break;
          }
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 &&
               isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      // small rewr
      if (isOpX<IMPL>(r) && isOpX<ITE>(r->right()))
      {
        return true;
      }

      if (isOpX<IMPL>(r) && isOpX<IMPL>(r->right()))
      {
        r = mk<IMPL>(mk<AND>(r->left(), r->right()->left()), r->right()->right());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool parse(string smt, bool doElim = true, bool doArithm = true)
    {
      using namespace std::chrono;
      auto totalParseStart = high_resolution_clock::now();
      
      if (debug > 0) outs () << "\nPARSING" << "\n=======\n";
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      
      auto loadStart = high_resolution_clock::now();
      fp.loadFPfromFile(smt);
      auto loadEnd = high_resolution_clock::now();
      auto loadTime = duration_cast<milliseconds>(loadEnd - loadStart).count();
      
      auto processStart = high_resolution_clock::now();
      chcs.reserve(fp.m_rules.size());

      ExprMap eqs;
      for (auto it = fp.m_rules.begin(); it != fp.m_rules.end(); )
      {
        if (isOpX<EQ>(*it))
        {
          eqs[(*it)->left()->left()] = (*it)->right()->left();
          it = fp.m_rules.erase(it);
        }
        else ++it;
      }

      for (auto &r: fp.m_rules)
      {
        hasAnyArrays |= containsOp<ARRAY_TY>(r);
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();
        while (true)
        {
          auto r1 = replaceAll(r, eqs);
          if (r == r1) break;
          else r = r1;
        }

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        filter (r, bind::IsConst(), inserter (origVrs, origVrs.begin()));
        // small rewr:
        if (isOpX<ITE>(r->last()))
        {
          hr.body = mk<IMPL>(mk<AND>(r->left(), r->last()->left()),
                             r->last()->right());
          chcs.push_back(chcs.back());
          chcs.back().body = mk<IMPL>(mk<AND>(r->left(), mkNeg(r->last()->left())),
                             r->last()->last());
        }
        else
        {
          hr.body = r;
        }
      }
      auto processEnd = high_resolution_clock::now();
      auto processTime = duration_cast<milliseconds>(processEnd - processStart).count();

      auto setupStart = high_resolution_clock::now();
      for (auto & hr : chcs)
      {
        Expr head = hr.body->right();
        hr.body = hr.body->left();
        if (isOpX<FAPP>(head))
        {
          if (head->left()->arity() == 2 &&
              (find(fp.m_queries.begin(), fp.m_queries.end(), head) !=
               fp.m_queries.end()))
            addFailDecl(head->left()->left());
          else
            addDecl(head->left());
          hr.dstRelation = head->left()->left();
          for (auto it = head->args_begin()+1; it != head->args_end(); ++it)
            hr.dstVars.push_back(*it); // to be rewritten later
        }
        else
        {
          if (!isOpX<FALSE>(head)) hr.body = mk<AND>(hr.body, mk<NEG>(head));
          addFailDecl(mk<FALSE>(m_efac));
          hr.dstRelation = mk<FALSE>(m_efac);
        }
        hasBV |= containsOp<BVSORT>(hr.body);
      }
      auto setupEnd = high_resolution_clock::now();
      auto setupTime = duration_cast<milliseconds>(setupEnd - setupStart).count();

      if (debug > 0) outs () << "Reserved space for " << chcs.size()
                          << " CHCs and " << decls.size() << " declarations\n";

      // the second loop is needed because we want to distinguish
      // uninterpreted functions used as variables
      // from relations to be synthesized
      auto elimStart = high_resolution_clock::now();
      for (auto it = chcs.begin(); it != chcs.end(); )
      {
        // ExprVector origSrcSymbs, origDstSymbs;
        // ExprSet lin;
        HornRuleExt & hr = *it;
        if (!hr.splitBody())
        {
          it = chcs.erase(it);
          continue;
        }
        else ++it;

        if (hr.srcRelation == NULL) hr.srcRelation = mk<TRUE>(m_efac);

        hr.isFact = isOpX<TRUE>(hr.srcRelation);
        hr.isQuery = (hr.dstRelation == failDecl);
        if (hr.isQuery) { hasQuery = true; }
        hr.isInductive = (hr.srcRelation == hr.dstRelation);

        hr.origDst = hr.dstVars;
        hr.dstVars.clear();

        hr.assignVarsAndRewrite (invVars[hr.srcRelation],
                                 invVarsPrime[hr.dstRelation]);

        if (doElim)
        {
          hr.body = eliminateQuantifiers(conjoin(hr.lin, m_efac), hr.locVars,
                                                 !hasBV && doArithm, false);
          hr.body = u.removeITE(hr.body);
          hr.body = simplifyArr(hr.body);
          hr.body = u.removeRedundantConjuncts(hr.body);
          hr.shrinkLocVars();
        }
        else
        {
          // Lightweight mode: skip expensive solver-based simplification
          // but still do essential rewriting
          hr.body = eliminateQuantifiers(conjoin(hr.lin, m_efac), hr.locVars,
                                                 false, false);  // No arithm, no core QE
          hr.body = u.removeITE(hr.body);
          // Skip removeRedundantConjuncts - it's the expensive part
        }
      }
      auto elimEnd = high_resolution_clock::now();
      auto elimTime = duration_cast<milliseconds>(elimEnd - elimStart).count();
      
      auto declElimStart = high_resolution_clock::now();
      if (doElim)
      {
        int sz = chcs.size();
        for (int c = 0; c < chcs.size(); c++)
        {
          chcsToCheck1.insert(c);
          chcsToCheck2.insert(c);
        }
        if (!eliminateDecls()) return false;

        // eliminating all at once,
        // otherwise elements at chcsToCheck* need updates
        for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
          chcs.erase(chcs.begin() + *it);
        toEraseChcs.clear();

        // get rid of vacuous:
        while (true)
        {
          bool toBreak = true;
          for (auto & d : decls)
          {
            set<int> toEraseChcs;
            bool toCont = false;
            for (int c = 0; c < chcs.size(); c++)
            {
              if (chcs[c].dstRelation == d->left())
              {
                toCont = true;
                break;
              }
              if (chcs[c].srcRelation == d->left())
                toEraseChcs.insert(c);
            }
            if (toCont) continue;
            for (auto it = toEraseChcs.rbegin(); it != toEraseChcs.rend(); ++it)
            {
              toBreak = false;
              chcs.erase(chcs.begin() + *it);
            }
          }
          if (toBreak) break;
        }
      }

      for (int i = 0; i < chcs.size(); i++)
        outgs[chcs[i].srcRelation].push_back(i);
      auto declElimEnd = high_resolution_clock::now();
      auto declElimTime = duration_cast<milliseconds>(declElimEnd - declElimStart).count();

      auto cycleStart = high_resolution_clock::now();
      findCycles();
      auto cycleEnd = high_resolution_clock::now();
      auto cycleTime = duration_cast<milliseconds>(cycleEnd - cycleStart).count();

      // prepare a version of wtoCHCs w/o queries
      dwtoCHCs = wtoCHCs;
      for (auto it = dwtoCHCs.begin(); it != dwtoCHCs.end();)
        if ((*it)->isQuery) it = dwtoCHCs.erase(it);
          else ++it;

      auto totalParseEnd = high_resolution_clock::now();
      auto totalParseTime = duration_cast<milliseconds>(totalParseEnd - totalParseStart).count();
      
      outs() << "[Parse Timing] Load: " << loadTime << "ms, "
             << "Process: " << processTime << "ms, "
             << "Setup: " << setupTime << "ms, "
             << "Elim: " << elimTime << "ms, "
             << "DeclElim: " << declElimTime << "ms, "
             << "Cycles: " << cycleTime << "ms, "
             << "Total: " << totalParseTime << "ms\n";

      if (debug >= 1)
      {
        outs () << (doElim ? "  Simplified " : "  Parsed ") << "CHCs:\n";
        print(debug >= 4, true);
      }
      return true;
    }

    bool eliminateTrivTrueOrFalse()
    {
      set<int> toEraseChcsTmp;
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
        if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

        auto c = &chcs[i];
        if (c->isQuery && !c->isFact)
        {
          auto f = find(chcsToCheck1.begin(), chcsToCheck1.end(), i);
          if (f != chcsToCheck1.end())
          {
            if (u.isTrue(c->body))
            {
              // thus, c->srcRelation should be false
              for (int j = 0; j < chcs.size(); j++)
              {
                if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end()) continue;
                if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), j) != toEraseChcsTmp.end()) continue;

                HornRuleExt* s = &chcs[j];
                if (s->srcRelation == c->srcRelation)
                {
                  // search for vacuous cases where s == inv -> inv2   and   c == inv /\ true -> false
                  // then, inv can only be false, thus s does not give any constraint
                  toEraseChcsTmp.insert(j);  // could erase here, but ther will be a mess with pointers
                }
                else if (s->dstRelation == c->srcRelation)
                {
                  s->isQuery = true;
                  s->dstRelation = failDecl;
                  s->locVars.insert(s->locVars.end(), s->dstVars.begin(), s->dstVars.end());
                  s->dstVars.clear();
                  chcsToCheck1.insert(j);
                  chcsToCheck2.insert(j);
                }
              }
              decls.erase(c->srcRelation);
            }
            chcsToCheck1.erase(f);
          }
        }
        else if (c->isQuery && c->isFact)
          if (u.isSat(c->body))
          {
            outs () << "Counterexample found (during preprocessing)\n";
            return false;
          }
      }

      if (toEraseChcsTmp.empty()) return true;

      for (auto it = toEraseChcsTmp.rbegin(); it != toEraseChcsTmp.rend(); ++it)
      {
        if (debug >= 2) outs () << "  Eliminating vacuous CHC: " <<
                chcs[*it].srcRelation << " -> " << chcs[*it].dstRelation << "\n";
        if (debug >= 3) outs () << "    its body is true: " << chcs[*it].body << "\n";
        toEraseChcs.insert(*it);
      }

      return eliminateTrivTrueOrFalse();     // recursive call
    }

    bool eliminateDecls()
    {
      pair<int,int> preElim = {chcs.size() - toEraseChcs.size(), decls.size()};
      if (debug > 0)
        outs () << "Reducing the number of CHCs: " << preElim.first <<
              "; and the number of declarations: " << preElim.second << "...\n";
      if (debug >= 3)
      {
        outs () << "  Current CHC topology:\n";
        print(false);
      }

      Expr declToRemove = NULL;
      vector<int> srcMax, dstMax;
      set<int> toEraseChcsTmp;
      for (auto d = decls.begin(); d != decls.end();)
      {
        vector<int> src, dst;
        for (int i = 0; i < chcs.size(); i++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end()) continue;
          if (find(toEraseChcsTmp.begin(), toEraseChcsTmp.end(), i) != toEraseChcsTmp.end()) continue;

          if (chcs[i].srcRelation == (*d)->left()) src.push_back(i);
          if (chcs[i].dstRelation == (*d)->left()) dst.push_back(i);
        }

        if ((src.size() > 0 && dst.size() > 0) &&
            emptyIntersect(src, dst))
        {

          if (declToRemove != NULL)
            if (declToRemove->arity() > (*d)->arity())
              { ++d; continue; }
          if (declToRemove != NULL)
            if (declToRemove->arity() == (*d)->arity() &&
                src.size() * dst.size() > srcMax.size() * dstMax.size())
              { ++d; continue; }

          srcMax = src;
          dstMax = dst;
          declToRemove = *d;
        }

        if (src.size() == 0) // found dangling CHCs
        {
          toEraseChcsTmp.insert(dst.begin(), dst.end());
          d = decls.erase(d);
        }
        else ++d;
      }

      // first, it will remove dangling CHCs since it's cheaper
      if (declToRemove != NULL && toEraseChcsTmp.empty())
      {
        for (int i : srcMax)
          for (int j : dstMax)
            concatenateCHCs(i, j);

        toEraseChcsTmp.insert(srcMax.begin(), srcMax.end());
        toEraseChcsTmp.insert(dstMax.begin(), dstMax.end());
        decls.erase(declToRemove);
      }

      for (auto a = toEraseChcsTmp.rbegin(); a != toEraseChcsTmp.rend(); ++a)
      {
        if (debug >= 2)
          outs () << "  Eliminating CHC: " << chcs[*a].srcRelation
                  << " -> " << chcs[*a].dstRelation << "\n";
      }

      // get rid of CHCs that don't add any _new_ constraints
      removeTautologies();

      if (preElim.first > (chcs.size() - toEraseChcs.size()) ||
          preElim.second > decls.size())
        return eliminateDecls();
      else
      {
        // remove unrelated constraints and shrink arities of predicates
        // currently disabled
        // if (!hasAnyArrays) slice();

        int preComb = (chcs.size() - toEraseChcs.size());
        combineCHCs();
        if (preComb > (chcs.size() - toEraseChcs.size()))
          return eliminateDecls();
      }
      return true;
    }

    void concatenateCHCs(int i, int j)
    {
      chcs.push_back(HornRuleExt());
      HornRuleExt* s = &chcs[i];
      HornRuleExt* d = &chcs[j];
      HornRuleExt* n = &chcs.back();
      if (debug >= 2)
      {
        outs () << "  Concatenating two CHCs: "
                << d->srcRelation << " -> " << d->dstRelation << " and "
                << s->srcRelation << " -> " << s->dstRelation << "\n";
      }
      n->srcRelation = d->srcRelation;
      n->dstRelation = s->dstRelation;
      n->srcVars = d->srcVars;
      n->dstVars = d->dstVars;

      ExprVector newVars;
      for (int i = 0; i < d->dstVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__bnd_var_" +
          to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->dstVars[i], new_name));
      }
      Expr mergedBody = replaceAll(s->body, s->srcVars, newVars);
      n->dstVars.insert(n->dstVars.end(), d->locVars.begin(), d->locVars.end());
      for (int i = 0; i < d->locVars.size(); i++)
      {
        Expr new_name = mkTerm<string> ("__loc_var_" +
          to_string(glob_ind++), m_efac);
        newVars.push_back(cloneVar(d->locVars[i], new_name));
      }
      mergedBody = mk<AND>(replaceAll(d->body, n->dstVars, newVars), mergedBody);
      n->locVars = newVars;
      n->locVars.insert(n->locVars.end(), s->locVars.begin(), s->locVars.end());
      n->body = simpleQE(mergedBody, n->locVars);
      n->shrinkLocVars();
      n->dstVars = s->dstVars;
      n->isInductive = n->srcRelation == n->dstRelation;
      n->isFact = isOpX<TRUE>(n->srcRelation);
      n->isQuery = n->dstRelation == failDecl;
      chcsToCheck1.insert(chcs.size()-1);
      chcsToCheck2.insert(chcs.size()-1);
    }

    void removeTautologies()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        auto h = &chcs[i];
        auto f = find(chcsToCheck2.begin(), chcsToCheck2.end(), i);
        if (f != chcsToCheck2.end())
        {
          if (u.isFalse(h->body))
          {
            if (debug >= 2)
              outs () << "  Eliminating CHC: " << h->srcRelation
                      << " -> " << h->dstRelation << "\n";
            if (debug >= 3)
              outs () << "    its body is false: " << h->body << "\n";
            toEraseChcs.insert(i);
            continue;
          }
          chcsToCheck2.erase(f);
        }

        bool found = false;
        if (h->isInductive)
        {
          found = true;
          for (int j = 0; j < h->srcVars.size(); j++)
          {
            if (u.isSat(h->body, mkNeg(mk<EQ>(h->srcVars[j], h->dstVars[j]))))
            {
              found = false;
              break;
            }
          }
        }
        if (found && false)
        {
          if (debug >= 2)
            outs () << "  Eliminating CHC: " << h->srcRelation
                    << " -> " << h->dstRelation << "\n";
          if (debug >= 3)
            outs () << "    inductive but does not change vars: "
                    << h->body << "\n";
          toEraseChcs.insert(i);
        }
        else ++h;
      }
    }

    void combineCHCs()
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        set<int> toComb = {i};
        HornRuleExt& s = chcs[i];
        for (int j = i + 1; j < chcs.size(); j++)
        {
          if (find(toEraseChcs.begin(), toEraseChcs.end(), j) != toEraseChcs.end())
            continue;

          HornRuleExt& d = chcs[j];
          if (s.srcRelation == d.srcRelation && s.dstRelation == d.dstRelation)
          {
            for (int k = 0; k < s.srcVars.size(); k++)
              assert (s.srcVars[k] == d.srcVars[k]);
            for (int k = 0; k < s.dstVars.size(); k++)
              assert (s.dstVars[k] == d.dstVars[k]);
            toComb.insert(j);
          }
        }
        if (toComb.size() > 1)
        {
          if (debug >= 2)
          {
            outs () << "    Disjoing bodies of " << toComb.size() << " CHCs: "
                    << s.srcRelation << " -> " << s.dstRelation << "\n";
          }
          ExprVector all;
          for (auto it = toComb.rbegin(); it != toComb.rend(); ++it)
          {
            all.push_back(chcs[*it].body);
            if (*it != i) toEraseChcs.insert(*it);
          }
          s.body = distribDisjoin(all, m_efac);
          chcsToCheck1.insert(i);
          chcsToCheck2.insert(i);
          return combineCHCs();
        }
      }
    }

    // (recursive) multi-stage slicing begins here
    set<int> chcsToVisit;
    map<Expr, ExprSet> varsSlice;

    void updateTodo(Expr decl, int num)
    {
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        if (i != num &&
            !chcs[i].isQuery &&
            (chcs[i].srcRelation == decl || chcs[i].dstRelation == decl))
              chcsToVisit.insert(i);
      }
    }

    void slice()
    {
      chcsToVisit.clear();
      varsSlice.clear();
      // first, compute sets of dependent variables
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;

        if (chcs[i].isQuery)
        {
          chcs[i].body = keepQuantifiers(chcs[i].body, chcs[i].srcVars);
          Expr decl = chcs[i].srcRelation;
          filter (chcs[i].body, bind::IsConst(),
            std::inserter (varsSlice[decl], varsSlice[decl].begin ()));
          updateTodo(chcs[i].srcRelation, i);
        }
      }
      while (!chcsToVisit.empty()) slice(*chcsToVisit.begin());

      // now, prepare for variable elimination
      for (auto & d : varsSlice)
      {
//      if (invVars[d.first].size() > d.second.size())
//        outs () << "sliced for " << *d.first << ": " << invVars[d.first].size()
//                << " -> "    << d.second.size() << "\n";
        ExprSet varsPrime;
        for (auto & v : d.second)
        {
          Expr pr = replaceAll(v, invVars[d.first], invVarsPrime[d.first]);
          varsPrime.insert(pr);
        }

        keepOnly(invVars[d.first], d.second);
        keepOnly(invVarsPrime[d.first], varsPrime);
      }

      // finally, update bodies and variable vectors
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;
        auto & c = chcs[i];

        if (u.isFalse(c.body) || u.isTrue(c.body)) continue;

        ExprSet bd;
        getConj(c.body, bd);
        for (auto b = bd.begin(); b != bd.end();)
        {
          if (emptyIntersect(*b, invVars[c.srcRelation]) &&
              emptyIntersect(*b, invVarsPrime[c.dstRelation]))
            b = bd.erase(b);
          else ++b;
        }
        if (!c.isFact) c.srcVars = invVars[c.srcRelation];
        if (!c.isQuery) c.dstVars = invVarsPrime[c.dstRelation];
        c.body = conjoin(bd, m_efac);
      }
    }

    void slice(int num)
    {
      HornRuleExt* hr = &chcs[num];
      assert (!hr->isQuery);
      ExprSet srcCore, dstCore, srcDep, dstDep, varDeps, cnjs;
      auto & dst = hr->dstVars;
      auto & src = hr->srcVars;

      if (qeUnsupported(hr->body))
      {
        varDeps.insert(src.begin(), src.end());
        varDeps.insert(hr->locVars.begin(), hr->locVars.end());
        varDeps.insert(dst.begin(), dst.end());
      }
      else
      {
        // all src vars from the preconditions are dependent
        varDeps = varsSlice[hr->srcRelation];
        filter (getPrecondition(hr), bind::IsConst(),
                      std::inserter (varDeps, varDeps.begin ()));

        for (auto & v : varsSlice[hr->dstRelation])
          varDeps.insert(replaceAll(v, invVars[hr->dstRelation], dst));

        srcCore = varsSlice[hr->dstRelation];
        dstCore = varDeps;

        getConj(hr->body, cnjs);
        while(true)
        {
          int vars_sz = varDeps.size();
          for (auto & c : cnjs)
          {
            ExprSet varsCnj;
            filter (c, bind::IsConst(),
                          std::inserter (varsCnj, varsCnj.begin ()));
            if (!emptyIntersect(varDeps, varsCnj))
              varDeps.insert(varsCnj.begin(), varsCnj.end());
          }
          if (hr->isInductive)
          {
            for (auto & v : varDeps)
            {
              varDeps.insert(replaceAll(v, dst, src));
              varDeps.insert(replaceAll(v, src, dst));
            }
          }
          if (vars_sz == varDeps.size()) break;
        }
      }

      bool updateSrc = false;
      bool updateDst = false;
      if (!hr->isFact)
      {
        ExprSet& srcVars = varsSlice[hr->srcRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(src.begin(), src.end(), *v) != src.end())
          {
            if (find(srcVars.begin(), srcVars.end(), *v) == srcVars.end())
            {
              updateSrc = true;
              srcVars.insert(*v);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      srcDep = varsSlice[hr->srcRelation];
      dstDep = varDeps;

      if (!hr->isQuery)
      {
        ExprSet& dstVars = varsSlice[hr->dstRelation];
        for (auto v = varDeps.begin(); v != varDeps.end();)
        {
          if (find(dst.begin(), dst.end(), *v) != dst.end())
          {
            Expr vp = replaceAll(*v, dst, invVars[hr->dstRelation]);
            if (find(dstVars.begin(), dstVars.end(), vp) == dstVars.end())
            {
              updateDst = true;
              dstVars.insert(vp);
            }
            v = varDeps.erase(v);
          }
          else ++v;
        }
      }

      if (!varDeps.empty())
        hr->body = eliminateQuantifiers(hr->body, varDeps, false);

      if (updateSrc) updateTodo(hr->srcRelation, num);
      if (updateDst) updateTodo(hr->dstRelation, num);
      chcsToVisit.erase(num);
    }

    vector<int> getPrefix(Expr rel) // get only first one; to extend
    {
      assert(!cycles[rel].empty());
      assert(!prefixes[rel].empty());
      vector<int> pref = prefixes[rel][0];
      assert(!pref.empty());
      if (chcs[pref[0]].isFact)
        return pref;
      vector<int> ppref = getPrefix(chcs[pref[0]].srcRelation);
      ppref.insert(ppref.end(), pref.begin(), pref.end());
      return ppref;
    }

    bool hasCycles()
    {
      if (chcs.size() == 0) return false;
      if (cycleSearchDone) return cycles.size() > 0;
      findCycles();
      return (cycles.size() > 0);
    }

    void getAllTraces (Expr src, Expr dst, int len, vector<int> trace,
                vector<vector<int>>& traces, bool once = false)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            if (once && find(trace.begin(), trace.end(), a) != trace.end())
              continue;
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (once && find(trace.begin(), trace.end(), a) != trace.end())
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, once);
        }
      }
    }

    bool isRelVisited(vector<int>& trace, ExprVector& av, Expr rel)
    {
      for (auto t : trace)
        if (chcs[t].dstRelation == rel)
          return true;
      return find(av.begin(), av.end(), rel) != av.end();
    }

    void getAllAcyclicTraces (Expr src, Expr dst, int len, vector<int> trace,
                  vector<vector<int>>& traces, ExprVector& av)
    {
      if (len == 1)
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst)
          {
            vector<int> newtrace = trace;
            newtrace.push_back(a);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : outgs[src])
        {
          if (chcs[a].dstRelation == dst ||
              isRelVisited(trace, av, chcs[a].dstRelation))
            continue;
          vector<int> newtrace = trace;
          newtrace.push_back(a);
          getAllAcyclicTraces(chcs[a].dstRelation, dst, len-1, newtrace, traces, av);
        }
      }
    }

    void findCycles()
    {
      ExprVector endRels;
      outgs.clear(); acyclic.clear(); cycles.clear(); allCHCs.clear();
      prefixes.clear(); seqPoints.clear(); wtoCHCs.clear();
      for (int i = 0; i < chcs.size(); i++)
      {
        outgs[chcs[i].srcRelation].push_back(i);
        if (chcs[i].isQuery) unique_push_back(chcs[i].dstRelation, endRels);
      }

      ExprVector av;
      for (auto & d : decls)
        if (outgs[d->left()].empty())
          endRels.push_back(d->left());

      for (auto & r : endRels) {
        findCycles(mk<TRUE>(m_efac), r, av);
      }

      assert(wtoCHCs.size() == chcs.size());

      // filter wtoDecls
      for (auto it = wtoDecls.begin(); it != wtoDecls.end();)
      {
        if (*it == failDecl || isOpX<TRUE>(*it)) it = wtoDecls.erase(it);
        else ++it;
      }

      if (debug > 0)
      {
        for (auto & a : cycles)
          outs () << "  traces num for: " << a.first << ": " << a.second.size() << "\n";
      }
      for (auto & a : acyclic)
      {
        if (seqPoints.empty())
          for (auto & i : a) seqPoints.push_back(chcs[i].dstRelation);
        else
          for (auto it = seqPoints.begin(); it != seqPoints.end(); )
          {
            bool f = false;
            for (auto & i : a)
              if (*it == chcs[i].dstRelation)
                { f = true; break;}
            if (f) ++it;
            else it = seqPoints.erase(it);
          }
        if (seqPoints.empty()) break;
      }
      cycleSearchDone = true;
    }

    bool findCycles(Expr src, Expr dst, ExprVector& avoid)
    {
      if (debug >= 2) outs () << "\nfindCycles:  " << src << " => " << dst << "\n";
      vector<vector<int>> nonCycleTraces;
      ExprVector highLevelRels;
      for (int i = 1; i <= chcs.size(); i++)
      {
        if (debug >= 2)
        {
          outs () << ".";
          outs().flush();
        }
        getAllAcyclicTraces(src, dst, i, vector<int>(), nonCycleTraces, avoid);
      }

      bool tracesFound = nonCycleTraces.size() > 0;
      map <Expr, vector<vector<int>>> prefs;
      for (auto & d : nonCycleTraces)
      {
        vector<int> tmp;
        for (auto & chcNum : d)
        {
          if (chcs[chcNum].isQuery) break;      // last iter anyway
          Expr& r = chcs[chcNum].dstRelation;
          tmp.push_back(chcNum);
          if (find(avoid.begin(), avoid.end(), r) == avoid.end())
          {
            prefs[r].push_back(tmp);
            unique_push_back(r, highLevelRels);
          }
        }
      }

      if (tracesFound)
        if (src == dst)
          for (auto & c : nonCycleTraces) unique_push_back(c, cycles[src]);
        else
          for (auto & c : nonCycleTraces) unique_push_back(c, acyclic);
      else
        assert(src == dst);

      ExprVector avoid2 = avoid;
      for (auto & d : highLevelRels)
      {
        avoid2.push_back(d);
        bool nestedCycle = findCycles(d, d, avoid2);
        if (nestedCycle)
        {
          prefixes[d] = prefs[d]; // to debug
        }
      }

      // WTO sorting is here now:
      if (tracesFound)
      {
        if (src == dst)
        {
          unique_push_back(src, loopheads);      // could there be duplicates?
          if (debug > 0) outs () << "  loophead found: " << src << "\n";
        }
        else if (debug > 0) outs () << "  global:\n";
      }

      for (auto c : nonCycleTraces)
      {
        if (debug > 5)
        {
          outs () << "    trace: " << chcs[c[0]].srcRelation;
          for (auto h : c)
            outs () << " -> " << chcs[h].dstRelation << " ";
          outs () << "\n";
        }

        unique_push_back(chcs[c[0]].srcRelation, wtoDecls);
        for (auto h : c) {
          unique_push_back(chcs[h].dstRelation, wtoDecls);
          unique_push_back(&chcs[h], wtoCHCs);
        }
      }

      return tracesFound;
    }

    vector<int> empt;
    vector<int>& getCycleForRel(Expr rel)
    {
      for (auto & c : cycles[loopheads[0]]) // GF: loopheads[0]]?
        if (chcs[c[0]].srcRelation == rel)
          return c;
      return empt;
    }

    vector<int>& getCycleForRel(int chcNum)
    {
      return getCycleForRel(chcs[chcNum].srcRelation);
    }

    void addRule (HornRuleExt* r)
    {
      chcs.push_back(*r);
      Expr srcRel = r->srcRelation;
      if (!isOpX<TRUE>(srcRel))
      {
        if (invVars[srcRel].size() == 0)
        {
          addDeclAndVars(srcRel, r->srcVars);
        }
      }
      outgs[srcRel].push_back(chcs.size()-1);
    }

    void addDeclAndVars(Expr rel, ExprVector& args)
    {
      ExprVector types;
      for (auto &var: args) {
        types.push_back(bind::typeOf(var));
      }
      types.push_back(mk<BOOL_TY>(m_efac));

      decls.insert(bind::fdecl (rel, types));
      for (auto & v : args)
      {
        invVars[rel].push_back(v);
      }
    }

    void addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          errs () << "Multiple queries are unsupported\n";
          exit (1);
        }
      }
    }

    Expr getPostcondition(int i, ExprVector &vars)
    {
      HornRuleExt &hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      // for (auto &a : hr.srcVars)
        allVars.insert(allVars.end(), hr.srcVars.begin(), hr.srcVars.end());
      for (auto &a : cnjs)
      {
        if (emptyIntersect(a, allVars))
          newCnjs.insert(a);
      }
      Expr res = conjoin(newCnjs, m_efac);
      return replaceAll(res, hr.dstVars, vars);
    }

    Expr getPrecondition (HornRuleExt* hr)
    {
      Expr tmp = keepQuantifiers(hr->body, hr->srcVars);
      return weakenForHardVars(tmp, hr->srcVars);
    }

    // Transformations

    void copyIterations(Expr decl, int num)
    {
      HornRuleExt* hr;
      for (auto &a : chcs)
        if (a.srcRelation == decl->left() && a.dstRelation == decl->left())
          hr = &a;
      Expr pre = getPrecondition(hr);
      ExprSet newCnjs;
      newCnjs.insert(mk<NEG>(pre));
      for (int i = 0; i < hr->srcVars.size(); i++)
        newCnjs.insert(mk<EQ>(hr->dstVars[i], hr->srcVars[i]));
      Expr body2 = conjoin(newCnjs, m_efac);

      // adaping the code from BndExpl.hpp
      ExprVector ssa, bindVars1, bindVars2,newLocals;
      int bindVar_index = 0, locVar_index = 0;

      for (int c = 0; c < num; c++)
      {
        Expr body = hr->body;
        bindVars2.clear();
        if (c != 0)
        {
          body = replaceAll(mk<OR>(body, body2), hr->srcVars, bindVars1);
          for (int i = 0; i < hr->locVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__loc_var_" +
              to_string(locVar_index++), m_efac);
            Expr var = cloneVar(hr->locVars[i], new_name);
            body = replaceAll(body, hr->locVars[i], var);
            newLocals.push_back(var);
          }
        }

        if (c != num-1)
        {
          for (int i = 0; i < hr->dstVars.size(); i++)
          {
            Expr new_name = mkTerm<string> ("__bnd_var_" +
              to_string(bindVar_index++), m_efac);
            bindVars2.push_back(cloneVar(hr->dstVars[i], new_name));
            body = replaceAll(body, hr->dstVars[i], bindVars2[i]);
            newLocals.push_back(bindVars2[i]);
          }
        }
        ssa.push_back(body);
        bindVars1 = bindVars2;
      }
      hr->body = conjoin(ssa, m_efac);
      hr->locVars.insert(hr->locVars.end(), newLocals.begin(), newLocals.end());
    }

    void print (bool full = false, bool dump_cfg = false)
    {
      std::ofstream enc_chc;
      if (dump_cfg)
      {
        enc_chc.open("chc.dot");
        enc_chc <<("digraph print {\n");
      }
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find(toEraseChcs.begin(), toEraseChcs.end(), i) != toEraseChcs.end())
          continue;
        auto & hr = chcs[i];
        if (full)
        {
          if (hr.isFact) outs() << "  INIT:\n";
          else if (hr.isInductive) outs() << "  TR:\n";
          else if (hr.isQuery) outs() << "  BAD:\n";
          else outs() << "  CHC:\n";
        }

        outs () << "    " << * hr.srcRelation;
        if (full && hr.srcVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.srcVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.srcVars.size() << "]";
        outs () << " -> " << * hr.dstRelation;

        if (full && hr.dstVars.size() > 0)
        {
          outs () << " (";
          pprint(hr.dstVars);
          outs () << ")";
        }
        else outs () << "[#" << hr.dstVars.size() << "]";
        if (full)
        {
          outs() << "\n    body: \n";
          if (treeSize(hr.body) < 1000)
            pprint(hr.body, 4);
          else outs () << " < . . . . too large . . . . >\n";
        }
        else outs() << "\n";
        if (dump_cfg)
        {
          enc_chc << ' ' << hr.srcRelation;
          enc_chc << " -> ";
          enc_chc << ' ' << hr.dstRelation;
          enc_chc << '\n';
        }
      }
      if (dump_cfg)
      {
        enc_chc <<("}");
        enc_chc.close();
        // this needs a graphiz package installed:
        // system("dot -Tpdf -o chc.pdf chc.dot");
      }
    }

    void serializeExpr(Expr e)
    {
      std::ofstream out("tmp.smt2");
      u.print(e, out);
      out.close();
    }

    void serialize(bool horn = true)
    {
      if (horn) serializeHorn();
      else serializeCHC();
    }

    void serializeCHC()
    {
      // if (debug >= 2) 
        outs() << "Serializing CHC system to SMT2 format..." << std::endl;
      
      std::ofstream enc_chc;
      enc_chc.open("chc.smt2");
      
      // Create printer
      BVExprPrinter printer(u);

      // if (debug >= 3) 
        outs() << "Writing relation declarations...\n";
      for (auto & d : decls)
      {
        
        if (debug >= 4) 
          outs() << "  Declaring relation: " << d->arg(0) << "\n";

        enc_chc << "(declare-rel " << d->left() << " (";
        for (int i = 1; i < d->arity()-1; i++)
        {
          u.print(d->arg(i), enc_chc);
          if (i < d->arity()-2) enc_chc << " ";
        }
        enc_chc << "))\n";
      }

      enc_chc << "(declare-rel fail ())\n\n";

      if (debug >= 3) outs() << "Writing variable declarations...\n";
      enc_chc << "; srcVars\n";
      for(auto& v: invVars)
      {
        if (debug >= 4) outs() << "  Writing vars for relation: " << *v.first << "\n";
        for(auto& a: v.second)
        {
          enc_chc << "(declare-var ";
          u.print(a, enc_chc);
          enc_chc << " ";
          u.print(bind::typeOf(a), enc_chc);
          enc_chc << ")\n";
        }
        enc_chc << "\n";
      }

      enc_chc << "; dstVars\n";
      for (auto &v : invVarsPrime)
      {
        for (auto &a : v.second)
        {
          enc_chc << "(declare-var ";
          u.print(a, enc_chc);
          enc_chc << " ";
          u.print(bind::typeOf(a), enc_chc);
          enc_chc << ")\n";
        }
        enc_chc << "\n";
      }

      ExprSet varAdded;
      for (auto &c : chcs)
      {
        bool added = false;
        for(auto & l: c.locVars)
        {
          if(varAdded.find(l) == varAdded.end())
          {
            varAdded.insert(l);
            enc_chc << "(declare-var ";
            u.print(l, enc_chc);
            enc_chc << " ";
            u.print(bind::typeOf(l), enc_chc);
            enc_chc << ")\n";
            added = true;
          }
        }
        if(added) enc_chc << "\n";
      }

      if (debug >= 3) outs() << "Writing Horn rules...\n";
      for (auto & c : chcs)
      {
        if (debug >= 4) {
          outs() << "  Writing rule: " << *c.srcRelation;
          outs() << " -> " << *c.dstRelation << "\n";
        }
        enc_chc << "(rule ";
        Expr src, dst;
        if (c.isFact)
        {
          src = mk<TRUE>(m_efac);
        }
        else
        {
          for (auto &d : decls)
          {
            if (d->left() == c.srcRelation)
            {
              src = fapp(d, c.srcVars);
              break;
            }
          }
        }
        if (c.isQuery)
        {
          dst = failDecl;
        }
        else
        {
          for (auto &d : decls)
          {
            if (d->left() == c.dstRelation)
            {
              dst = fapp(d, c.dstVars);
              break;
            }
          }
        }
        enc_chc << "(=> ";
        // First normalize all BV operations to binary form
        Expr normalizedSrc = normalizeBVExpr(src);
        Expr normalizedBody = normalizeBVExpr(c.body);
        if(debug >= 4)
        {
          outs() << "  Normalized src: " << normalizedSrc << "\n";
          outs() << "  Normalized body: " << normalizedBody << "\n";
        }
        
        enc_chc << "(and ";
        printer.print(normalizedSrc, enc_chc);
        enc_chc << " ";
        printer.print(normalizedBody, enc_chc);
        enc_chc << ")";

        if(c.isQuery) 
        {
          enc_chc << " fail)";// << dst << ")";
        }
        else
        {
          enc_chc << " ";
          Expr normalizedDst = normalizeBVExpr(dst);
          printer.print(normalizedDst, enc_chc);
          enc_chc << ")";
        }
        enc_chc << ")\n\n";  
      }
      enc_chc << "(query fail)\n";
      if (debug >= 2) outs() << "Finished writing CHC system to " << "chc.smt2\n";
    }

    void serializeHorn ()
    {
      std::ofstream enc_chc;
      enc_chc.open("chc.smt2");
      enc_chc << "(set-logic HORN)\n";
      for (auto & d : decls)
      {
        enc_chc << "(declare-fun " << d->left() << " (";
        for (int i = 1; i < d->arity()-1; i++)
        {
          u.print(d->arg(i), enc_chc);
          if (i < d->arity()-2) enc_chc << " ";
        }
        enc_chc << ") Bool)\n";
      }
      enc_chc << "\n";
      for (auto & c : chcs)
      {
        Expr src, dst;
        if (c.isFact)
        {
          src = mk<TRUE>(m_efac);
        }
        else
        {
          for (auto & d : decls)
          {
            if (d->left() == c.srcRelation)
            {
              src = fapp(d, c.srcVars);
              break;
            }
          }
        }
        if (c.isQuery)
        {
          dst = mk<FALSE>(m_efac);
        }
        else
        {
          for (auto & d : decls)
          {
            if (d->left() == c.dstRelation)
            {
              dst = fapp(d, c.dstVars);
              break;
            }
          }
        }

        enc_chc << "(assert ";
        u.print(mkQFla(mk<IMPL>(mk<AND>(src, c.body), dst), true), enc_chc);
        enc_chc << ")\n\n";
      }
      enc_chc << "(check-sat)\n";
    }

    ZFixedPoint<EZ3> toZ3fp()
    {
      // fixed-point object
      ZFixedPoint<EZ3> fp(m_z3);
      ZParams<EZ3> params(m_z3);
      fp.set(params);

      Expr errRel = bind::boolConstDecl(failDecl);
      fp.registerRelation(errRel);

      for (auto &dcl : decls)
        fp.registerRelation(dcl);

      for (auto &r : chcs)
      {
        ExprSet allVars;
        allVars.insert(r.srcVars.begin(), r.srcVars.end());
        
        allVars.insert(r.dstVars.begin(), r.dstVars.end());
        allVars.insert(r.locVars.begin(), r.locVars.end());


        ExprSet pres;
        if (!r.isFact)
        {
          for (auto &dcl : decls)
          {
            if (dcl->left() == r.srcRelation)
            {
              pres.insert(bind::fapp(dcl, r.srcVars));
              break;
            }
          }
        }
        getConj(r.body, pres);
        fp.addRule(allVars, boolop::limp(conjoin(pres, m_efac), *decls.begin()));
      }
      fp.addQuery(bind::fapp(bind::fdecl(this->failDecl, ExprVector{sort::boolTy(m_efac)})));
      return fp;
    }

    ExprMap solve(unsigned timeout = 0u)
    {
      auto fp = toZ3fp();
      ZParams<EZ3> params(m_z3);
      params.set("timeout", timeout);
      fp.set(params);
      tribool res;
      ExprMap solution;
      try
      {
        res = fp.query();
      }
      catch (z3::exception &e)
      {
        std::string msg = e.msg();
        if (msg.find("canceled") == std::string::npos)
        {
          outs() << "Z3 ex: " << e.msg() << "...\n";
          exit(55);
        }
        else
        {
          // timeout
          return solution;
        }
      }
      if (!res)
      {
        for (auto const &pred : decls)
        {
          auto it = invVars.find(bind::name(pred));
          assert(it != invVars.end());
          Expr lemma = fp.getCoverDelta(bind::fapp(pred, it->second));
          solution.insert(std::make_pair<>(pred, lemma));
        }
      }
      return solution;
    }

    void simplifyCHCSystemSyntactically()
    {
      for (auto &chc : chcs)
      {
        chc.body = simplifyExpressionSyntactically(chc.body);
      }
    }

    Expr simplifyExpressionSyntactically(Expr e)
    {
      Expr res = simplifyBool(e);
      if (hasBV)
      {
        return simplifyBVConstructs(res);
      }
      return res;
    }

    Expr simplifyBVConstructs(Expr e)
    {
      std::map<Expr, unsigned> bitwidths;
      RW<SimplifyBVExpr> rw(new SimplifyBVExpr(e->getFactory(), bitwidths));
      return dagVisit(rw, e);
    }

    void strengthenWithInvariants(ExprMap const &invariants)
    {
      if(debug >= 2)
      {
        outs() << "Strengthening CHC system with invariants...\n";
      }
      if(debug >= 3)
      {
        outs() << "Invariants:\n";
        for(auto const &inv : invariants)
        {
          outs() << "  " << *inv.first << " -> " << *inv.second << "\n";
        }
      }

      for (auto &chc : this->chcs)
      {
        // inspiration from check CHC
        ExprSet newBody;
        newBody.insert(chc.body);
        Expr rel = chc.srcRelation;
        outs() << "rel: " << *rel << "\n";
        if(rel == mk<TRUE>(m_efac) || chc.isQuery)
        {
          continue;
        }
        ExprSet lms = {invariants.at(rel)};
        Expr substInvariants = replaceAll(conjoin(lms, m_efac), this->invVars[rel], chc.srcVars);
        getConj(substInvariants, newBody);
  
        if (!chc.isQuery)
        {
          Expr rel = chc.dstRelation;
          Expr lms = invariants.at(rel);
          Expr substInvariants = replaceAll(lms, this->invVars[rel], chc.dstVars);
          getConj(substInvariants, newBody);
        }
        chc.body = conjoin(newBody, this->m_efac);
      }
    }

    /**
     * Generate a SyGuS file for CVC5 to synthesize closed-form functions
     * describing the evolution of state variables along a concrete execution trace.
     * 
     * This method:
     * 1. Identifies the main invariant relation, fact (init), trans, and query rules
     * 2. Simulates a bounded concrete trace by successive model finding
     * 3. Generates SyGuS constraints from (step → state) pairs
     * 4. Outputs a .sygus file that CVC5 can solve to find closed-form expressions
     *
     * @param filename        Output SyGuS filename (default: "counterexample.sygus")
     * @param num_points      Number of trace points to collect (default: 128)
     * @param step_bitwidth   Bit-width for the step parameter (default: 16)
     * @param include_bad_check  Whether to check if bad state is reached (default: true)
     * @return true if SyGuS file was successfully generated, false otherwise
     */
    bool generateCounterexampleSyGuS(
        const std::string& filename = "counterexample.sygus",
        int num_points = -1,       // -1 means auto-detect
        int step_bitwidth = -1,    // -1 means auto-detect
        bool include_bad_check = true)
    {
      if (!hasBV)
      {
        outs() << "Error: generateCounterexampleSyGuS requires BV logic\n";
        return false;
      }

      outs() << "\n=== Generating Counterexample SyGuS ===\n";

      // Step 1: Identify main components
      Expr main_rel = nullptr;
      HornRuleExt* fact_rule = nullptr;
      HornRuleExt* trans_rule = nullptr;
      HornRuleExt* query_rule = nullptr;

      for (auto& d : decls)
      {
        if (d->left() != mk<TRUE>(m_efac) && d->left() != failDecl && !invVars[d->left()].empty())
        {
          if (main_rel != nullptr && main_rel != d->left())
          {
            outs() << "Warning: Multiple main relations found. Using first one.\n";
          }
          else
          {
            main_rel = d->left();
          }
        }
      }

      if (main_rel == nullptr)
      {
        outs() << "Error: Could not identify main invariant relation\n";
        return false;
      }

      outs() << "  Main relation: " << *main_rel << "\n";

      // Find fact, trans, and query rules
      for (auto& hr : chcs)
      {
        if (hr.isFact && hr.dstRelation == main_rel)
        {
          fact_rule = &hr;
        }
        else if (hr.isInductive && hr.srcRelation == main_rel && hr.dstRelation == main_rel)
        {
          trans_rule = &hr;
        }
        else if (hr.isQuery && hr.srcRelation == main_rel)
        {
          query_rule = &hr;
        }
      }

      if (fact_rule == nullptr)
      {
        outs() << "Error: Could not find initialization (fact) rule\n";
        return false;
      }
      if (trans_rule == nullptr)
      {
        outs() << "Error: Could not find transition (inductive) rule\n";
        return false;
      }

      outs() << "  Found fact rule, trans rule" << (query_rule ? ", and query rule" : "") << "\n";

      // Get state variables
      ExprVector state_vars = invVars[main_rel];
      outs() << "  State variables: " << state_vars.size() << "\n";

      // Determine bit-widths per variable
      std::map<Expr, unsigned> var_bw;
      unsigned max_state_bw = 0;
      unsigned total_state_bits = 0;
      for (auto& v : state_vars)
      {
        Expr vtype = bind::typeOf(v);
        if (bv::is_bvsort(vtype))
        {
          unsigned w = bv::width(vtype);
          var_bw[v] = w;
          if (w > max_state_bw) max_state_bw = w;
          total_state_bits += w;
        }
        else
        {
          outs() << "Warning: Variable " << *v << " is not BV type, skipping\n";
        }
      }

      // Auto-detect num_points if not specified (-1)
      // Key insight: We don't need full state space coverage for synthesis.
      // CVC5 can infer patterns from a small number of examples.
      // Use a small fixed default that works well for pattern inference.
      if (num_points < 0)
      {
        // Default to 16 points - enough for most linear/polynomial patterns
        // For very small state spaces, use the full space
        unsigned max_states = (max_state_bw <= 4) ? (1u << max_state_bw) : 16;
        num_points = max_states;
        
        outs() << "  Auto-detected trace points: " << num_points << "\n";
      }

      // Auto-detect step_bitwidth if not specified (-1)
      // Must be large enough to represent num_points values
      if (step_bitwidth < 0)
      {
        // Calculate minimum bits needed: ceil(log2(num_points))
        int bits_needed = 1;
        int temp = num_points - 1;
        while (temp > 1) { temp >>= 1; bits_needed++; }
        
        // Round up to standard sizes and ensure at least max_state_bw
        if (bits_needed <= 4) step_bitwidth = 4;
        else if (bits_needed <= 8) step_bitwidth = 8;
        else if (bits_needed <= 16) step_bitwidth = 16;
        else step_bitwidth = 32;
        
        // Ensure step_bitwidth is at least as wide as the widest state variable
        // This simplifies extraction in synthesized functions
        if ((unsigned)step_bitwidth < max_state_bw)
        {
          if (max_state_bw <= 8) step_bitwidth = 8;
          else if (max_state_bw <= 16) step_bitwidth = 16;
          else step_bitwidth = 32;
        }
        
        outs() << "  Auto-detected step bitwidth: " << step_bitwidth << "\n";
      }

      // Step 2: Extract concrete initial state
      outs() << "  Extracting initial state...\n";
      std::vector<std::map<Expr, Expr>> trace;
      
      ZSolver<EZ3> init_solver(m_z3);
      
      // Instantiate fact body with destination variables = state variables
      Expr init_body = replaceAll(fact_rule->body, fact_rule->dstVars, state_vars);
      init_solver.assertExpr(init_body);

      if (!init_solver.solve())
      {
        outs() << "Error: Initial state is unsatisfiable\n";
        return false;
      }

      // Extract concrete initial values
      std::map<Expr, Expr> current_state;
      auto init_model = init_solver.getModel();
      for (auto& v : state_vars)
      {
        Expr val = init_model.eval(v);
        if (val == nullptr || val == v)
        {
          // If no value from model, try to extract from body directly
          // For simple cases like (= x #x0), the body itself constrains it
          val = bv::bvnum(mpz_class(0), var_bw[v], m_efac);
          outs() << "    Warning: Using default 0 for " << *v << "\n";
        }
        current_state[v] = val;
        if (debug >= 2)
        {
          outs() << "    " << *v << " = " << *val << "\n";
        }
      }
      trace.push_back(current_state);
      outs() << "  Initial state extracted (step 0)\n";

      // Step 3: Simulate bounded concrete trace
      outs() << "  Simulating trace for " << num_points << " steps...\n";
      
      // Create "next" variables for the successor state
      ExprVector next_vars;
      for (size_t i = 0; i < state_vars.size(); i++)
      {
        Expr new_name = mkTerm<string>("__next_" + to_string(i), m_efac);
        next_vars.push_back(cloneVar(state_vars[i], new_name));
      }

      int bad_reached_at = -1;
      for (int step = 1; step < num_points; ++step)
      {
        ZSolver<EZ3> succ_solver(m_z3);
        
        // Assert current concrete state
        for (auto& v : state_vars)
        {
          succ_solver.assertExpr(mk<EQ>(v, current_state[v]));
        }

        // Instantiate transition body
        Expr inst_body = replaceAll(trans_rule->body, trans_rule->srcVars, state_vars);
        inst_body = replaceAll(inst_body, trans_rule->dstVars, next_vars);
        succ_solver.assertExpr(inst_body);

        if (!succ_solver.solve())
        {
          outs() << "  No successor at step " << step << ", stopping trace\n";
          break;
        }

        // Extract successor state
        auto succ_model = succ_solver.getModel();
        std::map<Expr, Expr> next_state;
        for (size_t i = 0; i < state_vars.size(); i++)
        {
          Expr val = succ_model.eval(next_vars[i]);
          if (val == nullptr || val == next_vars[i])
          {
            // No concrete value, use previous
            val = current_state[state_vars[i]];
          }
          next_state[state_vars[i]] = val;
        }
        
        trace.push_back(next_state);
        current_state = next_state;

        // Optional: check if bad state is reached
        if (include_bad_check && query_rule != nullptr && bad_reached_at < 0)
        {
          ZSolver<EZ3> bad_solver(m_z3);
          for (auto& v : state_vars)
          {
            bad_solver.assertExpr(mk<EQ>(v, current_state[v]));
          }
          Expr bad_body = replaceAll(query_rule->body, query_rule->srcVars, state_vars);
          bad_solver.assertExpr(bad_body);
          
          if (bad_solver.solve())
          {
            bad_reached_at = step;
            outs() << "  Bad state reached at step " << step << "\n";
          }
        }

        if (debug >= 3 && step % 10 == 0)
        {
          outs() << "    Step " << step << " completed\n";
        }
      }

      outs() << "  Collected " << trace.size() << " trace points\n";

      // Step 4: Generate SyGuS file
      outs() << "  Writing SyGuS file: " << filename << "\n";
      
      std::ofstream out(filename);
      if (!out.is_open())
      {
        outs() << "Error: Could not open file " << filename << " for writing\n";
        return false;
      }

      // Header
      out << "; SyGuS file for counterexample synthesis\n";
      out << "; Generated from CHC system\n";
      out << "; Main relation: " << *main_rel << "\n";
      out << "; Trace points collected: " << trace.size() << "\n";
      if (bad_reached_at >= 0)
      {
        out << "; Bad state reached at step: " << bad_reached_at << "\n";
      }
      out << "\n";
      out << "(set-logic BV)\n\n";

      // Generate synth-fun for each state variable
      for (size_t varIdx = 0; varIdx < state_vars.size(); varIdx++)
      {
        Expr v = state_vars[varIdx];
        if (var_bw.find(v) == var_bw.end()) continue;

        unsigned vwidth = var_bw[v];
        std::string fun_name = "state_" + to_string(varIdx);

        out << "; Function for variable " << *v << "\n";
        out << "(synth-fun " << fun_name << " ((step (_ BitVec " << step_bitwidth << "))) ";
        out << "(_ BitVec " << vwidth << ")\n";

        // Grammar
        out << "  ((Start (_ BitVec " << vwidth << ")) (Shift (_ BitVec " << vwidth << ")))\n";
        out << "  ((Start (_ BitVec " << vwidth << ") (\n";
        
        // Convert step to variable width if different
        if ((unsigned)step_bitwidth < vwidth)
        {
          out << "    ((_ zero_extend " << (vwidth - step_bitwidth) << ") step)\n";
        }
        else if ((unsigned)step_bitwidth > vwidth)
        {
          out << "    ((_ extract " << (vwidth - 1) << " 0) step)\n";
        }
        else
        {
          out << "    step\n";
        }

        // Constants - common useful values
        out << "    #x" << std::string(vwidth / 4, '0') << "\n";  // 0
        out << "    #x" << std::string(vwidth / 4 - 1, '0') << "1\n";  // 1

        // BV operations
        out << "    (bvadd Start Start)\n";
        out << "    (bvsub Start Start)\n";
        out << "    (bvxor Start Start)\n";
        out << "    (bvand Start Start)\n";
        out << "    (bvor Start Start)\n";
        out << "    (bvnot Start)\n";
        out << "    (bvneg Start)\n";
        out << "    (bvlshr Start Shift)\n";
        out << "    (bvshl Start Shift)\n";
        out << "  ))\n";
        
        // Shift amounts
        out << "  (Shift (_ BitVec " << vwidth << ") (\n";
        for (int sh = 0; sh <= 8 && sh < (int)vwidth; sh++)
        {
          out << "    #x" << std::string(vwidth / 4 - 1, '0') << std::hex << sh << std::dec << "\n";
        }
        out << "  ))\n";
        out << "))\n\n";
      }

      // Generate constraints from trace
      out << "; Constraints from concrete trace\n";
      for (size_t step = 0; step < trace.size(); step++)
      {
        const auto& state = trace[step];
        
        for (size_t varIdx = 0; varIdx < state_vars.size(); varIdx++)
        {
          Expr v = state_vars[varIdx];
          if (var_bw.find(v) == var_bw.end()) continue;
          
          auto it = state.find(v);
          if (it == state.end()) continue;

          unsigned vwidth = var_bw[v];
          std::string fun_name = "state_" + to_string(varIdx);

          // Convert step to hex string
          std::stringstream step_ss;
          step_ss << std::hex << std::setfill('0') << std::setw(step_bitwidth / 4) << step;
          std::string step_hex = step_ss.str();

          // Convert value to hex string
          std::string val_hex;
          Expr val = it->second;
          if (bv::is_bvnum(val))
          {
            mpz_class valMpz = bv::toMpz(val);
            std::stringstream val_ss;
            val_ss << std::hex << std::setfill('0') << std::setw(vwidth / 4);
            // Handle the mpz_class properly
            std::string hexStr = valMpz.get_str(16);
            // Pad to correct width
            while (hexStr.length() < vwidth / 4)
            {
              hexStr = "0" + hexStr;
            }
            val_hex = hexStr;
          }
          else
          {
            // Try to extract from the expression
            val_hex = std::string(vwidth / 4, '0');
            outs() << "Warning: Could not extract value for " << *v << " at step " << step << "\n";
          }

          out << "(constraint (= (" << fun_name << " #x" << step_hex << ") #x" << val_hex << "))\n";
        }
      }

      out << "\n(check-synth)\n";
      out.close();

      outs() << "  SyGuS file generated successfully!\n";
      outs() << "  Run with: cvc5 --lang=sygus2 " << filename << "\n";

      return true;
    }

    /**
     * Run CVC5 on a SyGuS file and parse the result.
     * 
     * @param sygus_filename  The SyGuS file to solve
     * @param timeout_seconds Timeout in seconds (default: 60)
     * @return A map from function name to synthesized expression (as string), or empty on failure
     */
    std::map<std::string, std::string> runCVC5SyGuS(
        const std::string& sygus_filename,
        int timeout_seconds = 60)
    {
      std::map<std::string, std::string> result;
      
      std::string cmd = "timeout " + to_string(timeout_seconds) + "s cvc5 --lang=sygus2 " + sygus_filename;
      
      outs() << "  Running: " << cmd << "\n";
      
      FILE* pipe = popen(cmd.c_str(), "r");
      if (!pipe)
      {
        outs() << "Error: Failed to run CVC5\n";
        return result;
      }

      std::string output;
      char buffer[256];
      while (fgets(buffer, sizeof(buffer), pipe) != nullptr)
      {
        output += buffer;
      }
      
      int status = pclose(pipe);
      if (status != 0)
      {
        outs() << "CVC5 exited with status " << status << "\n";
        if (!output.empty())
        {
          outs() << "Output: " << output << "\n";
        }
        return result;
      }

      outs() << "CVC5 output:\n" << output << "\n";

      // Parse the output - CVC5 outputs (define-fun name (...) (...) body)
      // Simple parsing: look for define-fun lines
      std::istringstream iss(output);
      std::string line;
      while (std::getline(iss, line))
      {
        if (line.find("(define-fun") != std::string::npos)
        {
          // Extract function name and body
          size_t nameStart = line.find("define-fun") + 11;
          size_t nameEnd = line.find(" ", nameStart);
          if (nameStart != std::string::npos && nameEnd != std::string::npos)
          {
            std::string fname = line.substr(nameStart, nameEnd - nameStart);
            result[fname] = line;
          }
        }
      }

      return result;
    }

    /**
     * Generate a CCEX file from CVC5's synthesized functions.
     * 
     * This creates a file in the same format as the benchmark CCEX files,
     * which can be used with validateCEXInductive().
     * 
     * @param synthesized_funcs  Map from function name to define-fun string from CVC5
     * @param ccex_filename      Output CCEX filename
     * @param step_bitwidth      Bit-width of the step parameter used in synthesis
     * @return true if CCEX file was successfully generated
     */
    bool generateCCEXFromSynthesis(
        const std::map<std::string, std::string>& synthesized_funcs,
        const std::string& ccex_filename = "synthesized_ccex.smt2",
        int step_bitwidth = -1)  // -1 means auto-detect from synthesized functions
    {
      if (synthesized_funcs.empty())
      {
        outs() << "Error: No synthesized functions provided\n";
        return false;
      }

      // Auto-detect step_bitwidth from synthesized function definitions
      // Look for pattern: ((step (_ BitVec N)))
      if (step_bitwidth <= 0)
      {
        for (auto& kv : synthesized_funcs)
        {
          std::string def = kv.second;
          size_t bvPos = def.find("(_ BitVec ");
          if (bvPos != std::string::npos)
          {
            size_t numStart = bvPos + 10;
            size_t numEnd = def.find(")", numStart);
            if (numEnd != std::string::npos)
            {
              std::string bwStr = def.substr(numStart, numEnd - numStart);
              step_bitwidth = std::stoi(bwStr);
              break;
            }
          }
        }
        if (step_bitwidth <= 0)
        {
          outs() << "Warning: Could not auto-detect step bitwidth, using 16\n";
          step_bitwidth = 16;
        }
      }

      // Find main relation and get state variables
      Expr main_rel = nullptr;
      for (auto& d : decls)
      {
        if (d->left() != mk<TRUE>(m_efac) && d->left() != failDecl && !invVars[d->left()].empty())
        {
          main_rel = d->left();
          break;
        }
      }

      if (main_rel == nullptr)
      {
        outs() << "Error: Could not identify main invariant relation\n";
        return false;
      }

      ExprVector state_vars = invVars[main_rel];

      // Determine bit-widths per variable
      std::map<int, unsigned> var_bw;
      for (size_t i = 0; i < state_vars.size(); i++)
      {
        Expr vtype = bind::typeOf(state_vars[i]);
        if (bv::is_bvsort(vtype))
        {
          var_bw[i] = bv::width(vtype);
        }
      }

      outs() << "\n=== Generating CCEX from Synthesized Functions ===\n";

      std::ofstream out(ccex_filename);
      if (!out.is_open())
      {
        outs() << "Error: Could not open file " << ccex_filename << " for writing\n";
        return false;
      }

      // Header comment
      out << "; CCEX file generated from CVC5 SyGuS synthesis\n";
      out << "; Main relation: " << *main_rel << "\n";
      out << "; Number of state variables: " << state_vars.size() << "\n\n";

      // Write the synthesized define-fun declarations
      // We need to rename them from state_X to var_X_at_i format
      out << "; Synthesized closed-form functions for state evolution\n";
      for (size_t i = 0; i < state_vars.size(); i++)
      {
        std::string synth_name = "state_" + std::to_string(i);
        auto it = synthesized_funcs.find(synth_name);
        if (it == synthesized_funcs.end()) continue;

        // Parse the define-fun and rewrite with new name
        // Original: (define-fun state_0 ((step (_ BitVec 16))) (_ BitVec 4) body)
        // Target:   (define-fun var_0_at_i ((i (_ BitVec 16))) (_ BitVec 4) body_with_i)
        std::string def = it->second;
        
        // Replace function name
        std::string new_name = "var_" + std::to_string(i) + "_at_i";
        size_t name_pos = def.find(synth_name);
        if (name_pos != std::string::npos)
        {
          def.replace(name_pos, synth_name.length(), new_name);
        }
        
        // Replace 'step' with 'i' in parameter and body
        size_t pos = 0;
        while ((pos = def.find("step", pos)) != std::string::npos)
        {
          def.replace(pos, 4, "i");
          pos += 1;
        }
        
        out << def << "\n";
      }
      out << "\n";

      // Declare trace arrays for each variable
      out << "; Trace arrays (one per state variable)\n";
      for (size_t i = 0; i < state_vars.size(); i++)
      {
        if (var_bw.find(i) == var_bw.end()) continue;
        unsigned vwidth = var_bw[i];
        out << "(declare-const trace_" << i << " (Array (_ BitVec " << step_bitwidth 
            << ") (_ BitVec " << vwidth << ")))\n";
      }
      out << "\n";

      // Generate the forall assertion that ties arrays to functions
      out << "; Assert that trace arrays follow the synthesized functions\n";
      out << "(assert\n";
      out << "  (forall ((i (_ BitVec " << step_bitwidth << ")))\n";
      
      // Generate hex constants properly for any bitwidth
      // For step_bitwidth bits, we need (step_bitwidth + 3) / 4 hex digits
      int hex_digits = (step_bitwidth + 3) / 4;
      out << "    (=> (and (bvule #x" << std::string(hex_digits, '0') << " i) ";
      out << "(bvule i #x" << std::string(hex_digits, 'f') << "))\n";
      out << "        (and\n";
      
      for (size_t i = 0; i < state_vars.size(); i++)
      {
        std::string synth_name = "state_" + std::to_string(i);
        if (synthesized_funcs.find(synth_name) == synthesized_funcs.end()) continue;
        
        out << "          (= (select trace_" << i << " i) (var_" << i << "_at_i i))\n";
      }
      
      out << "        )\n";
      out << "    )\n";
      out << "  )\n";
      out << ")\n\n";
      out << "(check-sat)\n";
      
      out.close();

      outs() << "  CCEX file generated: " << ccex_filename << "\n";
      return true;
    }

    /**
     * Full pipeline: Generate SyGuS, run CVC5, create CCEX file.
     * 
     * @param sygus_filename    Temporary SyGuS filename
     * @param ccex_filename     Output CCEX filename
     * @param num_points        Number of trace points for synthesis
     * @param step_bitwidth     Bit-width for step parameter
     * @param timeout_seconds   CVC5 timeout
     * @return true if the full pipeline succeeded
     */
    bool synthesizeCounterexample(
        const std::string& sygus_filename = "counterexample.sygus",
        const std::string& ccex_filename = "synthesized_ccex.smt2",
        int num_points = 128,
        int step_bitwidth = 16,
        int timeout_seconds = 60)
    {
      outs() << "\n=== Counterexample Synthesis Pipeline ===\n";

      // Step 1: Generate SyGuS file
      if (!generateCounterexampleSyGuS(sygus_filename, num_points, step_bitwidth, true))
      {
        outs() << "Failed to generate SyGuS file\n";
        return false;
      }

      // Step 2: Run CVC5
      auto synthesized = runCVC5SyGuS(sygus_filename, timeout_seconds);
      if (synthesized.empty())
      {
        outs() << "CVC5 synthesis failed or timed out\n";
        return false;
      }

      // Step 3: Generate CCEX file
      if (!generateCCEXFromSynthesis(synthesized, ccex_filename, step_bitwidth))
      {
        outs() << "Failed to generate CCEX file\n";
        return false;
      }

      outs() << "\n=== Synthesis Pipeline Complete ===\n";
      outs() << "  CCEX file ready for validation: " << ccex_filename << "\n";
      return true;
    }
  };
}

#endif
