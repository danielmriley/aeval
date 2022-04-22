#ifndef NONLINCHCSOLVER__HPP__
#define NONLINCHCSOLVER__HPP__

#include "HornNonlin.hpp"
#include "DataLearner.hpp"

#include <fstream>
#include <chrono>
#include <queue>
// #include <stdlib.h>

using namespace std;
using namespace boost;

namespace ufo
{
  static void getCombinations(vector<vector<int>>& in, vector<vector<int>>& out, int pos = 0)
  {
    if (pos == 0) out.push_back(vector<int>());
    if (pos == in.size()) return;

    vector<vector<int>> out2;

    for (auto & a : in[pos])
    {
      for (auto & b : out)
      {
        out2.push_back(b);
        out2.back().push_back(a);
      }
    }
    out = out2;
    getCombinations(in, out, pos + 1);
  }

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};

  class NonlinCHCsolver
  {
    private:

    ExprFactory &m_efac;
    EZ3 z3;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;
    bool hasArrays = false;
    ExprSet declsVisited;
    ExprVector decls;
    map<HornRuleExt*, vector<ExprVector>> abdHistory;
    int globalIter = 0;
    int strenBound;
    int debug = 0;
    map<Expr, Expr> extend;
    ExprVector fixedRels;
    map<Expr, vector<int> > reachChcs;
    string SYGUS_BIN;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
    int invVarsSz;

    string specName = "pre";
    string varName = "ST_";
    string ghostVar_pref = "gh_";
    Expr specDecl;
    ExprVector ghostVars;
    ExprVector ghostVarsPr;
    Expr decGhost0;
    Expr decGhost1;
    Expr ghost0Minus1;
    Expr ghost1Minus1;
    Expr ghostAss;
    Expr ghostGuard;
    Expr ghostGuardPr;
    Expr loopGuard;
    Expr loopGuardPr;
    Expr fcBodyInvVars;
    ExprSet bounds;
    ExprSet concrtBounds;
    ExprSet dataGrds;
    Expr mpzZero;

    bool hornspec = false;
    bool dg = false;
    bool printGsSoln = false;

    public:

    NonlinCHCsolver (CHCs& r, int _b, bool _dg, bool pssg, int dbg = 0)
      : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b), SYGUS_BIN(""), z3(m_efac), dg(_dg), printGsSoln(pssg), debug(dbg)
    {
      specDecl = mkTerm<string>(specName, m_efac);
      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isQuery) qr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;

      for(auto& dcl: ruleManager.decls) decls.push_back(dcl->left());
      invDecl = ruleManager.invRel;
      if(debug >= 2) outs() << "invDecl constructor: " << invDecl << "\n";
      invVars = tr->srcVars[0];
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();
      mpzZero = mkMPZ(0, m_efac);
    }

    bool setUpCounters()
    {
      if(debug >= 3) outs() << "setUpCounters\n";
      for (int i = 0; i < 2; i++)
      {
        Expr new_name = mkTerm<string> (ghostVar_pref + to_string(i), m_efac);
        Expr var = bind::intConst(new_name);
        ghostVars.push_back(var);

        new_name = mkTerm<string> (ghostVar_pref + to_string(i) + "'", m_efac);
        var = bind::intConst(new_name);
        ghostVarsPr.push_back(var);
      }

      ghost0Minus1 = mk<MINUS>(ghostVars[0], mkTerm (mpz_class (1), m_efac));
      ghost1Minus1 = mk<MINUS>(ghostVars[1], mkTerm (mpz_class (1), m_efac));
      decGhost0 = mk<EQ>(ghostVarsPr[0], ghost0Minus1);
      decGhost1 = mk<EQ>(ghostVarsPr[1], ghost1Minus1);
      ghostAss = mk<LT>(ghostVars[0], mkTerm (mpz_class (0), m_efac));
      ghostGuard = mk<NEQ>(ghostVars[0], mkTerm (mpz_class (0), m_efac));
      ghostGuardPr = mk<NEQ>(ghostVarsPr[0], mkTerm (mpz_class (0), m_efac));

      return true;
    }

    void replaceRule(HornRuleExt* hr, HornRuleExt* rule)
    {
      rule->srcRelation = hr->srcRelation;
      rule->srcRelations = hr->srcRelations;
      rule->srcVars = hr->srcVars;
      rule->dstRelation = hr->dstRelation;
      rule->dstVars = hr->dstVars;
      rule->head = hr->head;
      rule->isFact = hr->isFact;
      rule->isInductive = hr->isInductive;
      rule->isQuery = hr->isQuery;
      rule->body = hr->body;

/*      vector<HornRuleExt> chcsOld = chcs;
      chcs.clear();
      if(!hr->isInductive && !hr->isQuery) {
        addRule(hr);
        if(chcsOld.size() >= 2) chcs.push_back(chcsOld[1]);
        if(chcsOld.size() >= 3) chcs.push_back(chcsOld[2]);
      }
      else if(hr->isInductive) {
        if(chcsOld.size() >= 1) chcs.push_back(chcsOld[0]);
        addRule(hr);
        if(chcsOld.size() >= 3) chcs.push_back(chcsOld[2]);
      }
      else if(hr->isQuery) {
        if(chcsOld.size() >= 1) chcs.push_back(chcsOld[0]);
        if(chcsOld.size() >= 2) chcs.push_back(chcsOld[1]);
        addRule(hr);
      }
*/
    }

    void replaceRule(HornRuleExt* hr) {
      for(auto& rule: ruleManager.chcs) {
        if(!hr->isInductive && !hr->isQuery && !rule.isInductive && !rule.isQuery) {
          replaceRule(hr,&rule);
        }
        else if(hr->isInductive && rule.isInductive) {
          replaceRule(hr,&rule);
        }
        else if(hr->isQuery && rule.isQuery) {
          replaceRule(hr,&rule);
        }
      }
    }

    void specUpFc()
    {
      HornRuleExt* fc_new = new HornRuleExt();
      fc_new->srcRelation = fc->srcRelation;
      fc_new->srcRelations = fc->srcRelations;
      fc_new->srcRelations.push_back(specDecl);
      fc_new->srcVars.clear();
      fc_new->dstRelation = fc->dstRelation;
      fc_new->dstVars = fc->dstVars;
      fc_new->dstVars.push_back(ghostVarsPr[0]);
      fc_new->head = bind::boolConstDecl(fc_new->dstRelation);
      fc_new->isFact = false;
      ExprVector specVars;
      ExprVector specVarsPr;
//      specVars = invVars; // only include if keeping pre and inv vars the same.
  //    specVarsPr = invVarsPr; // only include if keeping pre and inv vars the same.
      for(int i = 0; i < invVars.size(); i++) {
        specVars.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()), m_efac)));
        specVarsPr.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()) + "'", m_efac)));
      }
      fc_new->srcVars.push_back(specVars);
      ExprSet fc_body;
      for(int i = 0; i < specVars.size(); i++) {
        fc_body.insert(mk<EQ>(specVars[i], invVarsPr[i]));
      }

      fc_body.insert(replaceAll(fc->body, invVarsPr, specVars));
      fc_body.insert(mk<EQ>(ghostVars[1], ghostVarsPr[0]));

      fc_new->body = conjoin(fc_body, m_efac);
      if(debug >= 3) outs() << "fc_new body: " << fc_new->body << "\n";
      for(auto& v: fc_new->srcVars) {
        v.push_back(ghostVars[1]);
      }
      specVars = fc_new->srcVars[0];
      ruleManager.invVars[specDecl].clear();
      ruleManager.addDeclAndVars(specDecl,specVars);


      replaceRule(fc_new);


      fcBodyInvVars = fc_new->body;
      ExprSet temp;
      getConj(fcBodyInvVars,temp);
      bool replaced;
      for(auto e = temp.begin(); e != temp.end(); ) {
        replaced = false;
        for(auto& i: fc_new->dstVars) {
          if(contains(*e, i)) {
            e = temp.erase(e);
            replaced = true;
          }

        }
        if(!replaced) e++;
      }
      fcBodyInvVars = conjoin(temp, m_efac);
      if(debug >= 4) {
        for(auto& v: fc_new->srcRelations)
          outs() << "Rel: " << v << "\n";

        for(auto& v: fc_new->srcVars)
          for(auto& e: v) outs() << "var: " << e << "\n";
      }


      for (auto & a : ruleManager.chcs)       // r.chcs changed by r.addRule, so pointers to its elements are broken
        if (a.isInductive) tr = &a;
        else if (!a.isInductive && !a.isQuery) fc = &a;
    }

    void setUpTr() // NEED TO RESET INV DECL
    {
      HornRuleExt* tr_new = new HornRuleExt();
      tr_new->srcRelation = tr->srcRelation;
      tr_new->srcRelations = tr->srcRelations;
      ruleManager.invVars[invDecl].clear();
      tr_new->srcVars = tr->srcVars;
      for(auto& sv: tr_new->srcVars) {
        sv.push_back(ghostVars[0]);
      }
      invVars.push_back(ghostVars[0]);
      invVarsPr.push_back(ghostVarsPr[0]);
      tr_new->dstRelation = tr->dstRelation;
      tr_new->dstVars = tr->dstVars;
      tr_new->dstVars.push_back(ghostVarsPr[0]);
      tr_new->head = bind::boolConstDecl(tr_new->dstRelation);
      tr_new->isInductive = true;
      ruleManager.addDeclAndVars(invDecl,invVars);


      ExprSet tmp;
      getConj(tr->body, tmp);
      tmp.insert(decGhost0);
      tr_new->body = conjoin(tmp, m_efac);
      replaceRule(tr_new);

      fcBodyInvVars = replaceAll(fcBodyInvVars, fc->srcVars[0], invVars);
      if(debug >= 4) outs() << "fcBodyInvVars: " << fcBodyInvVars << "\n";

    for (auto & a : ruleManager.chcs)       // r.chcs changed by r.addRule, so pointers to its elements are broken
      if (a.isInductive) tr = &a;
      else if (!a.isInductive && !a.isQuery) fc = &a;
    }

    void setUpQr()
    {
      qr = new HornRuleExt();
      qr->srcRelation = tr->srcRelation;
      qr->srcRelations = tr->srcRelations;
      qr->srcVars = tr->srcVars;
      qr->body = mk<AND>(mkNeg(loopGuard), ghostGuard);
      qr->dstRelation = mkTerm<string> ("err", m_efac);
      qr->head = bind::boolConstDecl(qr->dstRelation);
      qr->isQuery = true;
      ruleManager.hasQuery = true;

      ruleManager.addFailDecl(qr->dstRelation);
      ruleManager.addRule(qr);

    for (auto & a : ruleManager.chcs)       // r.chcs changed by r.addRule, so pointers to its elements are broken
      if (a.isInductive) tr = &a;
      else if (!a.isInductive && !a.isQuery) fc = &a;
    }

    bool setUpQueryAndSpec()
    {
      setUpCounters();

      for (auto & a : ruleManager.chcs)
        if (a.isInductive) tr = &a;
        else if (a.isFact) fc = &a;
        else if (a.isQuery) qr = &a;

      invDecl = tr->srcRelations[0];
      invVars = tr->srcVars[0];
      invVarsPr = tr->dstVars;
      invVarsSz = invVars.size();

      if (tr == NULL)
      {
        outs() << "TR is missing\n";
        exit(0);
      }

      if (fc == NULL)
      {
        outs() << "INIT is missing\n";
        exit(0);
      }
      loopGuard = ruleManager.getPrecondition(*ruleManager.decls.begin());
      loopGuardPr = replaceAll(loopGuard, invVars, invVarsPr);
      ruleManager.decls.clear();

      //fc
      specUpFc();
      setUpTr();
      setUpQr();

      if(debug) ruleManager.print();

      return true;
    }

    void mutateHeuristicEq(ExprSet& src, ExprSet& dst, Expr dcl, bool toProp)
    {
      int invNum = getVarIndex(dcl, decls);
      ExprSet src2;
      map<Expr, ExprVector> substs;
      Expr (*ops[])(Expr, Expr) = {mk<PLUS>, mk<MINUS>};        // operators used in the mutations

      for (auto a1 = src.begin(); a1 != src.end(); ++a1)
        if (isNumericEq(*a1))
        {
          for (auto a2 = std::next(a1); a2 != src.end(); ++a2)    // create various combinations
            if (isNumericEq(*a2))
            {
              const ExprVector m1[] = {{(*a1)->left(), (*a2)->left()}, {(*a1)->left(), (*a2)->right()}};
              const ExprVector m2[] = {{(*a1)->right(), (*a2)->right()}, {(*a1)->right(), (*a2)->left()}};
              for (int i : {0, 1})
                for (Expr (*op) (Expr, Expr) : ops)
                  src2.insert(simplifyArithm(normalize(
                    mk<EQ>((*op)(m1[i][0], m1[i][1]), (*op)(m2[i][0], m2[i][1])))));
            }

          // before pushing them to the cand set, we do some small mutations to get rid of specific consts
          Expr a = simplifyArithm(normalize(*a1));
          if (isOpX<EQ>(a) && isIntConst(a->left()) &&
              isNumericConst(a->right()) && lexical_cast<string>(a->right()) != "0")
            substs[a->right()].push_back(a->left());
          src2.insert(a);
        }

      bool printedAny = false;
      if (debug >= 2) outs () << "Mutated candidates:\n";
      for (auto a : src2)
        if (!u.isFalse(a) && !u.isTrue(a))
        {
          if (debug >= 2) { outs () << "  " << a << "\n"; printedAny = true; }

          if (containsOp<ARRAY_TY>(a)) {}
//            arrCands[invNum].insert(a);
          else
            dst.insert(a);

          if (isNumericConst(a->right()))
          {
            cpp_int i1 = lexical_cast<cpp_int>(a->right());
            for (auto b : substs)
            {
              cpp_int i2 = lexical_cast<cpp_int>(b.first);

              if (i1 % i2 == 0 && i1/i2 != 0)
                for (auto c : b.second)
                {
                  Expr e = simplifyArithm(normalize(mk<EQ>(a->left(), mk<MULT>(mkMPZ(i1/i2, m_efac), c))));
                  if (!u.isSat(mk<NEG>(e))) continue;
                  if (containsOp<ARRAY_TY>(e)) {}
//                    arrCands[invNum].insert(e);
                  else
                    dst.insert(e);

                  if (debug >= 2) { outs () << "  " << e << "\n"; printedAny = true; }
                }
            }
          }
        }
      if (debug >= 2 && !printedAny) outs () << "  none\n";
    }


    void filterNonGhExp(ExprSet& candSet)
    {
      for(auto i = candSet.begin(); i != candSet.end(); ) {
        if(!contains(*i, ghostVars[0])) {
          dataGrds.insert(*i);
          i = candSet.erase(i);
        }
        else i++;
      }
    }

    boost::tribool dataForBound(map<Expr, ExprSet>& candMap, Expr block) {
      if(debug >= 2)
        outs() << "\nUSING DATA\n===========\n";
      Expr invs = mk<TRUE>(m_efac);
      Expr srcRel = ruleManager.invRel;
      Expr model;
      Expr loopGuard;
      map<Expr, ExprSet> poly;
      DataLearner dl(ruleManager, z3, (debug > 0));
      boost::tribool res;

      for(auto hr : ruleManager.chcs) {
        if(hr.isInductive) loopGuard = ruleManager.getPrecondition(&hr);
      }

      if(invs == NULL) {outs() << "RETURNING\n"; return false;}

      if(debug >= 6) {
        outs() << "\n    srcRel: " << srcRel << "\n";
        outs() << "    loopGuard: " << loopGuard << "\n";
        outs() << "    invs: " << invs << "\n";
        outs() << "    block: " << block << "\n";
      }
      Expr dcl = invDecl;
      if(debug >= 6) outs() << "dcl: " << dcl << "\n";
      if (srcRel == dcl)
      {
        if(debug >= 6) outs() << "Compute Data\n";
        res = dl.computeDataTerm(srcRel, block, invs, loopGuard);
        if(!res) return res;
        dl.computePolynomials(dcl, poly[dcl]);
        concrtBounds.clear();
        concrtBounds = dl.getConcrInvs(dcl);
      //  filterNonGhExp(concrtBounds);
      }

      // mutations after all
      for (auto & p : poly)
      {
        mutateHeuristicEq(p.second, candMap[p.first], p.first, (block == NULL));
      }

      return res;
    }

    void filterDuplicates(ExprSet& setOne, ExprSet& setTwo)
    {
      for(auto one = setOne.begin(); one != setOne.end(); ) {
        for(auto two = setTwo.begin(); two != setTwo.end(); ) {
          if(contains(*one, *two)) {
            two = setTwo.erase(two);
          }
          else two++;
        }
      }
    }

    boost::tribool exploreBounds(map<Expr, ExprSet>& ghCandMap, Expr block)
    {
      boost::tribool res;

      //block = mkNeg(block);
      if(block == mk<FALSE>(m_efac)) return false;

      map<Expr, ExprSet> ghBoundMap;

      res = dataForBound(ghCandMap, block);
      filterNonGhExp(ghCandMap[invDecl]);
      if(ghCandMap[invDecl].empty()) return false;

      ExprSet temp;
      for(auto i = ghCandMap[invDecl].begin(),
          end = ghCandMap[invDecl].end(); i != end; i++) {
        Expr e = *i;
        e = normalize(e,ghostVars[0]);
        temp.insert(e);
      }
      ghCandMap[invDecl].swap(temp);

      if(debug >= 2) {
        outs() << "filtered cands:\n";
        if(!ghCandMap[invDecl].empty()) pprint(ghCandMap[invDecl],2);
        else outs() << "  none.\n";
      }

      if(!res && debug >= 3) outs() << "RETURNING FALSE FROM EXPLOREBOUNDS\n";
      return res;
    }

    bool checkAllOver (bool checkQuery = false)
    {
      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery && !checkQuery) continue;
        if (!checkCHC(hr, candidates)) return false;
      }
      return true;
    }

    bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
    {
      ExprSet checkList;
      checkList.insert(hr.body);
      Expr rel;
      if(debug >= 6) {
        if(hr.isQuery) outs() << "Query\n";
        else if(hr.isInductive) outs() << "Inductive\n";
        else outs() << "Pre\n";

      }
      for (int i = 0; i < hr.srcRelations.size(); i++)
      {
        Expr rel = hr.srcRelations[i];
        ExprSet lms = annotations[rel];
        Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars[i]);
        if(debug >= 6) outs() << "overbody: " << overBody << "\n";
        getConj(overBody, checkList);
      }
      if (!hr.isQuery)
      {
        rel = hr.dstRelation;
        ExprSet negged;
        ExprSet lms = annotations[rel];
        for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
        Expr neg = disjoin(negged, m_efac);
        if(debug >= 6) outs() << "neg: " << neg << "\n";
        checkList.insert(neg);
      }
      if(debug >= 6) { outs() << "checkList:\n"; pprint(checkList, 2); }
      return bool(!u.isSat(checkList));
    }

    void shrinkCnjs(ExprSet & cnjs)
    {
      ExprSet shrunk;
      ExprSet cnjsTmp = cnjs;
      for (auto c1 = cnjsTmp.begin(); c1 != cnjsTmp.end(); ++c1)
      {
        if (isOpX<OR>(*c1)) continue;
        for (auto c2 = cnjs.begin(); c2 != cnjs.end();)
        {
          if (!isOpX<OR>(*c2)) { ++c2; continue; };
          ExprSet dsjs;
          ExprSet newDsjs;
          getDisj(*c2, dsjs);
          for (auto & d : dsjs)
            if (u.isSat(*c1, d))
              newDsjs.insert(d);
          shrunk.insert(disjoin(newDsjs, m_efac));
          c2 = cnjs.erase(c2);
          cnjs.insert(disjoin(newDsjs, m_efac));
        }
        cnjs.insert(shrunk.begin(), shrunk.end());
        shrunk.clear();
      }
    }

    void preproGuessing(Expr e, ExprVector& ev1, ExprVector& ev2, ExprSet& guesses, bool backward = false, bool mutate = true)
    {
      if (!containsOp<FORALL>(e)) e = rewriteSelectStore(e);
      ExprSet complex;
      findComplexNumerics(e, complex);
      ExprMap repls;
      ExprMap replsRev;
      map<Expr, ExprSet> replIngr;
      for (auto & a : complex)
      {
        Expr repl = bind::intConst(mkTerm<string>
              ("__repl_" + lexical_cast<string>(repls.size()), m_efac));
        repls[a] = repl;
        replsRev[repl] = a;
        ExprSet tmp;
        filter (a, bind::IsConst (), inserter (tmp, tmp.begin()));
        replIngr[repl] = tmp;
      }
      Expr eTmp = replaceAll(e, repls);

      ExprSet ev3;
      filter (eTmp, bind::IsConst (), inserter (ev3, ev3.begin())); // prepare vars
      for (auto it = ev3.begin(); it != ev3.end(); )
      {
        if (find(ev1.begin(), ev1.end(), *it) != ev1.end()) it = ev3.erase(it);
        else
        {
          Expr tmp = replsRev[*it];
          if (tmp == NULL) ++it;
          else
          {
            ExprSet tmpSet = replIngr[*it];
            minusSets(tmpSet, ev1);
            if (tmpSet.empty()) it = ev3.erase(it);
            else ++it;
          }
        }
      }

      eTmp = eliminateQuantifiers(eTmp, ev3);
      if (backward) eTmp = mkNeg(eTmp);
      eTmp = simplifyBool(simplifyArithm(eTmp, false, true));

      ExprSet tmp;

      if (mutate)
        mutateHeuristic(eTmp, tmp);
      else
        getConj(eTmp, tmp);

      for (auto g : tmp)
      {
        g = replaceAll (g, replsRev);
        if (!ev2.empty())
          g = replaceAll(g, ev1, ev2);
        guesses.insert(g);
      }
    }

    bool isFixedRel(const Expr & rel)
    {
      return find(fixedRels.begin(), fixedRels.end(), rel) != fixedRels.end();
    }

    void addFixedRel(Expr rel)
    {
      fixedRels.push_back(rel);
    }

    // search for a CHC having the form r1 /\ .. /\ rn => rel, where rel \not\in {r1, .., rn}
    bool hasNoDef(Expr rel)
    {
      for (auto & hr : ruleManager.chcs)
        if (hr.dstRelation == rel &&
          find (hr.srcRelations.begin(), hr.srcRelations.end(), rel) == hr.srcRelations.end())
            return false;
      return true;
    }

    // lightweight (non-inductive) candidate propagation both ways
    // subsumes bootstrapping (ssince facts and queries are considered)
    void propagate(bool fwd = true)
    {
      // outs() << "Entry\n";//DEBUG
      // printCands(false);//DEBUG
      int szInit = declsVisited.size();
      for (auto & hr : ruleManager.chcs)
      {
	// outs() << "hrd: " << *(hr.dstRelation) << "\n";//DEBUG

        bool dstVisited = declsVisited.find(hr.dstRelation) != declsVisited.end();
        bool srcVisited = hr.isFact || (hr.isInductive && hasNoDef(hr.dstRelation) && extend.find(hr.dstRelation) == extend.end());
        bool dstFixed = isFixedRel(hr.dstRelation);

	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG

        for (auto & a : hr.srcRelations)
          srcVisited |= declsVisited.find(a) != declsVisited.end();

	// outs() << "sv: " << srcVisited << " fwd: " << fwd << " dv: " << dstVisited << "\n";//DEBUG
        if (fwd && srcVisited && !dstVisited && !dstFixed)
        {
          propagateCandidatesForward(hr);
          declsVisited.insert(hr.dstRelation);
        }
        else if (!fwd && !hr.isInductive && !srcVisited && dstVisited)
        {
          propagateCandidatesBackward(hr);
          declsVisited.insert(hr.srcRelations.begin(), hr.srcRelations.end());
        }
	// printCands(false);//DEBUG
      }

      if (declsVisited.size() != szInit) propagate(fwd);
      // outs() << "Exit\n";//DEBUG
      // printCands(false);//DEBUG
    }

    void propagateCandidatesForward(HornRuleExt& hr)
    {
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isQuery) return;

        Expr body = getQuantifiedCands(true, hr);

        ExprSet all;
        all.insert(body);
        for (int i = 0; i < hr.srcVars.size(); i++)
        {
          Expr rel = hr.srcRelations[i];
          if (!hasArrays) // we need "clean" invariants in the case of arrays (to be used as ranges)
          {
            // currently, tries all candidates; but in principle, should try various subsets
            for (auto & c : candidates[rel])
              all.insert(replaceAll(c, ruleManager.invVars[rel], hr.srcVars[i]));
          }
        }

	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "before: " << *c << "\n";

        if (hr.isInductive)   // get candidates of form [ <var> mod <const> = <const> ]
          retrieveDeltas (body, hr.srcVars[0], hr.dstVars, candidates[hr.dstRelation]);

        preproGuessing(conjoin(all, m_efac), hr.dstVars, ruleManager.invVars[hr.dstRelation], candidates[hr.dstRelation]);
	// //DEBUG
	// for (auto c : candidates[hr.dstRelation])
	//   outs() << "after: " << *c << "\n";
      }
    }

    void propagateCandidatesBackward(HornRuleExt& hr, bool forceConv = false)
    {
      // outs() << "in backward\n";//DEBUG
//      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isFact) return;

        Expr dstRel = hr.dstRelation;
        ExprVector& rels = hr.srcRelations;

        ExprVector invVars;
        ExprVector srcVars;

        // identifying nonlinear cases (i.e., when size(occursNum[...]) > 1)
        map<Expr, set<int>> occursNum;
        for (int i = 0; i < rels.size(); i++)
        {
          occursNum[rels[i]].insert(i);
          for (int j = i+1; j < rels.size(); j++)
            if (rels[i] == rels[j])
              occursNum[rels[i]].insert(j);
        }

        for (int i = 0; i < hr.srcVars.size(); i++)
          srcVars.insert(srcVars.end(), hr.srcVars[i].begin(), hr.srcVars[i].end());

        if (hr.srcVars.size() == 1) invVars = ruleManager.invVars[rels[0]];

        ExprSet cands;
        if (hr.isQuery)
        {
          if (getQuantifiedCands(false, hr) == NULL) return;
          else cands.insert(mk<FALSE>(m_efac));
        }
        else cands.insert(simplifyBool(conjoin(candidates[dstRel], m_efac)));

        ExprSet mixedCands;
        ExprVector curCnd;

        for (int i = 0; i < rels.size(); i++)
        {
          ExprSet tmp;
          getConj(replaceAll(conjoin(candidates[rels[i]], m_efac),
                             ruleManager.invVars[rels[i]], hr.srcVars[i]), tmp);
          curCnd.push_back(conjoin(tmp, m_efac));
        }

        // actually, just a single candidate, in the most recent setting;
        // TODO: remove the loop (or find use of it)
        for (auto & c : cands)
        {
          ExprSet all, newCnd;
          all.insert(hr.body);
          all.insert(mkNeg(replaceAll(c, ruleManager.invVars[dstRel], hr.dstVars)));
          all.insert(curCnd.begin(), curCnd.end());

          // TODO: add more sophisticated blocking based on unseccussful tries from abdHistory

          preproGuessing(conjoin(all, m_efac), srcVars, invVars, newCnd, true, false);

          if (!(u.isSat(conjoin(curCnd, m_efac), conjoin(newCnd, m_efac))))
          {
            // simple heuristic: find if some current guess was already created by abduction
            // then, delete it and try again
            if (!hr.isInductive)
              for (auto & t : abdHistory[&hr])
                for (int j = 0; j < t.size(); j++)
                  if (u.implies(conjoin(candidates[rels[j]], m_efac), t[j]))
                    candidates[rels[j]].clear();
            continue;
          }

          // oftentimes, newCnd is a disjunction that can be simplified
          // by considering other candidates in curCnd
          ExprSet tmp, tmp2;
          for (auto c : newCnd) getConj(c, tmp);
          for (auto c : curCnd) getConj(c, tmp);
          shrinkCnjs(tmp);
          getConj(conjoin(tmp, m_efac), tmp2);
          ineqMerger(tmp2, true);
          simplifyPropagate(tmp2);
          Expr stren = simplifyArithm(conjoin(tmp2, m_efac));
          mixedCands.insert(stren);
        }

        if (hr.srcVars.size() == 1)
        {
          if (!isFixedRel(rels[0])) {
            if (forceConv) forceConvergence(candidates[rels[0]], mixedCands);
            for (auto & m : mixedCands) getConj(m, candidates[rels[0]]);
          }
        }
        else
        {
          // decomposition here
          // fairness heuristic: prioritize candidates for all relations, which are true
          // TODO: find a way to disable it if for some reason some invariant should only be true
          vector<bool> trueCands;
          ExprSet trueRels;
          int numTrueCands = 0;
          for (int i = 0; i < rels.size(); i++)
          {
            trueCands.push_back(u.isTrue(curCnd[i]));
            if (trueCands.back())
            {
              trueRels.insert(rels[i]);
              numTrueCands++;
            }
          }

          // numTrueCands = 0;       // GF: hack to disable fairness

          ExprSet allGuessesInit;
          if (numTrueCands > 0)      // at least one curCnd should be true
            for (int i = 0; i < rels.size(); i++)
              if (!trueCands[i])
                allGuessesInit.insert(curCnd[i]);

          // actually, just a single candidate, in the most recent setting;
          // TODO: remove the loop (or find use of it)
          for (auto it = mixedCands.begin(); it != mixedCands.end(); )
          {
            if (containsOp<ARRAY_TY>(*it)) { ++it; continue; }
            Expr a = *it;
            ExprSet processed;
            ExprSet allGuesses = allGuessesInit;
            ExprVector histRec;

            auto candidatesTmp = candidates;

            for (int i = 0; i < rels.size(); i++)
            {
              // skip the relation if it already has a candidate and there exists a relation with no candidate
              // (existing candidates are already in allGuesses)
              if (numTrueCands > 0 && !trueCands[i]) continue;
              if (isFixedRel(rels[i])) continue;
              Expr r = rels[i];

	      // Expr modelphi = conjoin(curCnd, m_efac);

	      // if (rels.size() == 1) {
	      // 	if (extend.find(r) != extend.end()) {
	      // 	  modelphi = mk<AND>(modelphi, replaceAll(extend[r], ruleManager.invVars[r], hr.srcVars[i]));
	      // 	}
	      // } else {
	      // 	for (int j = i+1; j < rels.size(); j++) {
	      // 	  if (extend.find(rels[j]) != extend.end()) {
	      // 	    modelphi = mk<AND>(modelphi, replaceAll(extend[rels[j]], ruleManager.invVars[rels[j]], hr.srcVars[j]));
	      // 	  }
	      // 	}
	      // }

              if (!u.isSat(a, conjoin(curCnd, m_efac))) return; // need to recheck because the solver has been reset

              if (processed.find(r) != processed.end()) continue;

              invVars.clear();
              ExprSet backGuesses, allVarsExcept;
              ExprVector vars;
              for (int j = 0; j < rels.size(); j++)
              {
                Expr t = rels[j];
                if (processed.find(t) != processed.end()) continue;
                if (t == r)
                {
                  vars.insert(vars.begin(), hr.srcVars[j].begin(), hr.srcVars[j].end());
                  if (occursNum[r].size() == 1) invVars = ruleManager.invVars[rels[j]];
                }
                else
                  allVarsExcept.insert(hr.srcVars[j].begin(), hr.srcVars[j].end());
              }

              // model-based cartesian decomposition
              ExprSet all = allGuesses;
              all.insert(mkNeg(a));

              if (trueRels.size() != 1)                  // again, for fairness heuristic:
                all.insert(u.getModel(allVarsExcept));

	      // outs() << "truerels.size: " << trueRels.size() << "\n";//DEBUG
	      // outs() << "model: " << *(u.getModel(allVarsExcept)) << "\n";//DEBUG
	      //DEBUG
	      // for (auto v : allVarsExcept)
	      // 	outs() << "allvarsexcept: " << *v << "\n";
	      // for (auto a : all)
		// outs() << "all: " << *a << "\n";//DEBUG

              // in the case of nonlin, invVars is empty, so no renaming happens:

              preproGuessing(conjoin(all, m_efac), vars, invVars, backGuesses, true, false);

              if (occursNum[r].size() == 1)
              {
                getConj(conjoin(backGuesses, m_efac), candidates[r]);
                histRec.push_back(conjoin(backGuesses, m_efac));
                allGuesses.insert(backGuesses.begin(), backGuesses.end());
		//DEBUG
		// for (auto ag : allGuesses)
		//   outs() << "AG: " << *ag << "\n";
              }
              else
              {
                // nonlinear case; proceed to isomorphic decomposition for each candidate
                map<int, ExprVector> multiabdVars;

                for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                  for (auto & v : ruleManager.invVars[r])
                    multiabdVars[*it2].push_back(
                      cloneVar(v, mkTerm<string> (
                        "__multiabd_var" + lexical_cast<string>(*v) + "_" + to_string(*it2), m_efac)));

                Expr b = conjoin(backGuesses, m_efac);
                {
                  ExprSet sol;
                  int iter = 0;
                  while (++iter < 10 /*hardcode*/)
                  {
                    // preps for obtaining a new model

                    ExprSet cnj;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                    {
                      ExprSet dsj;
                      if (!sol.empty())
                        dsj.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      for (auto it3 = occursNum[r].begin(); it3 != occursNum[r].end(); ++it3)
                      {
                        ExprSet modelCnj;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          modelCnj.insert(mk<EQ>(hr.srcVars[*it2][i], multiabdVars[*it3][i]));
                        dsj.insert(conjoin(modelCnj, m_efac));
                      }
                      cnj.insert(disjoin(dsj, m_efac));
                    }

                    // obtaining a new model
                    ExprVector args;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      for (auto & v : hr.srcVars[*it2])
                        args.push_back(v->left());
                    args.push_back(mk<IMPL>(conjoin(cnj, m_efac), b));

                    ExprSet negModels;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      negModels.insert(mkNeg(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], multiabdVars[*it2])));

                    if (!u.isSat(extend.find(r) != extend.end() ?
                                 mk<AND>(extend[r], mknary<FORALL>(args)) :
                                 mknary<FORALL>(args), sol.empty() ?
                                 mk<TRUE>(m_efac) :
                                 disjoin(negModels, m_efac)))
                    {
                      candidates[r].insert(sol.begin(), sol.end());
                      histRec.push_back(conjoin(sol, m_efac));
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                        allGuesses.insert(replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                      break;
                    }
                    else
                    {
                      ExprSet models;
                      for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      {
                        ExprSet elements;
                        for (int i = 0; i < ruleManager.invVars[r].size(); i++)
                          elements.insert(mk<EQ>(ruleManager.invVars[r][i], u.getModel(multiabdVars[*it2][i])));
                        models.insert(conjoin(elements, m_efac));
                      }
                      sol.insert (disjoin(models, m_efac)); // weakening sol by a new model
                    }

                    // heuristic to accelerate convergence
                    ExprVector chk;
                    for (auto it2 = occursNum[r].begin(); it2 != occursNum[r].end(); ++it2)
                      chk.push_back(replaceAll(disjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it2]));
                    sol.clear();
                    for (auto it1 = occursNum[r].begin(); it1 != occursNum[r].end(); ++it1)
                    {
                      int cnt = 0;
                      for (auto it3 = occursNum[r].begin(); it3 != it1; ++it3, ++cnt)
                        chk[cnt] = replaceAll(conjoin(sol, m_efac), ruleManager.invVars[r], hr.srcVars[*it3]);
                      chk[cnt] = mk<TRUE>(m_efac);

                      ExprSet allNonlin;
                      allNonlin.insert(mkNeg(b));
                      allNonlin.insert(conjoin(chk, m_efac));
                      preproGuessing(conjoin(allNonlin, m_efac), hr.srcVars[*it1], ruleManager.invVars[r], sol, true, false);
                    }
                    u.removeRedundantConjuncts(sol);
                  }
                }
              }
              processed.insert(r);
            }

            // fairness heuristic (need to be tested properly):
            {
              bool tryAgain = false;
              if (!abdHistory[&hr].empty() && equivVecs(abdHistory[&hr].back(), histRec))
              {
                candidates = candidatesTmp;

                for (int i = 0; i < histRec.size(); i++)
                {
                  if (u.isEquiv(curCnd[i], histRec[i]))
                  {
                    numTrueCands++;
                    trueCands[i] = true;
                    trueRels.insert(rels[i]);
                  }
                  else
                  {
                    trueCands[i] = false;
                    allGuessesInit.insert(curCnd[i]);
                  }
                }
                tryAgain = true; // to keep
              }

              abdHistory[&hr].push_back(histRec);

              if (tryAgain)
              {
                if (abdHistory[&hr].size() > 5 /*hardcoded bound*/)
                {
                  tryAgain = false;
                  for (int i = 0; i < 5 /*hardcoded bound*/; i++)
                    if (abdHistory[&hr][abdHistory[&hr].size() - 1 - i] != histRec)
                    {
                      tryAgain = true;
                      break;
                    }
                }
              }

              if (!tryAgain) ++it;
            }
//            outs () << "sanity check: " << u.implies(conjoin(allGuesses, m_efac), a) << "\n";
          }
        }
      }
    }

    // inductive strengthening of candidates (by abduction)
    void strengthen(int deep = 0)
    {
      if (deep >= strenBound) return;

      // currently, relies on the order in CHC file; TBD: proper backwards traversing
      for (auto hr = ruleManager.chcs.rbegin(); hr != ruleManager.chcs.rend(); hr++)
      {
        if (!hr->isFact)
        {
          filterUnsat();
          if (!checkCHC(*hr, candidates))
          {
	    // outs() << "in strengthen before\n";//DEBUG
	     // printCands(false);//DEBUG
            propagateCandidatesBackward(*hr, deep == strenBound - 1);
	    // outs() << "in strengthen after\n";//DEBUG
	    // printCands(false);//DEBUG
            strengthen(deep+1);
          }
        }
      }
    }

    void forceConvergence (ExprSet& prev, ExprSet& next)
    {
      if (prev.size() < 1 || next.size() < 1) return;
      ExprFactory& m_efac = (*next.begin())->getFactory();

      ExprSet prevSplit, nextSplit, prevSplitDisj, nextSplitDisj, common;

      for (auto & a : prev) getConj (a, prevSplit);
      for (auto & a : next) getConj (a, nextSplit);

      mergeDiseqs(prevSplit);
      mergeDiseqs(nextSplit);

      if (prevSplit.size() != 1 || nextSplit.size() != 1)
        return; // GF: to extend

      getDisj(*prevSplit.begin(), prevSplitDisj);
      getDisj(*nextSplit.begin(), nextSplitDisj);

      for (auto & a : prevSplitDisj)
        for (auto & b : nextSplitDisj)
          if (a == b) common.insert(a);

      if (common.empty()) return;
      next.clear();
      next.insert(disjoin(common, m_efac));
    }

    bool equivVecs (ExprVector e1, ExprVector e2)
    {
      if (e1.size() != e2.size()) return false;
      for (int i = 0; i < e1.size(); i++)
      {
        if (!u.isEquiv(e1[i], e2[i])) return false;
      }
      return true;
    }

    void getImplicationGuesses(map<Expr, ExprSet>& postconds)
    {
      map<Expr, ExprSet> preconds;
      for (auto & r : ruleManager.chcs)
      {
        if (r.isQuery) continue;

        int srcRelInd = -1;
        Expr rel = r.head->left();

        if (isFixedRel(rel)) continue;

        for (int i = 0; i < r.srcVars.size(); i++) if (r.srcRelations[i] == rel) srcRelInd = i;
        if (srcRelInd >= 0)
          preproGuessing(r.body, r.srcVars[srcRelInd], ruleManager.invVars[rel], preconds[rel]);

        if (srcRelInd == -1) continue;
        int tot = 0;
        for (auto guess : postconds[rel])
        {
          if (tot > 5) break; // empirically chosen bound
          if (isOpX<IMPL>(guess) || isOpX<OR>(guess)) continue; // hack

          for (auto & pre : preconds[rel])
          {
            if (u.implies(pre, guess)) continue;
            tot++;
            Expr newGuess = mk<IMPL>(pre, guess);
            ExprVector tmp;
            tmp.push_back(replaceAll(newGuess, ruleManager.invVars[rel], r.srcVars[srcRelInd]));
            tmp.push_back(r.body);
            // simple invariant check (for speed, need to be enhanced)
            if (u.implies (conjoin(tmp, m_efac), replaceAll(newGuess, ruleManager.invVars[rel], r.dstVars)))
            {
              candidates[rel].insert(newGuess);
              ExprSet newPost;
              tmp.push_back(mkNeg(replaceAll(pre, ruleManager.invVars[rel], r.dstVars)));
              preproGuessing(conjoin(tmp, m_efac), r.dstVars, ruleManager.invVars[rel], newPost);
              for (auto & a : newPost)
                candidates[rel].insert(mk<IMPL>(mk<NEG>(pre), a));
            }
          }
        }
      }
    }

    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false)
    {
      printCands(unsat, partialsolns, nonmaximal, simplify, outs());
    }

    template <typename OutputStream>
    void printCands(bool unsat = true, map<Expr, ExprSet> partialsolns = map<Expr,ExprSet>(), bool nonmaximal = false, bool simplify = false, OutputStream & out = outs())
    {
      if (unsat)
      {
        out << "unsat";
        if (nonmaximal)
          out << " (may not be maximal solution) \n";
        else
          out << "\n";
      }

      for (auto & a : partialsolns.empty() ? candidates : partialsolns)
      {
        out << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          out << "(" << *b << " " << u.varType(b) << ")";
        }
        out << ") Bool\n  ";

        ExprSet lms = a.second;
        Expr sol = conjoin(lms, m_efac);

        // sanity checks:
        ExprSet allVars;
        filter (sol, bind::IsConst (), inserter (allVars, allVars.begin()));
        minusSets(allVars, ruleManager.invVars[a.first]);
        map<Expr, ExprVector> qv;
        getQVars (sol, qv);
        for (auto & q : qv) minusSets(allVars, q.second);
        for(auto& r: allVars) outs() << "allVars: " << r << "\n";
        assert (allVars.empty());
//        if (!u.isSat(sol)) assert(0);

        Expr res = simplifyBool(simplifyArithm(sol));
        if (simplify)
        {
          lms.clear();
          getConj(res, lms);
          shrinkCnjs(lms);
          u.removeRedundantConjuncts(lms);
          res = conjoin(lms, m_efac);
        }
        pprint(res);
        out << ")\n";
      }
    }

    bool dropUnsat(map<Expr, ExprSet>& annotations, const ExprVector & unsatCore, const map<Expr, pair<Expr, Expr>> & flagToCand)
    {
      for (auto & c : unsatCore) {
        auto entry = flagToCand.find(c);
        if (entry == flagToCand.end()) continue;
        Expr rel = (entry->second).first;
        Expr cand = (entry->second).second;
        annotations[rel].erase(cand);
        return true;
      }

      return false;
    }

    /* vacuity check based on SAT check */
    void vacCheck(map<Expr, ExprSet>& annotations)
    {
      bool recurse = false;

      for (auto & hr : ruleManager.chcs)
      {
        if (hr.isFact) continue;

        ExprVector flags;
        ExprSet finalExpr;
        map<Expr, pair<Expr, Expr>> flagToCand;
        bool hasArray = false;

        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr rel = hr.srcRelations[i];
          if (isFixedRel(rel)) {
            for (auto cand : annotations[rel]) {
              cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);
              finalExpr.insert(cand);
            }
          } else {
            for (auto cand : annotations[rel]) {
              if (!hasArray && containsOp<FORALL>(cand)) hasArray = true;
              Expr flag = bind::boolConst(mkTerm<string>("__unsatcoreVar__" + to_string(flags.size()+1), m_efac));
              flags.push_back(flag);
              flagToCand[flag] = make_pair(rel, cand);
              cand = replaceAll(cand, ruleManager.invVars[rel], hr.srcVars[i]);
              finalExpr.insert(mk<IMPL>(flag, cand));
            }
          }
        }

        if (!hr.isQuery && u.isSat(hr.body)) {
          finalExpr.insert(hr.body);
        }

        // outs() << "BODY: " << *(hr.body) << "\n";
        // for (auto f : finalExpr)
        //   outs() << *f << "\n";

        if (!hasArray) {
          ExprVector unsatCore;
          if (!u.isSatAssuming(finalExpr, flags, std::back_inserter(unsatCore))) {
            // outs() << "failed hr: " << *(hr.body) << "\n";
            // outs() << "flags: " << flags.size() << "\n";
            // outs() << "unsatcore: " << unsatCore.size() << "\n";
            assert(dropUnsat(annotations, unsatCore, flagToCand));
            recurse = true;
          }
        } else {
          if (!u.isSat(finalExpr)) {
            ExprVector t1;
            ExprVector t2;
            u.splitUnsatSets(finalExpr, t1, t2);
            for (int i = 0; i < hr.srcRelations.size(); i++) {
              Expr rel = hr.srcRelations[i];

              for (auto itr =  annotations[rel].begin(); itr != annotations[rel].end();) {
                Expr c = replaceAll(*itr, hr.srcVars[i], ruleManager.invVars[rel]);
                if (find(t1.begin(), t1.end(), c) == t1.end()) {
                  itr = annotations[rel].erase(itr);
                } else {
                  ++itr;
                }
              }
            }
            recurse = true;
          }
        }

        if (recurse)
          return vacCheck(annotations);
      }
    }


    void filterUnsat()
    {
      vector<HornRuleExt*> worklist;
      for (auto & a : candidates)
        if (!u.isSat(a.second)) {
          assert(!isFixedRel(a.first));
          for (auto & hr : ruleManager.chcs)
            if (hr.dstRelation == a.first && hr.isFact)
              worklist.push_back(&hr);
        }

      multiHoudini(worklist, false);

      for (auto & a : candidates)
      {
        if (!u.isSat(a.second))
        {
          ExprVector tmp;
          ExprVector stub; // TODO: try greedy search, maybe some lemmas are in stub?
          u.splitUnsatSets(a.second, tmp, stub);
          a.second.clear();
          a.second.insert(tmp.begin(), tmp.end());
        }
      }
      vacCheck(candidates);
    }

    Expr getQuantifiedCands(bool fwd, HornRuleExt& hr)
    {
      ExprSet qVars;
      Expr body = hr.body;
      if (fwd && hr.isFact)
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())  // immediately try proving properties if already quantified
        {
          // make sure that we can use it as a property (i.e., variables check)

          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          bool allGood = true;
          for (auto & v : allVars)
            if (find (hr.dstVars.begin(), hr.dstVars.end(), v) == hr.dstVars.end())
              { allGood = false; break; }
          if (allGood)
          {
            ExprSet tmpSet;
            getQuantifiedFormulas(hr.body, tmpSet);
            for (auto c : tmpSet)
            {
              // over-approximate the body such that it can pass through the seed mining etc..
              body = replaceAll(body, c, mk<TRUE>(m_efac));
              c = replaceAll(c, hr.dstVars, ruleManager.invVars[hr.dstRelation]);
              candidates[hr.dstRelation].insert(c);
            }
          }
        }
      }
      if (!fwd && hr.isQuery)  // similar for the query
      {
        getQuantifiedVars(hr.body, qVars);
        if (!qVars.empty())
        {
          ExprSet allVars;
          filter (hr.body, bind::IsConst (), inserter (allVars, allVars.begin()));
          minusSets(allVars, qVars);
          for (int i = 0; i < hr.srcVars.size(); i++)
          {
            bool toCont = false;
            for (auto & v : allVars)
              if (find (hr.srcVars[i].begin(), hr.srcVars[i].end(), v) == hr.srcVars[i].end())
                { toCont = true; break; }
            if (toCont) continue;
            getQuantifiedFormulas(mkNeg(hr.body), candidates[hr.srcRelations[i]]);
          }
          return NULL; // just as an indicator that everything went well
        }
      }
      return body;
    }

    bool isSkippable(Expr model, ExprVector vars, map<Expr, ExprSet>& cands)
    {
      if (model == NULL) return true;

      for (auto v: vars)
      {
        if (!containsOp<ARRAY_TY>(v)) continue;
        Expr tmp = u.getModel(v);
        if (tmp != v && !isOpX<CONST_ARRAY>(tmp) && !isOpX<STORE>(tmp))
        {
          return true;
        }
      }

      for (auto & a : cands)
        for (auto & b : a.second)
          if (containsOp<FORALL>(b)) return true;

      return false;
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if (!anyProgress(worklist)) {
        if(debug >= 3) outs() << "No progress\n";
        return false;
      }
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;
        if (isFixedRel(hr->dstRelation)) continue;

        if (!checkCHC(*hr, candidatesTmp))
        {
          bool res2 = true;
          Expr dstRel = hr->dstRelation;

          Expr model = u.getModel(hr->dstVars);
          if (isSkippable(model, hr->dstVars, candidatesTmp))
          {
            candidatesTmp[dstRel].clear();
            res2 = false;
          }
          else
          {
            for (auto it = candidatesTmp[dstRel].begin(); it != candidatesTmp[dstRel].end(); )
            {
              Expr repl = *it;
              repl = replaceAll(*it, ruleManager.invVars[dstRel], hr->dstVars);

              if (!u.isSat(model, repl)) { it = candidatesTmp[dstRel].erase(it); res2 = false; }
              else ++it;
            }
          }

          if (recur && !res2) res1 = false;
          if (!res1) break;
        }
      }
      candidates = candidatesTmp;
      if (!recur) return false;
      if (res1) return anyProgress(worklist);
      else return multiHoudini(worklist);
    }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist)
          if (find(hr->srcRelations.begin(), hr->srcRelations.end(), a.first) !=
              hr->srcRelations.end() || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    // only one level of propagation here; to be extended
    void arrayGuessing(Expr tgt)
    {
      bool arrFound = false;
      for (auto & var : ruleManager.invVars[tgt])
        if (bind::isConst<ARRAY_TY> (var)) {
          arrFound = true;
          break;
        }
      if (!arrFound) return;

      int ind;
      bool iterGrows;
      Expr iterator;
      Expr qVar = bind::intConst(mkTerm<string> ("_FH_arr_it", m_efac));
      Expr range;
      HornRuleExt *hr = 0;
      HornRuleExt *qr = 0;

      // preprocessing
      for (auto & a : ruleManager.chcs)
      {
        if (a.isQuery && a.srcRelations[0] == tgt /*hack for now*/ &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
          qr = &a;
        if (a.isInductive && a.dstRelation == tgt &&
            (containsOp<SELECT>(a.body) || containsOp<STORE>(a.body)))
        {
          ExprVector counters;
          hr = &a;

          getCounters(a.body, counters);
          for (Expr c : counters)
          {
            ind = getVarIndex(c, a.srcVars[0] /*hack for now*/);
            if (ind < 0) continue;

            if (u.implies(a.body, mk<GT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = false;
              break;
            }
            else if (u.implies(a.body, mk<LT>(c, a.dstVars[ind])))
            {
              iterator = c;
              iterGrows = true;
            }
          }
        }
      }

      if (iterator == NULL) return;

      // range computation
      for (auto & a : ruleManager.chcs)
      {
        if (!a.isInductive && a.dstRelation == tgt)
        {
          int max_sz = INT_MAX;
          for (Expr e : candidates[tgt])
          {
            if ((iterGrows &&
               ((isOpX<GEQ>(e) && iterator == e->left()) ||
                (isOpX<LEQ>(e) && iterator == e->right()))) ||
               (!iterGrows &&
                 ((isOpX<GEQ>(e) && iterator == e->right()) ||
                  (isOpX<LEQ>(e) && iterator == e->left()))))
            {
              Expr bound = (e->left() == iterator) ? e->right() : e->left();
              if (treeSize(bound) < max_sz)
              {
                range = iterGrows ? mk<AND>(mk<LEQ>(bound, qVar), mk<LT>(qVar, iterator)) :
                                    mk<AND>(mk<LT>(iterator, qVar), mk<LEQ>(qVar, bound));
                max_sz = treeSize(bound);
              }
            }
          }
        }
      }

      if (range == NULL) return;

      // cell property guessing
      Expr body = hr->body;
      body = unfoldITE(body);
      body = rewriteSelectStore(body);
      ExprSet tmp;
      ExprVector qVars1, qVars2;
      for (int i = 0; i < hr->dstVars.size(); i++)
      {
        if (ruleManager.invVars[hr->srcRelations[0]][i] == iterator)
        {
          qVars1.push_back(hr->dstVars[i]);
          qVars2.push_back(iterator);
        }
        else
        {
          qVars1.push_back(ruleManager.invVars[hr->srcRelations[0]][i]);
          qVars2.push_back(hr->dstVars[i]);
        }
      }
      body = simpleQE(body, qVars1);

      preproGuessing(body, qVars2, ruleManager.invVars[hr->srcRelations[0]], tmp);

      for (auto s : tmp)
      {
        if (!containsOp<SELECT>(s)) continue;
        s = replaceAll(s, iterator, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], hr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
        {
          candidates[tgt].insert(newGuess);
          // try to propagate (only one level now; TODO: extend)
          for (auto & hr2 : ruleManager.chcs)
          {
            if (hr2.isQuery) continue;
            if (find(hr2.srcRelations.begin(), hr2.srcRelations.end(), tgt) != hr2.srcRelations.end() &&
                hr2.dstRelation != tgt)
            {
              ExprSet cnjs;
              getConj(hr2.body, cnjs);
              Expr newRange;
              for (auto c : cnjs)
              {
                if (emptyIntersect(c, iterator)) continue;
                if (isOpX<NEG>(c)) c = mkNeg(c->left());
                c = ineqSimplifier(iterator, c);
                if (!isOp<ComparissonOp>(c)) continue;

                if (isOpX<EQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (iterGrows && isOpX<GT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<PLUS>(c->right(), mkTerm (mpz_class (1), m_efac)));
                if (!iterGrows && isOpX<LEQ>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, c->right());
                if (!iterGrows && isOpX<LT>(c) && c->left() == iterator)
                  newRange = replaceAll(range, iterator, mk<MINUS>(c->right(), mkTerm (mpz_class (1), m_efac)));

                if (newRange != NULL) break;
              }

              if (newRange == NULL) continue;

              ExprVector args;
              args.push_back(qVar->left());
              args.push_back(mk<IMPL>(newRange, s));
              Expr newCand = getForallCnj(
                    simpleQE(
                        mk<AND>(hr2.body,mknary<FORALL>(args)), hr2.srcVars[0]));

              newCand = replaceAll(newCand, hr2.dstVars, ruleManager.invVars[hr2.dstRelation]);
              // finally, try the propagated guess:
              candidates[hr2.dstRelation].insert(newCand);
            }
          }
        }
      }

      if (qr == 0) return;

      tmp.clear();
      getArrIneqs(mkNeg(qr->body), tmp);

      for (auto s : tmp)
      {
        ExprSet allv;
        filter (s, bind::IsConst (), inserter (allv, allv.begin()));
        for (auto & a : allv)
          if (bind::typeOf(a) == bind::typeOf(qVar) && find(hr->srcVars[0].begin(), hr->srcVars[0].end(), a) ==
              hr->srcVars[0].end()) s = replaceAll(s, a, qVar);

        ExprVector args;
        args.push_back(qVar->left());
        args.push_back(mk<IMPL>(range, s));
        Expr newGuess = mknary<FORALL>(args);

        ExprSet chk;
        chk.insert(replaceAll(newGuess, ruleManager.invVars[tgt], qr->srcVars[0]));
        chk.insert(hr->body);
        chk.insert(candidates[tgt].begin(), candidates[tgt].end());
        // simple invariant check (for speed, need to be enhanced)
        if (u.implies (conjoin(chk, m_efac), replaceAll(newGuess, ruleManager.invVars[tgt], hr->dstVars)))
          candidates[tgt].insert(newGuess);
      }
    }

    Expr getForallCnj (Expr cands)
    {
      ExprSet cnj;
      getConj(cands, cnj);
      for (auto & cand : cnj)
        if (isOpX<FORALL>(cand)) return cand;
      return NULL;
    }

    bool equalCands(map<Expr, ExprSet>& cands)
    {
      for (auto & a : candidates)
      {
        if (a.second.size() != cands[a.first].size()) return false;
        if (!u.isEquiv(conjoin(a.second, m_efac), conjoin(cands[a.first], m_efac))) return false;
      }
      return true;
    }

    Result_t guessAndSolve()
    {
      if(debug >= 3) outs() << "\n    GUESS AND SOLVE\n=======================\n";
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        worklist.push_back(&hr);
      }

      while (true)
      {
        auto candidatesTmp = candidates;
        for (bool fwd : { false, true })
        {
          if (debug>=7)
          {
            outs () << "iter " << globalIter << "." << fwd << "\nCurrent candidates:\n";
            printCands(false);
          }
          declsVisited.clear();
          declsVisited.insert(ruleManager.failDecl);
          propagate(fwd);
          filterUnsat();
          if (fwd) multiHoudini(worklist);  // i.e., weaken
          else strengthen();
          filterUnsat();
          if (checkAllOver(true)) return Result_t::UNSAT;
        }
        if (equalCands(candidatesTmp)) break;
        if (hasArrays) break; // just one iteration is enough for arrays (for speed)
      }

      getImplicationGuesses(candidates);  // seems broken now; to revisit completely
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      for (auto tgt : ruleManager.decls) arrayGuessing(tgt->left());
      filterUnsat();
      multiHoudini(worklist);
      if (checkAllOver(true)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    void sanitizeForDump(string & in)
    {
      in.erase(remove(in.begin(), in.end(), '_'), in.end());
      in.erase(remove(in.begin(), in.end(), '|'), in.end());

      map<char,char> substmap;
      // substmap['_'] = 'U';
      // substmap['|'] = 'B';
      substmap['\''] = 'P';
      substmap['$'] = 'D';
      substmap[':'] = 'C';
      substmap[';'] = 'c';

      for (size_t i = 0; i < in.size(); i++) {
        auto subst = substmap.find(in[i]);
        if (subst != substmap.end()) {
          in[i] = subst->second;
        }
      }
      // std::replace(in.begin(), in.end(), '\'', 'p');
      // std::replace(in.begin(), in.end(), '$', 'D');
      // std::replace(in.begin(), in.end(), ':', 'C');
    }

    void printAllVarsRels(const ExprSet & allVars, stringstream & decls, bool sygus = false, map<Expr, ExprVector> syvars = map<Expr, ExprVector>())
    {
      for (auto v : allVars) {
        decls << "(declare-var " << *v << " " << u.varType(v) << ")\n";
      }

      for (auto d : ruleManager.decls) {
        if (d == ruleManager.failDecl) continue;
        if (sygus) {
          decls << "(synth-fun " << *(d->left()) << " (";
          if (syvars.find(d->left()) != syvars.end()) {
            for (auto var : syvars[d->left()]) {
              decls << "( " << *var << " " << u.varType(var) << ")";
            }
          } else {
            for (auto itr = ruleManager.invVars[d->left()].begin(), end = ruleManager.invVars[d->left()].end(); itr != end; ++itr) {
              decls << "( " << *itr << " " << u.varType(*itr) << ")";
            }
          }
          decls << ") Bool)\n";
        } else {
          decls << "(declare-rel " << *bind::fname(d) << " (";
          for (unsigned i = 0; i < bind::domainSz(d); i++)
          {
            Expr ty = bind::domainTy(d, i);
            if (isOpX<BOOL_TY>(ty)) decls << "Bool ";
            else if (isOpX<REAL_TY>(ty)) decls << "Real ";
            else if (isOpX<INT_TY>(ty)) decls << "Int ";
            else decls << "UnSupportedSort";
          }
          decls << ")) \n";
        }
      }
    }

    string dumpToFile(stringstream & decls, stringstream & rules, string oldsmt = "", string postfix = "", bool sygus = false)
    {
      if (oldsmt.size() == 0) {
        oldsmt = ruleManager.infile;
      }

      string newsmt = oldsmt.substr(oldsmt.find_last_of("/"));
      newsmt = "/tmp/" + newsmt.substr(0, newsmt.find_last_of("."));
      newsmt += postfix + "_" + to_string(std::chrono::system_clock::now().time_since_epoch().count());
      newsmt += sygus ? ".sl" : ".smt2";

      if(debug >= 3) outs() << "newsmt: " << newsmt << "\n";

      string ds = decls.str();
      string rs = rules.str();

      sanitizeForDump(ds);
      sanitizeForDump(rs);

      ofstream newsmtFile(newsmt);
      newsmtFile << ds << "\n" << rs << "\n";
      newsmtFile.close();

      return newsmt;
    }

    ExprVector getUnderConsRels(bool recurse = true)
    {
      ExprVector ucRels = getAllRels();

      for (auto uItr = ucRels.begin(); uItr != ucRels.end();) {
        bool found = false;
        for (auto & hr : ruleManager.chcs) {
          if (hr.isQuery) continue;
          if (hr.dstRelation == *uItr && hr.srcRelations.size() == 0) {
            found = true;
            break;
          }
        }
        if (found) {
          uItr = ucRels.erase(uItr);
        } else {
          ++uItr;
        }
      }

      for (auto uItr = ucRels.begin(); uItr != ucRels.end();) {
        bool update = false;
        for (auto & hr : ruleManager.chcs) {
          if (hr.isQuery) continue;
          if (hr.dstRelation != *uItr) continue;
          bool found;
          for (auto src : hr.srcRelations) {
            if (find(ucRels.begin(), ucRels.end(), src) != ucRels.end()) {
              found = true;
              break;
            }
          }
          if (!found) {
            update = true;
            break;
          }
        }
        if (update) {
          (void)ucRels.erase(uItr);
          uItr = ucRels.begin();
        } else {
          uItr++;
        }
      }

      return ucRels;
    }

    void getCurSoln(map<Expr, ExprSet> & soln, const ExprVector & rels, map<Expr, ExprVector> & invVars)
    {
      // outs() << "getcursoln: \n";
      for (auto r : rels) {
        soln[r].clear();
        for (auto e : candidates) {
          string saneName = lexical_cast<string>(*r);
          sanitizeForDump(saneName);
          if (saneName == lexical_cast<string>(*(e.first))) {
            // outs() << "rel: " << *r << "\n cands: " << *(conjoin(e.second, m_efac)) << "\n";
            for (auto c : e.second) {
              soln[r].insert(replaceAll(c, ruleManager.invVars[e.first], invVars[r]));
            }
          }
        }
      }
    }

    Result_t getWeakerSoln(const Expr & rel, const ExprVector & rels, const string & newsmt, map<Expr, ExprSet> & soln)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newsmt);
      if(debug >= 2) outs() << "getWeakerSoln\n";
      NonlinCHCsolver newNonlin(nrm, 1, 1, 1, debug);
      ExprVector query;

      Result_t res = newNonlin.guessAndSolve();
      assert(res != Result_t::SAT);

      if (res == Result_t::UNSAT) {
        newNonlin.getCurSoln(soln, rels, ruleManager.invVars);
        return Result_t::SAT;
      }

      return Result_t::UNKNOWN;
    }

    void dumpSMT(const ExprVector & constraints, const ExprSet & allVars, const bool newenc = false)
    {
      stringstream asserts;
      stringstream decls;

      printAllVarsRels(allVars, decls);

      for (auto c : constraints) {
        asserts << "(assert ";
        u.print(c, asserts);
        asserts << ")\n";
      }

      asserts << "(check-sat)\n(get-model)\n";

      dumpToFile(decls, asserts, ruleManager.infile, newenc ? "_smt_V2_" : "_smt_");

    }

    Result_t checkMaximalSMT(ExprVector & weakenRels, ExprVector & fixedRels, map<Expr, Expr> & soln, ExprVector rels = ExprVector())
    {
      map<Expr, ExprVector> newVars;
      map<Expr, ExprVector> newVarsp;
      map<Expr, Expr> newCand;
      map<Expr, Expr> newCandp;

      if(debug >= 2) outs() << "checkMaximalSMT\n";

      for (auto rel : rels) {
        string relName = lexical_cast<string>(*(rel));
        if(debug >= 2) outs() << "relName: " << relName << "\n";

        ExprVector tvars;
        ExprVector tvarsp;
        ExprVector eqVars;
        ExprVector eqVarsp;
        for (int i = 0; i < ruleManager.invVars[rel].size(); i++) {
          Expr var = ruleManager.invVars[rel][i];
          string name_suff = relName + "_" + to_string(i);
          Expr newVar = cloneVar(var, mkTerm<string>("_MAX_" + name_suff, m_efac));
          Expr newVarp = cloneVar(var, mkTerm<string>("_MAXP_" + name_suff, m_efac));
          tvars.push_back(newVar);
          tvarsp.push_back(newVarp);
          eqVars.push_back(mk<EQ>(var, newVar));
          eqVarsp.push_back(mk<EQ>(var, newVarp));
        }
        Expr curCand = conjoin(candidates[rel], m_efac);
        newCand.insert({rel, mk<OR>(curCand, conjoin(eqVars, m_efac))});
        newCandp.insert({rel, mk<OR>(curCand, conjoin(eqVarsp, m_efac))});
        newVars.insert({rel, tvars});
        newVarsp.insert({rel, tvarsp});
      }

      ExprVector constraints;

      //weaker solution constraint
      if (rels.size() > 0) {
        //at least one solution should be weaker
        ExprVector disj;
        for (auto rel : rels) {
          Expr cand = mk<NEG>(conjoin(candidates[rel], m_efac));
          cand = replaceAll(cand, ruleManager.invVars[rel], newVars[rel]);
          disj.push_back(cand);
        }
        constraints.push_back(disjoin(disj, m_efac));
      }

      map<Expr, ExprVector> funcs;
      ExprSet allVars;

      for (auto hr : ruleManager.chcs)
      {
        ExprSet antec;
        bool addVacuity = false;

        if(hr.srcRelations[0] == specDecl) {
          addVacuity = true;
          if(debug >= 3) outs() << "Rel: " << hr.srcRelations[0] << "\n";
          if(debug >= 3) outs() << "addVacuity = true!\n";
        }

// remove this block
        for (int i = 0; i < hr.srcRelations.size(); i++) {
          if (find(fixedRels.begin(), fixedRels.end(), hr.srcRelations[i]) != fixedRels.end()) {
            Expr curCand = conjoin(candidates[hr.srcRelations[i]], m_efac);
            antec.insert(replaceAll(curCand, ruleManager.invVars[hr.srcRelations[i]], hr.srcVars[i]));
          } else if (find(rels.begin(), rels.end(), hr.srcRelations[i]) == rels.end()) {
            for (auto d : ruleManager.decls) {
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.srcRelations[i]))) {
                Expr t = bind::fapp(d, hr.srcVars[i]);
                funcs.insert({t, hr.srcVars[i]});
                antec.insert(t);
                addVacuity = true;
                break;
              }
            }
          } else {
            Expr t = replaceAll(newCand[hr.srcRelations[i]], ruleManager.invVars[hr.srcRelations[i]], hr.srcVars[i]);
            antec.insert(t);
          }
        }

        Expr conseq;

        if (!hr.isQuery) {
          antec.insert(hr.body);
          if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
            Expr curCand = conjoin(candidates[hr.dstRelation], m_efac);
            conseq = replaceAll(curCand, ruleManager.invVars[hr.dstRelation], hr.dstVars);
          } else if (find(rels.begin(), rels.end(), hr.dstRelation) == rels.end()) {
            for (auto d : ruleManager.decls) {
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
          Expr t = bind::fapp(d, hr.dstVars);
          conseq = t;
          // funcs.push_back(t);
          break;
              }
            }
          } else {
            conseq = replaceAll(newCand[hr.dstRelation], ruleManager.invVars[hr.dstRelation], hr.dstVars);
          }
        } else {
          conseq = mkNeg(hr.body);
        }

        ExprVector forallArgs;
        // ExprVector existsArgs;

        for (int i = 0; i < hr.srcRelations.size(); i++) {
          for (auto v : hr.srcVars[i]) {
            forallArgs.push_back(v->left());
            allVars.insert(v);
          }

          for (auto nv : newVars[hr.srcRelations[i]]) {
            // existsArgs.push_back(nv->left());
            allVars.insert(nv);
          }
        }

        for (auto v : hr.dstVars) {
          forallArgs.push_back(v->left());
          allVars.insert(v);
        }

        for (auto nv : newVarsp[hr.dstRelation]) {
          // existsArgs.push_back(nv->left());
          allVars.insert(nv);
        }

        for (auto lv : hr.locVars) {
          forallArgs.push_back(lv->left());
          allVars.insert(lv);
        }
        if(debug >= 3) outs() << "forallArgs\n";
        if(debug >= 3) pprint(forallArgs, 2);
        // existsArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), conseq));
        // forallArgs.push_back(mknary<EXISTS>(existsArgs));

        // Try to change IMPL to AND after trying set addVacuity to true;
        if(addVacuity) forallArgs.push_back(mk<AND>(conjoin(antec, m_efac), conseq));
        else forallArgs.push_back(mk<IMPL>(conjoin(antec, m_efac), conseq));
        constraints.push_back(mknary<FORALL>(forallArgs));

        // Add this back if things go weird...
      /*  if (addVacuity) {
          if(debug >= 2) outs() << "addVacuity\n";
          forallArgs.pop_back();
          forallArgs.push_back(conjoin(antec, m_efac));
          constraints.push_back(mknary<EXISTS>(forallArgs));
        }*/
      }

      //DEBUG
      dumpSMT(constraints, allVars);
      if(debug >= 5) outs() << "constraints\n";
      if(debug >= 5) pprint(constraints, 2);
      boost::tribool res = u.isSat(constraints);

      if (boost::logic::indeterminate(res)) {
        if(debug >= 3) outs() << "result is indeterminate \n";//DEBUG
        return Result_t::UNKNOWN;

      } else if (!res) {
        if(debug >= 3) outs() << "result is unsat!!\n";//DEBUG
        return Result_t::UNSAT;
      }

      //debug
      // u.printModel();
      // for (auto func : funcs) {
      // 	Expr fm = u.getModel(func.first);
      // 	outs() << *(func.first) << " -> " << *fm << "\n";
      // }

      for (auto rel : rels) {
        Expr model = u.getModel(newVars[rel]);
        if(debug >= 3) outs() << "model: " << *model << "\n";//DEBUG
        Expr weakerSoln = mk<OR>(conjoin(candidates[rel],m_efac), replaceAll(model, newVars[rel], ruleManager.invVars[rel]));
        soln.insert({rel, weakerSoln});
        if(debug >= 3) outs() << "weakersoln: " << *weakerSoln << "\n";//DEBUG
      }

      for (auto d : ruleManager.decls) {
        if (find(rels.begin(), rels.end(), d->left()) != rels.end()) continue;
        for (auto func : funcs) {
          if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*((func.first)->left()->left()))) {
            soln.insert({d->left(), replaceAll(u.getModel(func.first), func.second, ruleManager.invVars[d->left()])});
            break;
          }
        }
      }

      // //debug
      // for (auto se : soln) {
      // 	outs() << *(se.first) << "->\n";
      // 	outs() << *(se.second) << "\n";
      // }
      // for (auto ce : candidates) {
      // 	outs() << *(ce.first) << "->\n";
      // 	for (auto c : ce.second)
      // 	  outs() << *c << "\n";
      // }

      if (rels.size() > 0) {
        for (auto d : ruleManager.decls) {
          Expr rel = d->left();
          if (find(fixedRels.begin(), fixedRels.end(), rel) != fixedRels.end()) continue;
          if (u.isSat(soln[rel], mk<NEG>(conjoin(candidates[rel], m_efac)))) {
            weakenRels.push_back(rel);
          } else {
            fixedRels.push_back(rel);
          }
        }
      }
      if(debug >= 5) outs() << "*** returning SAT ***\n";
      return Result_t::SAT;

    }

    ExprVector getAllRels()
    {
      ExprVector retRels;

      for (auto d : ruleManager.decls) {
        retRels.push_back(d->left());
      }

      return retRels;
    }

    // Adds two new rules in addition to the rules present in 'oldsmt':
    // 1) candidate[rel](invVars[rel]) => rel(invVars[rel])
    // 2) ~candidate[rel](invVars[rel]) /\ tmprel(invVars[rel]) => rel(invVars[rel])
    // returns the name of the file where new rules are present
    string constructWeakeningRules(const ExprVector & weakenRels, const ExprVector & fixedRels)
    {
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = isOpX<FALSE>(ruleManager.failDecl) ? "fail" : lexical_cast<string>(ruleManager.failDecl);

      for (auto inve : ruleManager.invVars) {
        allVars.insert(inve.second.begin(), inve.second.end());
      }

      for (auto rel : weakenRels) {

        const string tmpRelName = "tmprel" + lexical_cast<string>(*rel);

        newDecls << "(declare-rel " << tmpRelName << " (";
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          newDecls << " " << u.varType(*itr);
        }
        newDecls << "))\n";

        //candidate[rel] => rel
        newRules << "(rule (=> ";
        Expr e = simplifyBool(conjoin(candidates[rel], m_efac)); //done to avoid single disjunct, which is causing crash later
        u.print(e, newRules);
        newRules << "( " << *rel;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")))\n";

        //~candidate[rel] /\ tmprel => rel
        newRules << "(rule (=> (and ";
        u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
        newRules << "( " << tmpRelName;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")) ( " << *rel;
        for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
          if (itr != ruleManager.invVars[rel].begin())
            newRules << " ";
          newRules << " " << *itr;
        }
        newRules << ")))\n";
      }


      for (auto & hr : ruleManager.chcs)
      {
        for (int i = 0; i < hr.srcVars.size(); i++) {
          allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
        }
        allVars.insert(hr.locVars.begin(), hr.locVars.end());
        allVars.insert(hr.dstVars.begin(), hr.dstVars.end());

        ExprSet antec;
        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr src = hr.srcRelations[i];
          if (find(fixedRels.begin(), fixedRels.end(), src) != fixedRels.end()) {
            Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
            antec.insert(t);

          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
          Expr t = bind::fapp(d, hr.srcVars[i]);
          antec.insert(t);
          break;
              }
          }
        }

        antec.insert(hr.body);
        Expr conseq;
        bool addFail = false;

        if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
          antec.insert(mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars)));
          addFail = true;
        } else {
          if (hr.isQuery) {
            addFail = true;
          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
          conseq = bind::fapp(d, hr.dstVars);
          break;
              }
          }
        }

        if (addFail) {
          newRules << "(rule (=> ";
          u.print(conjoin(antec, m_efac), newRules);
          newRules << " " << queryRelStr << "))\n";
        } else {
          newRules << "(rule ";
          u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
          newRules << ")\n";
        }
        //debug
        // outs() << newRules.str();
      }
      printAllVarsRels(allVars, newDecls);
      newDecls << "(declare-rel " << queryRelStr << "())\n";
      newRules << "(query " << queryRelStr << ")\n";
      return dumpToFile(newDecls, newRules, ruleManager.infile);
    }

    Result_t solveWeakCHC(const string & newsmt, map<Expr, ExprSet> & soln)
    {
      EZ3 z3(m_efac);
      CHCs nrm(m_efac, z3);
      nrm.parse(newsmt);
      if(debug >= 3) outs() << "solveWeakCHC\n";
      nrm.print();
      NonlinCHCsolver newNonlin(nrm, 1, 1, 1, debug);
      ExprVector query;

      Result_t res = newNonlin.guessAndSolve();
      assert(res != Result_t::SAT);

      if (res == Result_t::UNSAT) {
        ExprVector allRels = getAllRels();
        newNonlin.getCurSoln(soln, allRels, ruleManager.invVars);
        return Result_t::SAT;
      }

      return Result_t::UNKNOWN;
    }

    // chc solver based weaker solution synthesis
    Result_t weakenUsingCHC(const ExprVector & weakenRels, const ExprVector & fixedRels)
    {
      if(debug >= 3) outs() << "weakenUsingCHC\n";
      string newsmt;
      newsmt = constructWeakeningRules(weakenRels, fixedRels);
      map<Expr, ExprSet> soln;
      if(debug >= 3) outs() << "Entering solveWeakCHC\n";
      Result_t res = solveWeakCHC(newsmt, soln);
      if(debug >= 3) outs() << "Left solveWeakCHC\n";
      if (res == Result_t::SAT) {
        // outs() << "CHC proved s\n";
        for (auto e : soln) {
          if (find (fixedRels.begin(), fixedRels.end(), e.first) == fixedRels.end()) {
              candidates[e.first].clear();
              candidates[e.first].insert(e.second.begin(), e.second.end());
          }
        }
      }
      return res;
    }

    // TODO: move the entire SyGuS-translation to some helper class
    string constructWeakeningSygus(const ExprVector & weakenRels, const ExprVector & fixedRels, map<Expr, ExprVector> & syvars, bool firstTime = false)
    {
      stringstream newRules;
      stringstream newDecls;
      ExprSet allVars;
      string queryRelStr = "false";

      for (auto inve : ruleManager.invVars) {
        allVars.insert(inve.second.begin(), inve.second.end());
      }

      newDecls << "(set-logic LIA)\n";

      if (!firstTime) {
        for (auto rel : weakenRels) {
          const string tmpRelName = "tmprel" + lexical_cast<string>(*rel);

          newDecls << "(synth-fun " << tmpRelName << " (";
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            newDecls << "( " << *itr << " " << u.varType(*itr) << ")";
          }
          newDecls << ") Bool)\n";

          //candidate[rel] => rel
          newRules << "(constraint (=> ";
          Expr e = simplifyBool(conjoin(candidates[rel], m_efac)); //done to avoid single disjunct, which is causing crash later
          u.print(e, newRules);
          newRules << "( " << *rel;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << "  ";
            newRules << " " << *itr;
          }
          newRules << ")))\n";

          //~candidate[rel] /\ tmprel => rel
          newRules << "(constraint (=> (and ";
          u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
          newRules << "( " << tmpRelName;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << ")) ( " << *rel;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << ")))\n";

          //vacuity
          newRules << "(constraint (exists ( ";
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            newRules << "( " << *itr << " " << u.varType(*itr) << ")";
          }
          newRules << ") (and";
          u.print(mk<NEG>(conjoin(candidates[rel], m_efac)), newRules);
          newRules << "( " << tmpRelName;
          for (auto itr = ruleManager.invVars[rel].begin(), end = ruleManager.invVars[rel].end(); itr != end; ++itr) {
            if (itr != ruleManager.invVars[rel].begin())
              newRules << " ";
            newRules << " " << *itr;
          }
          newRules << "))))\n";
        }
      }

      for (auto rel : weakenRels) {
        //these variables will be used later to get solution from sygus solver
        ExprVector newvars;
        for (int i = 0; i < ruleManager.invVars[rel].size(); i++) {
          Expr var = ruleManager.invVars[rel][i];
          Expr newVar;
          string varname =  "sygus" + lexical_cast<string>(*rel) + to_string(i);
          sanitizeForDump(varname);
          if (bind::isIntConst(var)) {
            newVar = bind::intConst(mkTerm<string>(varname, m_efac));
          } else if (bind::isRealConst(var)) {
            newVar = bind::realConst(mkTerm<string>(varname, m_efac));
          } else if (bind::isBoolConst(var)) {
            newVar = bind::intConst(mkTerm<string>(varname, m_efac));
          } else {
            outs() << "Unsupport vartype: " << u.varType(var) << "\n";
            assert(0);
          }
          newvars.push_back(newVar);
        }
        syvars.insert({rel, newvars});
      }

      for (auto & hr : ruleManager.chcs)
      {
        for (int i = 0; i < hr.srcVars.size(); i++) {
          allVars.insert(hr.srcVars[i].begin(), hr.srcVars[i].end());
        }
        allVars.insert(hr.locVars.begin(), hr.locVars.end());
        allVars.insert(hr.dstVars.begin(), hr.dstVars.end());

        ExprSet antec;
        for (int i = 0; i < hr.srcRelations.size(); i++) {
          Expr src = hr.srcRelations[i];
          if (find(fixedRels.begin(), fixedRels.end(), src) != fixedRels.end()) {
            Expr t = replaceAll(conjoin(candidates[src], m_efac), ruleManager.invVars[src], hr.srcVars[i]);
            antec.insert(t);
          } else {
            for (auto d : ruleManager.decls)
              if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*src)) {
          Expr t = bind::fapp(d, hr.srcVars[i]);
          antec.insert(t);
          break;
	      }
      }
    }

    //vacuity
    if (!hr.isQuery) {
      antec.insert(hr.body);
    }

    if (hr.srcRelations.size() != 0) {
      newRules << "(constraint (exists ( ";
      for (int i = 0; i < hr.srcVars.size(); i++) {
        for (auto sv : hr.srcVars[i])
          newRules << "( " << *sv << " " << u.varType(sv) << ")";
      }
      for (int i = 0; i < hr.dstVars.size(); i++) {
        newRules << "( " << *(hr.dstVars[i]) << " " << u.varType(hr.dstVars[i]) << ")";
      }
      for (int i = 0; i < hr.locVars.size(); i++) {
        newRules << "( " << *(hr.locVars[i]) << " " << u.varType(hr.locVars[i]) << ")";
      }
      newRules << ")";
      u.print(conjoin(antec, m_efac),  newRules);
      newRules << "))\n";
    }

    Expr conseq;
    bool addFail = false;

    if (find(fixedRels.begin(), fixedRels.end(), hr.dstRelation) != fixedRels.end()) {
      antec.insert(mk<NEG>(replaceAll(conjoin(candidates[hr.dstRelation], m_efac), ruleManager.invVars[hr.dstRelation], hr.dstVars)));
      addFail = true;
    } else {
      if (hr.isQuery) {
        antec.insert(hr.body);
        addFail = true;
      } else {
        for (auto d : ruleManager.decls)
          if (lexical_cast<string>(*bind::fname(d)) == lexical_cast<string>(*(hr.dstRelation))) {
            conseq = bind::fapp(d, hr.dstVars);
            break;
          }
        }
      }

      if (addFail) {
        newRules << "(constraint (=> ";
        u.print(conjoin(antec, m_efac), newRules);
        newRules << " " << queryRelStr << "))\n";
      } else {
        newRules << "(constraint ";
        u.print(mk<IMPL>(conjoin(antec, m_efac), conseq), newRules);
        newRules << ")\n";
      }
      //debug
      // outs() << newRules.str();
      }
      printAllVarsRels(allVars, newDecls, true, syvars);
      // newDecls << "(declare-rel " << queryRelStr << "())\n";
      // newRules << "(query " << queryRelStr << ")\n";
      newRules << "(check-synth)\n";
      return dumpToFile(newDecls, newRules, ruleManager.infile, "_sygus_", true);
    }

    Result_t solveWeakSygus(map<Expr, ExprVector> & syvars, const ExprVector & weakenRels, const string & slfile, map<Expr, Expr> & soln)
    {
      // const string SYGUS_BIN = "/home/u1392220/tmp/max_synth/ws/modver/build/run_sygus.sh";
      const string output = slfile.substr(0, slfile.find_last_of(".")) + ".out";
//      outs() << "starting sygus on file " << slfile << "\n";
      string cmd = SYGUS_BIN + " " + slfile + " >" + output;
      outs() << "all " << cmd << "\n";
      int sysret = system(cmd.c_str());
      if (sysret == -1 || WEXITSTATUS(sysret) != 0) {
        return Result_t::UNKNOWN;
      }

      EZ3 z3(m_efac);

      ifstream tmpinfile(output.c_str());
      if (!tmpinfile) {
        return Result_t::UNKNOWN;
      }
      stringstream tmpinstream;
      tmpinstream << tmpinfile.rdbuf();
      tmpinfile.close();
      string defs(tmpinstream.str());

      for (auto rel : weakenRels)
      {
        stringstream smtstream;
        smtstream << defs;
        for (auto sv : syvars[rel]) {
          smtstream << "(declare-fun " << *sv << " () " << u.varType(sv) << ")\n";
        }

        string sanerelname = lexical_cast<string>(*rel);
        sanitizeForDump(sanerelname);
        smtstream <<  "(assert( " + sanerelname;
        for (int i = 0; i < syvars[rel].size(); i++) {
          smtstream << " " + lexical_cast<string>(*(syvars[rel][i]));
        }
        smtstream << "))\n";
        smtstream << "(check-sat)\n";
        // outs() << smtstream.str();

        try {
          Expr funcAsserts = z3_from_smtlib(z3, smtstream.str());
          soln.insert({rel, replaceAll(funcAsserts, syvars[rel], ruleManager.invVars[rel])});

        } catch (z3::exception &e){
          char str[3000];
          strncpy(str, e.msg(), 300);
          outs() << "z3 exception: " << str << " while reading : " << smtstream.str() <<"\n";
          return Result_t::UNKNOWN;
        }
      }

      //debug
      // outs() << "soln from sygus: \n";
      // for (auto se : soln) {
      // 	outs() << *(se.first) << " -> " << *(se.second) << "\n";
      // }

      return Result_t::SAT;
    }

    Result_t weakenUsingSygus(const ExprVector & weakenRels, const ExprVector & fixedRels, const bool & firstTime = false)
    {
      map<Expr, ExprVector> syvars;
      string newsl = constructWeakeningSygus(weakenRels, fixedRels, syvars, firstTime);
      map<Expr, Expr> soln;

      Result_t res = solveWeakSygus(syvars, weakenRels, newsl, soln);

      if (res == Result_t::SAT) {
      	// outs() << "sygus proved s\n";
      	for (auto e : soln) {
      	  if (find (fixedRels.begin(), fixedRels.end(), e.first) == fixedRels.end()) {
      	      candidates[e.first].clear();
      	      candidates[e.first].insert(e.second);
      	  }
      	}
      }

      //flip the result as caller expects unsat first time; argh!
      if (firstTime) {
        if (res == Result_t::UNSAT) {
          res = Result_t::SAT;
        } else if (res == Result_t::SAT) {
          res = Result_t::UNSAT;
        }
      }

      return res;
    }

    ExprVector vecDiff(ExprVector vec1, ExprVector vec2) {
      ExprVector diff;
      for (auto v1 : vec1) {
        if (find (vec2.begin(), vec2.end(), v1) == vec2.end()) {
          diff.push_back(v1);
        }
      }
      return diff;
    }

    ExprSet parseForGuards(ExprSet& grds) { // return bool
      ExprSet exp;
      if(debug >= 3) outs() << "Begin parsing for guards\n";
      for(auto e = candidates[specDecl].begin(); e != candidates[specDecl].end() ; e++) {
        if(contains(*e,ghostVars[0]) || contains(*e,ghostVars[1])) {
          // add the ghost formula here. size is one and is Equality of form gh = ....
        }
        else {
          Expr r = replaceAll(*e, fc->srcVars[0],invVars);
          exp.insert(normalize(r));
        }
      }
      if(exp.empty()) exp.insert(mk<TRUE>(m_efac));
      grds.insert(conjoin(exp, m_efac));
      if(debug >= 3) {
        outs() << "End parsing for guards\n";
      }
      return exp;
    }

    map<Expr, ExprSet> ghCandMap;
    ExprSet usedGhCands; // remember previously failed usedGhCands.
    map<Expr,Expr> grds2gh; // associate a guard (phi(vars)) with a precond of gh (f(vars))

    void printGhSoln() {
      Expr l = ghostVars[0];
      Expr r;
      Expr phi;
      ExprVector phiV;
      bool zero = true, good = false;

      if(!u.isSat(fcBodyInvVars,mkNeg(loopGuard))) {
        if(debug >= 3) outs() << "ZERO LOOP EXE IS NOT POSSIBLE ON INPUT\n";
        zero = false;
      }
      auto m = grds2gh.rbegin();
      auto b = grds2gh.rend();

      for(; m != b; m++) {
        good = true;
        if(!zero && m == grds2gh.rbegin()) {
          if(isOpX<MULT>(m->second->left())) {
            r = mk<DIV>(m->second->right(),m->second->left()->left());
          }
          else {
            r = m->second->right();
          }
        }
        else if(m == grds2gh.rbegin()) {
          if(isOpX<MULT>(m->second->left())) {
            r = mk<ITE>(m->first,mk<DIV>(m->second->right(),m->second->left()->left()), mpzZero);
          }
          else {
            r = mk<ITE>(m->first,m->second->right(), mpzZero);
          }
        }
        else {
          if(isOpX<MULT>(m->second->left())) {
            r = mk<ITE>(m->first,mk<DIV>(m->second->right(),m->second->left()->left()), r);
          }
          else {
            r = mk<ITE>(m->first,m->second->right(), r);
          }
        }
      }
      if(r != NULL) {
        l = mk<EQ>(l,r);
        u.print(l);
        outs() << "\n";
      }

    }

    Expr implyWeakening(Expr e) {
      Expr l;
      Expr j = e;
      if(e->left()->arity() != 2) {
        if(debug >= 5) outs() << "arity != 2\n";
        return e;
      }

      if(isOpX<EQ>(e)) {
        if(containsOp<UN_MINUS>(e->left())) {
          if(isOpX<MPZ>(e->right()) && e->right() != mpzZero) {
            cpp_int i = lexical_cast<cpp_int>(e->right());
            l = e->left();
            if(i > 0) {
              if(isOpX<UN_MINUS>(l->left())) {
                j = mk<LT>(l->left()->left(),l->right());
              }
              else {
                j = mk<LT>(l->right()->left(),l->left());
              }
            }
            else {
              if(isOpX<UN_MINUS>(l->left())) {
                j = mk<LT>(l->right(),l->left()->left());
              }
              else {
                j = mk<LT>(l->left(),l->right()->left());
              }
            }
          }
        }
      }

      if(u.implies(e,j)) e = j;
      return e;
    }

    boost::tribool boundSolve(Expr block, Result_t prevRes = Result_t::UNKNOWN) {
      map<Expr,ExprSet> bounds;
      dataGrds.clear();
      if(debug >= 2) {
        outs() << "EXPLOREBOUNDS\n";
        outs() << "=============\n";
      }
      boost::tribool res = exploreBounds(bounds, block); // maybe hold previously computed bounds in a global ExprSet to avoid duplication.
      if(debug >= 2) {
        outs() << "EXPLOREBOUNDS is finished\n";
      }
      // See if anything comes from using previous concrete datacands
//      if(!res) res = exploreBounds(bounds, mkNeg(disjoin(concrtBounds,m_efac)));
      ExprSet grds;
      if(dg) {
        for(auto& e: dataGrds) {
          Expr w = implyWeakening(e);
          if(debug >= 3) outs() << "Adding guard from data: " << w << "\n";
          grds.insert(w);
        }
      }
//      if(debug >= 2) for(auto& e: grds) outs() << "  grd: " << e << "\n";

      // check for previously explored bound.
      for(auto& prev: usedGhCands) {
        auto i = bounds[invDecl].begin(), end = bounds[invDecl].end();
        while(i != end) {
          if(prev == *i) i = bounds[invDecl].erase(i);
          else i++;
        }
      }
      if(bounds[invDecl].size() == 0) res = false;

      if(debug >= 2) {
        outs() << "Bounds found this iteration\n";
        for(auto& e: bounds[invDecl]) {
          outs() << "  " << e << "\n";
        }
      }
      if(res && debug >= 3) {
        outs() << "res is true\n";
      }
      else if(debug >= 3) {
        outs() << "res is false\n";
      }

      if(debug >= 2 && bounds[invDecl].size() > 0) outs() << "\nentering loop\n";
      for(auto b = bounds[invDecl].begin(), end = bounds[invDecl].end(); b != end && res; b++) { // change to go over iterators.
        candidates.clear();

        if(debug >= 2) outs() << "- - - b: " << *b << "\n";

        candidates[specDecl].insert(replaceAll(*b, tr->srcVars[0], fc->srcVars[0]));
        candidates[invDecl].insert(*b);
        for(auto& e: grds) {
          candidates[specDecl].insert(replaceAll(e, tr->srcVars[0], fc->srcVars[0]));
          candidates[invDecl].insert(e);
        }
        usedGhCands.insert(*b); // to remember what has been previously used.

        if(debug >= 2) {
          outs() << "Cands going to G&S\n";
          printCands(false);
        }
        Result_t res_t = guessAndSolve();
        if(debug >= 2) outs() << "finished G&S\n";
        u.removeRedundantConjuncts(candidates[invDecl]);
        u.removeRedundantConjuncts(candidates[specDecl]);
        if(debug >= 2) {
          printCands(false);
        }
/*
        if(!contains( // if G&S removed the ghCand then clear and move on.
              normalize(conjoin(candidates[specDecl],m_efac),ghostVars[1]),
                replaceAll(*b, tr->srcVars[0], fc->srcVars[0]))) {
          printCands(false);
          candidates.clear();
          outs() << "G&S removed cand\n";
          continue;
        }
*/
        if(res_t == Result_t::UNKNOWN) {
          if(std::next(b) == end) {
            if(debug >= 4) outs() << "* * * CLEARING CANDS\n";
            candidates.clear();
          }
          else {
            candidates[specDecl].erase(replaceAll(*b, tr->srcVars[0], fc->srcVars[0]));
            candidates[invDecl].erase(*b);
          }
          if(debug >= 2) outs() << "=====> unknown\n\n";
          continue;
        }

        // If you're here then G&S returned UNSAT
        if(debug >= 3) {
          printCands(false);
        }

        parseForGuards(grds);
        // add assertion to say no gh vars are in cands
        // Associate grds with the precond.
        grds2gh[conjoin(grds, m_efac)] = *b;

        if(debug >= 3) pprint(grds,2);

        for(auto& g: grds2gh) {
          grds.insert(g.first);
        }

        Expr grd = disjoin(grds,m_efac);
        if(debug >= 4) outs() << "grd: " << grd << "\n";
        if(u.isSat(mkNeg(grd), fcBodyInvVars, loopGuard)) {
          //Expr mdl = u.getModel();
          if(boundSolve(mkNeg(grd),res_t)) return true;
        }
        else return true;
      }
      return false;
    }

    void boundSolve()
    {
      Expr block = mk<TRUE>(m_efac);
      if(boundSolve(block)) {
        u.removeRedundantConjuncts(candidates[invDecl]);
        u.removeRedundantConjuncts(candidates[specDecl]);
        outs() << "unsat\n";
        printGhSoln();
        if(printGsSoln) printCands(true,candidates);
      }
      else {
        candidates.clear();
        if(guessAndSolve() == Result_t::UNSAT) {
          outs() << "G&S: unsat\n";
          u.removeRedundantConjuncts(candidates[invDecl]);
          u.removeRedundantConjuncts(candidates[specDecl]);
          printGhSoln();
          if(printGsSoln) printCands(true,candidates);
        }
        else outs() << "unknown\n";
      }
    }

    void maximalSolve (bool useGAS = true, bool usesygus = false, bool useUC = false, bool fixCRels = false)
    {
      int itr = 0;
      bool firstSMTCall = !useGAS;
      ExprVector allRels = getAllRels();
      ExprVector rels = useUC ? getUnderConsRels() : allRels;

      if(debug >= 5) {
        for(auto& e: allRels) {
          outs() << "allRels: rel: " << e << "\n";
        }
        for(auto& e: rels) {
          outs() << "rels: rel: " << e << "\n";
        }
      }

      if (useGAS) {
        Result_t res;
        if (!usesygus) {
          res = Result_t::UNSAT;//guessAndSolve();

        }  else {
          ExprVector tmpfrels;
          res = weakenUsingSygus(allRels, tmpfrels, true);
        }

        itr++;
        if (hasArrays) {
          switch (res) {
            case Result_t::UNSAT: printCands(); break;
            case Result_t::UNKNOWN: outs() << "unknown\n"; break;
            case Result_t::SAT: outs() << "sat\n"; break;
          }
          return;
        }

        if (res == Result_t::UNSAT && rels.size() == 0) {
          outs() << "Total iterations: "  << itr << "\n";
          //debug
          for (auto hr : ruleManager.chcs) {
            if (!checkCHC(hr, candidates)) {
              outs() << "something is wrong!(after GAS)\n";
              assert(0);
            }
          }
          printCands(true, candidates);
          return;
        }

        if (res == Result_t::SAT) {
          outs() << "sat\n";
          return;
        }

        if (res == Result_t::UNKNOWN){
          // outs() << "unknown\n";
          // return;
          // outs() << "GAS is uk\n";
          firstSMTCall = true;
        }
      }

      Expr block = mk<FALSE>(m_efac);
      bounds.clear();
      ExprSet grds; // hold the guards (phi) of the f(vars) /\ phi(vars) expression)
      Result_t res_t;

      while (true) { // spechorn loop (now..)
        boost::tribool res;
        Result_t maxRes;
        ExprVector weakenRels;
        ExprVector fixedRels = !firstSMTCall && fixCRels ? vecDiff(allRels, rels) : ExprVector() ;
        map<Expr, Expr> smtSoln;

        if(debug) outs() << "current iteration: "<< itr << "\n";
        // Add data candidates here.
        if(ghCandMap[invDecl].empty() || bounds.size() == 1) {
          if(debug >= 3) outs() << "\nEXPLORE BOUNDS\n==============\n";
          res = exploreBounds(ghCandMap, mkNeg(block));
          if(debug >= 4) outs() << "Left exploreBounds\n";
        }

        if(debug >= 3) {
          for(auto& e : ghCandMap[invDecl]) { // print bounds found
            outs() << "- - - GH_CAND FROM DATA: " << e << "\n";
          }
        }

        if(!res && ghCandMap[invDecl].empty()) {
        // short circuit here because loop can't be unrolled with the block.
          if(debug >= 2) {
            outs() << "\n* * * DATALEARNER CANNOT UNROLL WITH BLOCK * * *\n";
          }
          printCands(true,candidates);
          break;
        }
        candidates.clear();
        bounds.clear();
        for(auto& rel: fc->srcRelations) {
          for(auto e = ghCandMap[invDecl].begin(); e != ghCandMap[invDecl].end(); e++) {

            Expr in = replaceAll(*e, tr->srcVars[0], fc->srcVars[0]);
            //bounds.insert(in);
            candidates[rel].insert(in);
            if(debug >= 4) {
              outs() << "Cand added to rel: " << rel;
              outs() << " : " << in <<"\n";
            }
            break;
          }
        }

        for(auto& rel: decls) {
          for(auto e = ghCandMap[invDecl].begin(); e != ghCandMap[invDecl].end(); e++) {
            bounds.insert(*e);
            candidates[rel].insert(*e);
            if(debug >= 4) {
              outs() << "Cand added to rel: " << rel;
              outs() << " :: " << *e <<"\n";
            }
            ghCandMap[invDecl].erase(*e);
            break;
          }
        }
        res_t = guessAndSolve();
        if(debug >= 2) {
          outs() << "Result_t after G&S: ";
          if(res_t == Result_t::UNSAT) outs() << "unsat";
          else outs() << "unknown";
          outs() << "\nCands after G&S:\n";
          printCands(false);
        }
        if(res_t == Result_t::UNKNOWN) {
          candidates.clear();
          continue;
        }
        //parse cands of pre for grds.
        parseForGuards(grds);
        if(debug >= 3) pprint(grds,2);

        //need to check that all the guards from data have been checked.
        if(res_t == Result_t::UNSAT && !u.isSat(mkNeg(disjoin(grds,m_efac)), fcBodyInvVars)) {
          if(debug >= 5) outs() << "=========> breaking main loop\n";
          printCands(true,candidates);
          break;
        }
        // set block to be the conj of !grds.
        block = conjoin(bounds,m_efac);
        if(debug >= 5) outs() << "=========> continue\n";
        if(!hornspec) continue;
// ****************************************************************************

        maxRes = firstSMTCall ? checkMaximalSMT(weakenRels, fixedRels, smtSoln) : checkMaximalSMT(weakenRels, fixedRels, smtSoln, rels);
        itr++;

        if (maxRes == Result_t::UNSAT) {
          if(debug >= 2) outs() << "Total iterations: "  << itr << "\n";

          //debug
          ruleManager.print();
          for (auto hr : ruleManager.chcs) {
            if (!checkCHC(hr, candidates)) { // Some benches are failing here... Why?
              outs() << "something is wrong!(after SMT unsat)\n";

              assert(0);
            }
          }
          printCands(true, candidates);
          return;

        } else if (maxRes == Result_t::UNKNOWN){
          if (firstSMTCall) {
            outs() << "unknown\n";
          } else {
            //debug
            for (auto hr : ruleManager.chcs) {
              if (!checkCHC(hr, candidates)) {
                outs() << "something is wrong(after SMT uk)!\n";
                assert(0);
              }
            }
            printCands(true, candidates, true);
          }
          return;
        }

        if (firstSMTCall || !useGAS) {
          firstSMTCall  = false;
          for (auto ce : smtSoln) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
          }
          continue;
        }
        printCands(false);
        // Use the model from maximalSMT to make a new block EXPR.
        continue;

        if(debug >= 3) outs() << "Entering weakenUsingSygus\n"; // Change this to use DL with model from check.
        Result_t chcres = usesygus ? weakenUsingSygus(weakenRels, fixedRels) : weakenUsingCHC(weakenRels, fixedRels);
        if(debug >= 3) outs() << "Left weakenUsingSygus\n";

        if (chcres == Result_t::UNKNOWN) {
          for (auto ce : smtSoln) {
            // if (find(fixedRels.begin(), fixedRels.end(), ce.first) == fixedRels.end()) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
            // }
          }
        }

        //debug
        // outs() << "SOLN:\n";
        // for (auto ce : candidates) {
        //   outs() << *(ce.first) << "->\n";
        //   for (auto c : ce.second) {
        //     outs() << *c <<"\n";
        //   }
        // }
        for (auto hr : ruleManager.chcs) {
          if (!checkCHC(hr, candidates)) {
            outs() << "something is wrong (after CHC)!\n";
            assert(0);
          }
        }
        if(debug >= 5) outs() << "End of loop\n";
        if(debug >= 2) printCands(false);

      }
    }

    void nonmaximalSolve(bool useGAS, bool usesygus)
    {
      Result_t res;
      if (usesygus) {
        ExprVector tmpfrels;
        ExprVector allrels = getAllRels();
        res = weakenUsingSygus(allrels, tmpfrels, true);
      } else if (useGAS) {
        res = guessAndSolve();
      } else {
        ExprVector weakenRels;
        ExprVector fixedRels;
        map<Expr, Expr> smtSoln;
        res = checkMaximalSMT(weakenRels, fixedRels, smtSoln);
        if (res == Result_t::SAT) {
          for (auto ce : smtSoln) {
            candidates[ce.first].clear();
            candidates[ce.first].insert(ce.second);
          }
          res = Result_t::UNSAT;
        } else {
          res = Result_t::UNKNOWN;
        }
      }

      switch(res) {
        case Result_t::UNSAT: printCands(); break;
        case Result_t::SAT: outs() << "sat!\n"; break;
        case Result_t::UNKNOWN: outs() << "unknown\n"; break;
      }
    }

    // naive solving, without invariant generation
    Result_t solveIncrementally(int bound, int unr, ExprVector& rels, vector<ExprVector>& args)
    {
      if (unr > bound)       // maximum bound reached
      {
        return Result_t::UNKNOWN;
      }
      else if (rels.empty()) // base case == init is reachable
      {
        return Result_t::SAT;
      }

      Result_t res = Result_t::UNSAT;

      // reserve copy;
      auto ssaStepsTmp = ssaSteps;
      int varCntTmp = varCnt;

      vector<vector<int>> applicableRules;
      for (int i = 0; i < rels.size(); i++)
      {
        vector<int> applicable;
        for (auto & r : ruleManager.incms[rels[i]])
        {
          Expr body = ruleManager.chcs[r].body; //ruleManager.getPostcondition(r);
          if (args.size() != 0)
            body = replaceAll(body, ruleManager.chcs[r].dstVars, args[i]);
          // identifying applicable rules
          if (u.isSat(body, conjoin(ssaSteps, m_efac)))
          {
            applicable.push_back(r);
          }
        }
        if (applicable.empty())
        {
          return Result_t::UNSAT;         // nothing is reachable; thus it is safe here
        }
        applicableRules.push_back(applicable);
      }

      vector<vector<int>> ruleCombinations;
      getCombinations(applicableRules, ruleCombinations);

      for (auto & c : ruleCombinations)
      {
        ssaSteps = ssaStepsTmp;
        varCnt = varCntTmp;
        ExprVector rels2;
        vector<ExprVector> args2;

        for (int i = 0; i < c.size(); i++)
        {
          // clone all srcVars and rename in the body
          auto &hr = ruleManager.chcs[c[i]];
          Expr body = hr.body;
          if (!hr.dstVars.empty()) body = replaceAll(body, hr.dstVars, args[i]);
          vector<ExprVector> tmp;
          for (int j = 0; j < hr.srcRelations.size(); j++)
          {
            rels2.push_back(hr.srcRelations[j]);
            ExprVector tmp1;
            for(auto &a: hr.srcVars[j])
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              tmp1.push_back(cloneVar(a, new_name));
            }
            args2.push_back(tmp1);
            body = replaceAll(body, hr.srcVars[j], tmp1);
            for (auto & a : hr.locVars)
            {
              Expr new_name = mkTerm<string> ("_fh_" + to_string(varCnt++), m_efac);
              body = replaceAll(body, a, cloneVar(a, new_name));
            }
          }

          ssaSteps.push_back(body);
        }

        if (u.isSat(conjoin(ssaSteps, m_efac))) // TODO: optimize with incremental SMT solving (i.e., using push / pop)
        {
          Result_t res_tmp = solveIncrementally(bound, unr + 1, rels2, args2);
          if (res_tmp == Result_t::SAT) return Result_t::SAT;           // bug is found for some combination
          else if (res_tmp == Result_t::UNKNOWN) res = Result_t::UNKNOWN;
        }
      }
      return res;
    }

    // naive solving, without invariant generation
    void solveIncrementally(int bound)
    {
      ExprVector query;
      query.push_back(ruleManager.failDecl);
      vector<ExprVector> empt;
      switch (solveIncrementally (bound, 0, query, empt))
      {
      case Result_t::SAT: outs () << "sat\n"; break;
      case Result_t::UNSAT: outs () << "unsat\n"; break;
      case Result_t::UNKNOWN: outs () << "unknown\n"; break;
      }
    }

    void setSygusPath(string sp)
    {
      SYGUS_BIN=sp;
    }
  };

  inline void solveNonlin(string smt, int inv, int stren, bool maximal, const vector<string> & relsOrder, bool useGAS, bool usesygus, bool useUC, bool newenc, bool fixCRels, string syguspath, bool dg, bool pgss, int debug = 0)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3);
    ruleManager.parse(smt);
    NonlinCHCsolver spec(ruleManager, stren, dg, pgss, debug);
    if(debug >= 3) outs() << "invDecl: " << ruleManager.invRel << "\n";
    if(debug >= 3)
      for(auto& e: ruleManager.invVars[ruleManager.invRel])
        outs() << "invVar: " << e << "\n";
    if(!ruleManager.hasQuery && ruleManager.chcs.size() == 2) {
      if(debug >= 2) ruleManager.print();
      spec.setUpQueryAndSpec();
      if(debug >= 3) outs() << "invDecl: " << ruleManager.invRel << "\nStart solving\n";
    }
    else {
      outs() << "Unsupported format\n";
      assert(0);
    }

    spec.boundSolve();
  };
}

#endif
