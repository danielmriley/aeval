#ifndef BOUNDSOLVER_HPP
#define BOUNDSOLVER_HPP

#include "Horn.hpp"
#include "DataLearner.hpp"
#include "DataLearner2.hpp"

using namespace std;
using namespace boost;

namespace ufo
{

  enum class Result_t {SAT=0, UNSAT, UNKNOWN};

  class BoundSolver
  {
  private:

    ExprFactory &m_efac;
    EZ3 z3;
    ZSolver<EZ3> smt;
    SMTUtils u;
    CHCs& ruleManager;
    int varCnt = 0;
    ExprVector ssaSteps;
    map<Expr, ExprSet> candidates;

    HornRuleExt* fc;
    HornRuleExt* tr;
    HornRuleExt* br;
    HornRuleExt* qr;

    ExprVector decls;

    HornRuleExt tr_orig;    // for phases

    Expr invDecl;
    ExprVector invVars;
    ExprVector invVarsPr;
    int invVarsSz;
    int phaseNum = 0;
    bool hasArrays = false;

    string specName = "pre";
    string varName = "_FH_";
    string ghostVar_pref = "_gh_";
    Expr specDecl;
    ExprVector specVars;
    ExprVector specVarsPr;
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
    ExprVector phases;
    vector<pair<Expr, Expr>> phasePairs;
    map<Expr,ExprVector> phasesMap;
    vector<ExprVector> paths;
    Expr mpzZero;
    Expr mpzOne;
    Expr eTrue;
    ExprMap stren, grds2gh, fgrds2gh; // associate a guard (phi(vars)) with a precond of gh (f(vars))
    ExprMap hyperMap; // map inductive INV's to their loop guards and "Bridge" INV's to their ITE guard.
    vector<ExprVector> hyperChains;
    vector<pair<Expr,Expr>> hyperLinks;
    ExprSet allLoopGuards;

    string SYGUS_BIN;
//    int globalIter = 0;
    int strenBound;
    int debug = 0;

    bool hornspec = false;
    bool dg = false;
    bool data2 = false;
    bool doPhases = false;

  public:
    BoundSolver (CHCs& r, int _b, bool _dg, bool d2, bool _dp, int dbg = 0)
      : m_efac(r.m_efac), ruleManager(r), u(m_efac), strenBound(_b), SYGUS_BIN(""),
        z3(m_efac), smt(z3), dg(_dg), data2(d2), doPhases(_dp), debug(dbg)
    {
      fc = nullptr;
      tr = nullptr;
      br = nullptr;
      qr = nullptr;

      specDecl = mkTerm<string>(specName, m_efac);

      for (auto& dcl: ruleManager.decls) decls.push_back(dcl->left());

      mpzZero = mkMPZ(0, m_efac);
      mpzOne = mkMPZ(1, m_efac);
      eTrue = mk<TRUE>(m_efac);
      setUpCounters();
    } // end constructor

    void setUpCounters()
    {
      if (debug >= 3) outs() << "setUpCounters\n";
      for (int i = 0; i < 2; i++)
      {
        Expr new_name = mkTerm<string> (ghostVar_pref + to_string(i), m_efac);
        Expr var = bind::intConst(new_name);
        ghostVars.push_back(var);

        new_name = mkTerm<string> (ghostVar_pref + to_string(i) + "'", m_efac);
        var = bind::intConst(new_name);
        ghostVarsPr.push_back(var);
      }

      ghost0Minus1 = mk<MINUS>(ghostVars[0], mpzOne);
      ghost1Minus1 = mk<MINUS>(ghostVars[1], mpzOne);
      decGhost0 = mk<EQ>(ghostVarsPr[0], ghost0Minus1);
      decGhost1 = mk<EQ>(ghostVarsPr[1], ghost1Minus1);
      ghostAss = mk<LT>(ghostVars[0], mpzZero);
      ghostGuard = mk<NEQ>(ghostVars[0], mpzZero);
      ghostGuardPr = mk<NEQ>(ghostVarsPr[0], mpzZero);
    }

    void replaceRule(HornRuleExt* src, HornRuleExt* dst)
    {
      dst->srcRelation = src->srcRelation;
      dst->srcVars = src->srcVars;
      dst->dstRelation = src->dstRelation;
      dst->dstVars = src->dstVars;
      dst->isFact = src->isFact;
      dst->isInductive = src->isInductive;
      dst->isQuery = src->isQuery;
      dst->body = src->body;
    }

    void setUpFc(HornRuleExt* fc) {
      HornRuleExt* fc_new = new HornRuleExt();
      invVars = ruleManager.invVars[fc->dstRelation];
      invVarsPr = ruleManager.invVarsPrime[fc->dstRelation];

      fc_new->srcRelation = specDecl;
      fc_new->srcVars.clear();
      fc_new->dstRelation = fc->dstRelation;
      fc_new->dstVars = fc->dstVars;
      fc_new->dstVars.push_back(ghostVarsPr[0]);
      fc_new->isFact = false;

      specVars.clear();
      specVarsPr.clear();
      for (int i = 0; i < invVars.size(); i++) {
        // specVars.push_back(bind::intConst(mkTerm<string>(varName + to_string(i), m_efac)));
        // specVarsPr.push_back(bind::intConst(mkTerm<string>(varName + to_string(i) + "'", m_efac)));

        specVars.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()), m_efac)));
        specVarsPr.push_back(bind::intConst(mkTerm<string>(varName + to_string(i + invVars.size()) + "'", m_efac)));
      }
      fc_new->srcVars = specVars;

      ExprSet fc_body;
      for (int i = 0; i < specVars.size(); i++) {
        fc_body.insert(mk<EQ>(specVars[i], invVarsPr[i]));
      }

      fc_body.insert(replaceAll(fc->body, invVarsPr, specVars));
      fc_body.insert(mk<EQ>(ghostVars[1], ghostVarsPr[0]));

      fc_new->body = conjoin(fc_body, m_efac);
      if (debug >= 3) outs() << "fc_new body: " << fc_new->body << "\n";
      fc_new->srcVars.push_back(ghostVars[1]);
      // fc_new->srcVars.push_back(ghostVars[0]);
      specVars = fc_new->srcVars;
      ruleManager.invVars[specDecl].clear();
      ruleManager.addDeclAndVars(specDecl,specVars);

      replaceRule(fc_new, fc);

      fcBodyInvVars = fc_new->body;
      ExprSet temp;
      getConj(fcBodyInvVars,temp);
      bool replaced;
      for (auto e = temp.begin(); e != temp.end(); ) {
        replaced = false;
        for (auto& i: fc_new->dstVars) {
          if (contains(*e, i)) {
            e = temp.erase(e);
            replaced = true;
          }

        }
        if (!replaced) e++;
      }
      fcBodyInvVars = conjoin(temp, m_efac);
      if (debug >= 3) outs() << "fcBodyInvVars : " << fcBodyInvVars << "\n";
    }

    void setUpTr(HornRuleExt* tr) {
      HornRuleExt* tr_new = new HornRuleExt();
      if(tr->isInductive) {
        loopGuard = ruleManager.getPrecondition(tr);
        allLoopGuards.insert(mkNeg(loopGuard));
        loopGuardPr = replaceAll(loopGuard, invVars, invVarsPr);

        if(debug >= 3) {
          outs() << "LOOPGUARD: " << loopGuard << "\n";
          outs() << "LOOPGUARDPR: " << loopGuardPr << "\n";
        }
      }

      invDecl = tr->srcRelation;
      tr_new->srcRelation = tr->srcRelation;
      ruleManager.invVars[invDecl].clear();
      tr_new->srcVars = tr->srcVars;
      tr_new->srcVars.push_back(ghostVars[0]);

      if(emptyIntersect(invVars, ghostVars)) {
        invVars.push_back(ghostVars[0]);
      }
      if(emptyIntersect(invVarsPr, ghostVarsPr)) {
        invVarsPr.push_back(ghostVarsPr[0]);
      }

      tr_new->dstRelation = tr->dstRelation;
      tr_new->dstVars = tr->dstVars;
      tr_new->dstVars.push_back(ghostVarsPr[0]);
      if(tr->isInductive) tr_new->isInductive = true;

      ruleManager.addDeclAndVars(invDecl,invVars);

      ExprSet tmp;
      getConj(tr->body, tmp);
      tmp.insert(decGhost0);
      tr_new->body = conjoin(tmp, m_efac);
      replaceRule(tr_new, tr);
      if(tr->isInductive) tr_orig = *tr;
      fcBodyInvVars = replaceAll(fcBodyInvVars, specVars, invVars);
      if (debug >= 3) outs() << "fcBodyInvVars : " << fcBodyInvVars << "\n";
    }

    void setUpBr(HornRuleExt* tr) {
      HornRuleExt* tr_new = new HornRuleExt();
      invDecl = tr->srcRelation;
      tr_new->srcRelation = tr->srcRelation;
      ruleManager.invVars[invDecl].clear();
      tr_new->srcVars = tr->srcVars;
      tr_new->srcVars.push_back(ghostVars[0]);

      tr_new->dstRelation = tr->dstRelation;
      tr_new->dstVars = tr->dstVars;
      tr_new->dstVars.push_back(ghostVarsPr[0]);

      ruleManager.addDeclAndVars(invDecl,invVars);

      ExprSet tmp;
      getConj(tr->body, tmp);
      tmp.insert(mk<EQ>(ghostVars[0],ghostVarsPr[0]));
      tr_new->body = conjoin(tmp, m_efac);
      replaceRule(tr_new, tr);
    }

    void setUpQr(HornRuleExt* tr, Expr qrGuard)
    {
      HornRuleExt* qr = new HornRuleExt();
      qr->srcRelation = tr->srcRelation; // Need to pick the rel from the last loop.
      qr->srcVars = tr->srcVars;
      qr->dstRelation = mkTerm<string> ("err", m_efac);
      qr->isQuery = true;
      ruleManager.hasQuery = true;

      Expr lastRel = ruleManager.chcs[lastCycle].srcRelation;
      Expr lastBound, lastGuards;
      if(isOpX<IMPL>(qrGuard)) {
        // This means there are extra conditions that need to be put on the QR
        // along with the bound.
        lastBound = qrGuard->right();
        lastGuards = qrGuard->left();
      }
      else {
        // This should probably only hit at the first go around.
        lastBound = qrGuard;
      }
      // Expr lg = conjoin(allLoopGuards, m_efac);
      outs() << "SETUPQR " << loopGuard << " GG " << ghostGuard << "\n";
      qr->body = mk<AND>(mkNeg(loopGuard), mkNeg(lastBound));

      ruleManager.addFailDecl(qr->dstRelation);
      ruleManager.addRule(qr);
      outs() << "QR BODY: \n" << qr->body << "\n";
    }

    bool setUpQueryAndSpec() {
      ruleManager.decls.clear();
      for(auto& hr: ruleManager.chcs) {
        if(hr.isFact) {
          if (debug >= 4) outs() << "FACT\n";
          setUpFc(&hr);
        }
        else if(hr.isInductive) {
          if (debug >= 4) outs() << "INDUCTIVE\n";
          setUpTr(&hr);
        }
        else if(hr.isQuery) { if (debug >= 4) { outs() << "QUERY\n"; } }
        else {
          if (debug >= 4) outs() << "BRIDGE\n";
          setUpTr(&hr);
        }
      }
      if (debug >= 3) {
        outs() << "===================\n";
        ruleManager.print(true);
      }

      return true;
    }

    void removeQuery() {
      for(auto hr = ruleManager.chcs.begin(); hr != ruleManager.chcs.end(); ) {
        if(hr->isQuery) {
          if (debug >= 4) outs() << "erasing query\n";
          hr = ruleManager.chcs.erase(hr);
        }
        else { hr++; }
      }
    }

    void genCands(ExprSet & tmp, Expr pc)
    {
      Expr v = mkConst(mkTerm<string>("tmp_", m_efac), mk<INT_TY>(m_efac));
      ExprSet newCands;
      for (auto it = tmp.begin(); it != tmp.end(); ++it)
      {
        auto a = *it;
        if (contains(a, pc)) continue;
        if (!isOp<ComparissonOp>(a)) continue;
        a = normalize(a);

        for (auto it2 = std::next(it); it2 != tmp.end(); ++it2)
        {
          auto b = *it2;
          if (a == b) continue;
          if (!isOp<ComparissonOp>(b)) continue;
          b = normalize(b);

          Expr n = mk<AND>(reBuildCmp(a, mk<MINUS>(a->left(), a->right()), v),
                           reBuildCmp(b, mk<MINUS>(b->left(), b->right()), v));
          newCands.insert(eliminateQuantifier(n, v));
        }
      }
      tmp = newCands;
    }

    void parseForGuards() {
      if (debug >= 3) outs() << "Begin parsing for guards\n";
      // get a DNF form if there are disj in the result from G&S.
      ExprVector projections, prjcts, vars2keep;
      Expr pc = ghostVars[0];

      u.flatten(conjoin(candidates[specDecl], m_efac), prjcts, false, vars2keep, [](Expr a, ExprVector& b){return a;});

      for (auto& p : prjcts) {
        projections.push_back(replaceAll(p, fc->srcVars, invVars));
      }
      if (debug >= 3) {
        outs() << "\n   Projections\n=================\n";
        pprint(projections, 3);
        outs() << "=================\n";
      }
      ExprSet t,p,g;
      for (auto e = projections.begin(); e != projections.end() ; e++) {
        t.clear(); p.clear(); g.clear();
        getConj(*e, t);

        ExprSet temp;
        for (auto& a: t) {
          temp.insert(normalize(a));
        }
        t.clear();
        t.swap(temp);
        int c = 0;
        ExprSet toBeRenamed;
        for (auto& ee: t) {
          if (contains(ee, ghostVars[0]) || contains(ee, ghostVars[1])) {
            c++;
            Expr r = replaceAll(ee, fc->srcVars, invVars);

            r = normalize(r, pc);
            if (containsOp<EQ>(r) && r->left() == pc) g.insert(r);
            else toBeRenamed.insert(r);
          }
          else {
            Expr r = replaceAll(ee, fc->srcVars,invVars);
            p.insert(normalize(r));
          }
        }

        Expr join = *g.begin();
        auto i = g.begin(), end = g.end();
        i++;
        for (auto & a : toBeRenamed)
          p.insert(replaceAll(a, pc, join->right()));
        for (; i!=end; i++) {
          join = mk<EQ>(join->right(), (*i)->right());
          join = normalize(join);
          p.insert(join);
        }
        for (auto& d: g) {
          if (isOpX<MPZ>(d->right())) {
            join = d;
            break;
          }
        }

        auto grd = conjoin(p, m_efac);
        if (grds2gh[grd] != NULL && join->right() != grds2gh[grd])
        {
          if(debug >= 2) {
            outs () << "grds2gh for " << grd << ":\n   " << grds2gh[grd] << "\n";
            outs () << "   want to assign: " << join->right() << "\n";
          }
          assert(0 && "ERROR: guards already assigned\n");
        }
        {
          if(debug >= 2) outs () << "  ASSIGNING grds2gh for " << grd << ":\n   " << join->right() << "\n";
          grds2gh[grd] = join->right();  // GF: DS
        }
      }
      if (debug >= 3) { outs() << "End parsing for guards\n"; }
    }

    void bubbleSort(ExprVector& v) {
      for (int i = 0; i < v.size(); i++) {
        for (int j = 0; j < v.size()-1; j++) {
          if (v[j]->left()->arity() > v[j+1]->left()->arity()) {
            Expr e = v[j];
            v[j] = v[j+1];
            v[j+1] = e;
          }
        }
      }
    }

    void sortBounds(ExprVector& bounds) {
      ExprVector holdMPZ, holdOther;

      for (int i = 0; i < bounds.size(); i++) {
        Expr e = normalize(bounds[i]);
        if (isOpX<MPZ>(e->right()) && e->right() != mpzZero) {
          holdMPZ.push_back(e);
        }
        else {
          holdOther.push_back(e);
        }
      }
      bubbleSort(holdOther);
      bubbleSort(holdMPZ);
      bounds.clear();
      for (auto& v : holdOther) bounds.push_back(normalize(v, ghostVars[0]));
      for (auto& v : holdMPZ) bounds.push_back(normalize(v, ghostVars[0]));
    }

    void filterNonGhExp(ExprSet& candSet)
    {
      for (auto i = candSet.begin(); i != candSet.end(); ) {
        if (!contains(*i, ghostVars[0])) {
          if (dg) dataGrds.insert(*i);
          i = candSet.erase(i);
        }
        else i++;
      }
    }

    boost::tribool dataForBoundPhase(Expr src, Expr dst,
                                     map<Expr, ExprSet>& candMap, Expr block) {
      DataLearner2 dl2(ruleManager, z3, debug);
      Expr invs = mk<TRUE>(m_efac);
      boost::tribool res = true;
      Expr pc = ghostVars[0];
      assert (grds2gh[dst] != NULL);

      Expr brPrecondition = eTrue;
      if(br != nullptr) {
        brPrecondition = ruleManager.getPrecondition(br);
      }
      // outs() << "BR->PRECOND: " << brPrecondition << std::endl;
      // block = mk<AND>(block,brPrecondition);
      block = simplifyBool(block);
      outs() << "\nBLOCK: " << block << "\n" << std::endl;

      // qr->body = mk<AND>(mk<NEG>(src),
      //                    mk<NEG>(mk<AND>(dst, stren[dst],
      //                            mk<EQ>(pc, grds2gh[dst])))); // hack for now
      // tr->body = u.removeITE(mk<AND>(src, tr_orig.body));

      if (debug > 2) {
        outs () << "  using " << grds2gh[dst] << "\n    as bound for " << dst << "\n";
      }

      Expr dst1 = mk<AND>(mk<NEG>(src), mk<AND>(dst, stren[dst]), mk<EQ>(pc, grds2gh[dst]));

      Expr src1 = u.simplifiedAnd(block, src);
      if (isOpX<TRUE>(block)) {
        src1 = replaceAll(src1, invVars, fc->srcVars);
      }

      res = dl2.connectPhase(src1, dst1, invDecl, block, invs, loopGuard);

      if (res == true) {
        dl2.getDataCands(candMap[invDecl], invDecl);  // GF
      }
      else
      {
        if(debug >= 2) {
          outs () << "check sanity:\n";
          outs () << src1 << "   =>  ";
          outs () << dst << "\n";
        }
        ExprSet cnjs, cnjsUpd;
        getConj(src1, cnjs);
        // some small mutations
        for (auto s : cnjs)
        {
          s = simplifyArithm(replaceAll(
              keepQuantifiers(mk<AND>(s, tr->body), tr->dstVars),
              tr->dstVars, tr->srcVars));

          getConj(s, cnjsUpd);
        }
        cnjs.insert(cnjsUpd.begin(), cnjsUpd.end());

        for (auto it = cnjs.begin(); it !=cnjs.end();)
          if (u.implies(mk<AND>(*it, tr->body),
                   replaceAll(*it, tr->srcVars, tr->dstVars)))
            ++it; else it = cnjs.erase(it);

        // outs () << "    INV:    " << conjoin(cnjs, m_efac) << "\n";
        if (u.implies(mk<AND>(mk<NEG>(src),
                conjoin(cnjs, m_efac)), mk<NEG>(mk<AND>(dst, stren[dst]))))
          {} //outs () << "  SANE \n";
        else
        {
          outs () << "  INSANE \n";
          // if you see this, then we may have a soundness issue.
          // need to manually check the reported solution.
          // (and also need to fix something in the code)
          outs() << u.getModel() << "\n";
        }
      // check actual reachability:
      // if (u.implies());
      }
      return res;
    }

    boost::tribool exploreBounds(Expr src, Expr dst,
                                 map<Expr, ExprSet>& ghCandMap, Expr block)
    {
      boost::tribool res;

      if (isOpX<FALSE>(block)) return false;
      res = dataForBoundPhase(src, dst, ghCandMap, block);
      if (res == indeterminate) return indeterminate;
      else if (res == false) return false;
      filterNonGhExp(ghCandMap[invDecl]);
      if (ghCandMap[invDecl].empty()) return indeterminate;

      ExprSet temp;
      for (auto i = ghCandMap[invDecl].begin(),
          end = ghCandMap[invDecl].end(); i != end; i++) {
        Expr e = *i;
        e = normalize(e,ghostVars[0]);
        temp.insert(e);
      }
      ghCandMap[invDecl].swap(temp);
      if (debug >= 2) {
        outs() << "  Filtered cands found: ";
        if (!ghCandMap[invDecl].empty())
          outs() << ghCandMap[invDecl].size() << "\n";
        else outs() << "  none.\n";
      }
      // break odd/even

      return res;
    }

    bool checkAllOver (bool checkQuery = false, bool weak = true,
        Expr src = NULL, Expr dst = NULL)
     {
       for (auto & hr : ruleManager.chcs)
       {
         if (hr.isQuery && !checkQuery) continue;
         if (!checkCHC(hr, candidates)) return false;
       }
      if (weak)
      {
        if (debug >= 2) outs () << "try weakening\n";

        // ExprSet cannot, cannotSpec;
        // while (true)
        // {
        //   auto it = candidates [specDecl].begin();
        //   for (; it != candidates [specDecl].end();)
        //   {
        //     Expr cand = *it;
        //     if (find(cannotSpec.begin(), cannotSpec.end(), cand) != cannotSpec.end() ||
        //         lexical_cast<string>(cand).find("gh") != std::string::npos)  // hack for now
        //     {
        //       ++it;
        //       continue;
        //     }
        //
        //     if (u.implies(src, cand))
        //     {
        //       ++it;
        //       continue;
        //     }
        //
        //     if (debug >= 2) outs () << "can remove: " << cand << "?\n";
        //                 outs () << candidates [specDecl].size() << ". " << candidates [invDecl].size() << "\n";
        //     it = candidates [specDecl].erase(it);
        //     auto r = replaceAll(*it, fc->srcVars, tr->srcVars);
        //     candidates [invDecl].erase(r);
        //
        //     outs () << candidates [specDecl].size() << ". " << candidates [invDecl].size() << "\n";
        //     auto res = checkAllOver(checkQuery, false, src, dst);
        //     if (debug >= 5)   outs () << "checkAllOver (nest):  " << res << "\n";
        //     if (!res)
        //     {
        //       outs () << "inseer back\n";
        //       cannot.insert(r);
        //       cannotSpec.insert(cand);
        //       break;
        //     }
        //
        //   }
        //
        //   auto res = (it == candidates [specDecl].end());
        //   candidates [specDecl].insert(cannotSpec.begin(), cannotSpec.end());
        //   candidates [invDecl].insert(cannot.begin(), cannot.end());
        //   if (res) break;
        //
        // }


        for (auto & a : candidates)
        {
          ExprSet cannot;
          while (true)
          {
            auto it = a.second.begin();
            for (; it != a.second.end();)
            {
              Expr cand = *it;
              if (find(cannot.begin(), cannot.end(), cand) != cannot.end() ||
                  lexical_cast<string>(cand).find("gh") != std::string::npos)  // hack for now
              {
                ++it;
                continue;
              }

              if (u.implies(src, cand))
              {
                ++it;
                continue;
              }

              if (debug >= 3) outs () << "can remove: " << cand << " for " << a.first << "?\n";
              it = a.second.erase(it);
              auto res = checkAllOver(checkQuery, false, src, dst);
              if (debug >= 5)   outs () << "checkAllOver (nest):  " << res << "\n";
              if (!res)
              {
                cannot.insert(cand);
                break;
              }
            }

            auto res = (it == a.second.end());
            a.second.insert(cannot.begin(), cannot.end());
            if (res) break;
          }
        }
      }
       return true;
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

     bool checkCHC (HornRuleExt& hr, map<Expr, ExprSet>& annotations)
     {
       ExprSet checkList;
       checkList.insert(hr.body);
       Expr rel;
       if (debug >= 6) {
         if (hr.isQuery) outs() << "Query\n";
         else if (hr.isInductive) outs() << "Inductive\n";
         else if(hr.isFact) outs() << "Pre\n";
         else outs() << "Bridge\n";
       }
       {
         Expr rel = hr.srcRelation;
         ExprSet lms = annotations[rel];
         Expr overBody = replaceAll(conjoin(lms, m_efac), ruleManager.invVars[rel], hr.srcVars);
         if (debug >= 6) outs() << "overbody: " << overBody << "\n";
         getConj(overBody, checkList);
       }
       if (!hr.isQuery)
       {
         rel = hr.dstRelation;
         ExprSet negged;
         ExprSet lms = annotations[rel];
         for (auto a : lms) negged.insert(mkNeg(replaceAll(a, ruleManager.invVars[rel], hr.dstVars)));
         Expr neg = disjoin(negged, m_efac);
         if (debug >= 6) outs() << "neg: " << neg << "\n";
         checkList.insert(neg);
       }
       if (debug >= 6) { outs() << "checkList:\n"; pprint(checkList, 2); }
       auto res = bool(!u.isSat(checkList));
       return res;
     }

    bool anyProgress(vector<HornRuleExt*>& worklist)
    {
      for (auto & a : candidates)
        for (auto & hr : worklist) // if problems look here.
          if (hr->srcRelation == a.first || hr->dstRelation == a.first)
            if (!a.second.empty()) return true;
      return false;
    }

    void filterUnsat() // Maybe the rndv3 version can be adapted?
    {
     vector<HornRuleExt*> worklist;
     for (auto & a : candidates)
       if (!u.isSat(a.second)) {
         for (auto & hr : ruleManager.chcs)
           if (hr.dstRelation == a.first && hr.isFact) {
             worklist.push_back(&hr);
           }
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
    }

    // adapted from BndExpl:: getAllTraces
    bool getAllPaths (Expr src, Expr dst, int len, ExprVector trace, vector<ExprVector>& traces, std::vector<pair<Expr, Expr>> phasePairs)
    {
      // outs() << "\nCurrent trace\n";
      // for(auto& t : trace) outs() << t << "->";
      // outs() << "\n";
      if (len == 1)
      {
        for (auto a : phasePairs)
        {
          if (a.first == src && a.second == dst)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1) {
                  outs() << "\nCurrent trace\n";
                  for(auto& t : trace) outs() << t << "->";
                  outs() << "\n";
                  // outs() << "src: " << src << "  :  " << "dst: " << dst << "\n";
                  outs() << "cyclic paths not supported\n";
                }
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(dst);
            traces.push_back(newtrace);
          }
        }
      }
      else
      {
        for (auto a : phasePairs)
        {
          if (a.first == src)
          {
            for (auto & b : trace)
            {
              if (a.second == b)
              {
                if (debug >= 1) {
                  outs() << "   :  src: " << src << "  :  " << "dst: " << dst << "\n";
                  outs() << "\nCurrent trace\n";
                  for(auto& t : trace) outs() << t << "->";
                  outs() << "\n";
                  // outs() << "a.first: " << a.first << "\n";
                  // outs() << "a.second: " << a.second << "\n";
                  // outs() << "b: " << b << "   :  src: " << src << "  :  " << "dst: " << dst << "\n";
                  outs () << "cyclic paths not supported\n";

                }
                return false;
              }
            }
            ExprVector newtrace = trace;
            newtrace.push_back(a.second);
            bool  res = getAllPaths(a.second, dst, len-1, newtrace, traces, phasePairs);
            if (!res) return false;
          }
        }
      }

      return true;
    }

    void getCombs(ExprVector& elems, int pos, vector<ExprVector>& res)
    {
      if (pos == 0)
      {
        res = {{elems[0]}, {mkNeg(elems[0])}};
      }
      else
      {
        vector<ExprVector> res2;
        for (auto comb : res)
        {
          comb.push_back(elems[pos]);
          res2.push_back(comb);
          comb.back() = mkNeg(elems[pos]);
          res2.push_back(comb);
        }
        res = res2;
      }
      if (pos + 1 < elems.size())
        getCombs(elems, pos+1, res);
    }

    map<Expr,vector<pair<Expr, Expr>>> linkPairs;

    void pairLinks(std::set<int> cycles) {
      ExprVector init;
      ExprSet prevExit;

      for(auto& cycle: cycles) {
        if(cycle == 1) {
          // What if the first loop depends on ITE branch?
          // Then init needs to be assigned differentlt.
          // Basically, this is a bad way to do it.
          // Will change when I have a better idea..... DR

          init.push_back(fcBodyInvVars);
        }
        else {
          init.push_back(mk<TRUE>(m_efac));
        }

        HornRuleExt* hr = &ruleManager.chcs[cycle];
        Expr rel = hr->srcRelation;
        vector<pair<Expr, Expr>> phasePairs;

        setPointers(cycle, mkNeg(ghostGuard));

        for (auto& p : phasesMap[rel]) {
          for(auto& i: init) {
            if (i != p && u.isSat(i, p)) {
              phasePairs.push_back(std::make_pair(i,p));
            }
          }
        }

        Expr prevExitsDisj;
        if(cycle > 1) {
          prevExitsDisj = disjoin(prevExit, m_efac);
        }
        else {
          prevExitsDisj = mk<TRUE>(m_efac);
        }

        for (int i = 0; i < phasesMap[rel].size(); i++) {
          for (int j = 0; j < phasesMap[rel].size(); j++) {
            if (i == j) continue;
            if (u.isSat(tr->body, prevExitsDisj, phasesMap[rel][i], replaceAll(phasesMap[rel][j],invVars,invVarsPr))) {
              phasePairs.push_back(std::make_pair(phasesMap[rel][i], phasesMap[rel][j]));
            }
          }
        }
        for (auto& p : phasesMap[rel]) {
          if (!u.isSat(p, tr->body)) {
            phasePairs.push_back(std::make_pair(p,mk<FALSE>(m_efac)));
            prevExit.insert(p);
          }
        }

        init.clear();
        if(debug >= 4) for(auto& v: prevExit) outs() << "PE: " << v << "\n";
        linkPairs[hr->srcRelation].insert(linkPairs[hr->srcRelation].end(), phasePairs.begin(), phasePairs.end());
      }

      if(debug >= 2) {
        outs() << "\n=== Print Link Pairs ===\n";
        for(auto& lp: linkPairs) {
          outs() << "linkPairs for " << lp.first << "\n";
          for(auto& pp : lp.second) {
            outs() << "  " << pp.first << " -> " << pp.second << "\n";
          }
        }
      }
    }

    map<Expr, vector<ExprVector>> pathsMap;

    void printPathsMap() {
      for(auto& pm : pathsMap) {
        outs() << pm.first << "\n";
        for(auto& p: pm.second) {
          outs() << "  ";
          for(auto& v: p) {
            outs() << v << " -> ";
          }
          outs() << "\n";
        }
        outs() << "\n";
      }
    }

    bool makePredicateChains() {
      int cycle = 1;
      for(auto& lp: linkPairs) {
        ExprSet init;
        if(debug >= 4) outs() << "\n" << lp.first << "\n";
        for (auto & p : lp.second) {
          if (p.first == fcBodyInvVars || p.first == mk<TRUE>(m_efac)) {
            init.insert(p.first);
          }
        }
        if(debug >= 4) for(auto& i: init) outs()<< "  " << i << "\n";

        // sanity check:
        if (cycle == 1 && u.implies(fcBodyInvVars, disjoin(init, m_efac)))
        {
          if (debug >= 3) outs () << "Init cases general enough\n";
        }
        else if (cycle > 1 && u.implies(mk<TRUE>(m_efac), disjoin(init, m_efac)))
        {
          if (debug >= 3) outs () << "Init cases general enough\n";
        }
        else {
          assert(0 && "something is wrong in the phase construction");
        }

        for (auto & in : init)
        {
          int len = pathsMap[lp.first].size();
          for (int i = 1; i <= lp.second.size() ; i++) {
            bool res = getAllPaths (in, mk<FALSE>(m_efac), i, {in}, pathsMap[lp.first], lp.second);
            if (!res) return false;
          }
          assert (pathsMap[lp.first].size() > len && "No paths found\n");
        }
        cycle += 2;
      }

      if(debug >= 3) printPathsMap();

      return true;
    }

    void shrinkPrjcts(ExprVector & prjcts)
    {
      int sz = prjcts.size();
      if (debug) outs () << "shrinkPrjcts sz = " << sz << "\n";
      if (sz == 1) return;
      for (auto it = prjcts.begin(); it != prjcts.end();)
      {
        Expr cand = *it;
        if (u.implies(cand, loopGuard))
        {
          ++it;
          continue;
        }
        // outs () << "see if can remove " << cand << "\nvars: ";
        ExprSet vars;
        // for (auto it2 = prjcts.begin(); it2 != prjcts.end(); ++it2)
        //   if (it != it2)
        //     filter (*it2, bind::IsConst (), inserter (vars, vars.begin()));

        filter (loopGuard, bind::IsConst (), inserter (vars, vars.begin()));

        ExprVector copyNames, copyNamesPr, eq1, eq2;
        for (int i = 0; i < tr->srcVars.size(); i++)
        {
          Expr new_name = mkTerm<string> ("__eq_var_" + to_string(i), m_efac);
          Expr var = cloneVar(tr->srcVars[i], new_name);
          copyNames.push_back(var);

          new_name = mkTerm<string> ("__eq_var_" + to_string(i) + "_", m_efac);
          Expr var1 = cloneVar(tr->srcVars[i], new_name);
          copyNamesPr.push_back(var1);

          if (find(vars.begin(), vars.end(), tr->srcVars[i]) != vars.end())
          {
            eq1.push_back(mk<EQ>(tr->srcVars[i], var));
            eq2.push_back(mk<EQ>(tr->dstVars[i], var1));
          }
        }

        bool eq = true;
        for (auto c : {cand, mk<NEG>(cand)})
        {
          Expr newBody = replaceAll(replaceAll(mk<AND>(tr->body, c), tr->srcVars, copyNames),
                                              tr->dstVars, copyNamesPr);
          eq &= (true == (bool)u.isSat(newBody));
          ExprVector eqcheck = {
            tr->body,
            newBody,
            conjoin(eq1, m_efac),
            mk<NEG>(conjoin(eq2, m_efac))
          };
          eq &= (false == (bool)u.isSat(eqcheck));
        }

        if (eq)
        {
          outs () << "   >> erasing prj: " << *it << "\n";
          it = prjcts.erase(it);
          break;
        }
        else ++it;
      }
      if (prjcts.size() < sz) shrinkPrjcts(prjcts);
    }

    map<Expr, ExprSet> prjctsGlob;
    void collectPhaseAtomics(std::set<int> cycles) {
      for(auto& cycle: cycles) {
        setPointers(cycle, mkNeg(ghostGuard)); // sets Vars containers based on cycle.
        testPointers();

        HornRuleExt* hr = &ruleManager.chcs[cycle];
        Expr rel = hr->srcRelation;
        ExprVector& srcVars = invVars;
        ExprVector& dstVars = invVarsPr;
        assert(srcVars.size() == dstVars.size());
        ExprSet dstVarsSet;
        for (auto& d: dstVars) dstVarsSet.insert(d);

        if (debug >= 4) outs() << "BODY: " << hr->body << "\n";

        ExprVector vars2keep, prjcts, prjcts1;
        ExprSet prjctsTmp;
        bool hasArray = false;
        for (int i = 0; i < srcVars.size(); i++) {
          if (containsOp<ARRAY_TY>(srcVars[i]))
          {
            hasArray = true;
            vars2keep.push_back(dstVars[i]);
          }
          else
          {
            vars2keep.push_back(srcVars[i]);
          }
        }

        u.flatten(hr->body, prjcts1, false, vars2keep, keepQuantifiersRepl);

        for (auto p : prjcts1)
        {
          if (hasArray)
          {
            p = ufo::eliminateQuantifiers(p, dstVarsSet);
            p = weakenForVars(p, dstVars);
          }
          else
          {
            p = weakenForVars(p, dstVars);
            p = simplifyArithm(normalize(p));
          }
          getConj(p, prjctsTmp);
          if (debug >= 3) outs() << "Generated MBP: " << p << "\n";
        }
        testPointers();

        prjcts.insert(prjcts.end(), prjctsTmp.begin(), prjctsTmp.end());
        u.removeRedundantConjunctsVec(prjcts);

        for (auto it = prjcts.begin(); it != prjcts.end();)
        {
          bool toRem = false;
          for (auto it2 = prjcts.begin(); it2 != it; ++it2)
          {
            if (u.isEquiv(*it, mkNeg(*it2)))
            {
              toRem = true;
              break;
            }
          }
          if (toRem)
          it = prjcts.erase(it);
          else
          ++it;
        }

        if (debug >= 3)
        {
          outs() << "Split MBP: \n";
          pprint(prjcts, 3);
        }

        shrinkPrjcts(prjcts);
        for(auto& p: prjcts) prjctsGlob[rel].insert(p);
        // prjctsGlob.insert(prjctsGlob.end(), prjcts.begin(), prjcts.end());
      }

      if(debug >= 2) {
        outs() << "Global projections\n";
        for(auto& pgg: prjctsGlob) {
          outs() << pgg.first << "\n";
          for(auto& pg: pgg.second)
            outs() << "  : " << pg << "\n";
        }
      }

      setPointers(1, mkNeg(ghostGuard)); // Reset the pointers to the first loop.
    }

    void makeCombs() {
      for(auto& pgg : prjctsGlob) {
        Expr rel = pgg.first;
        ExprVector prjcts;
        vector<ExprVector> res;

        for(auto& pg: pgg.second)
          prjcts.push_back(pg);

        getCombs(prjcts, 0, res);
        for (auto & r : res)
        {
          phasesMap[rel].push_back(conjoin(r, m_efac));
          if (debug >= 3) {
            outs () << "  comb: ";
            pprint(r);
            outs () << "\n";
          }
        }
        testPointers();
      }
    }

    void setPointers(int cycle, Expr qrGuard) {
      HornRuleExt hr = ruleManager.chcs[cycle];
      loopGuard = ruleManager.getPrecondition(&hr);
      Expr rel = hr.srcRelation;
      removeQuery();
      setUpQr(&hr, qrGuard);
      if (debug >= 4) outs() << "src relation: " << rel << "\n";
      if(debug >= 5) ruleManager.print(true);

      tr = &ruleManager.chcs[cycle];
      for(auto& r: ruleManager.chcs) {
        if(r.isQuery) {
          qr = &r;
        }
        else {
          if(!r.isInductive && r.srcRelation == specDecl) {
            fc = &r;
          }
          if(!r.isInductive && !r.isFact && !r.isQuery && r.srcRelation == tr->srcRelation) {
            br = &r;
          }
          if(!r.isInductive && !r.isFact && !r.isQuery && r.dstRelation == tr->srcRelation) {
            // fc = &r;
          }
        }
      }
      testPointers();
    }

    void testPointers() {
      if(debug>= 3) outs() << "\n\n";
      if(fc == nullptr || tr == nullptr || qr == nullptr/* || br == nullptr*/) {
        outs() << "ERROR: NULLPTR\n";
        exit(0);
      }
      else if(debug >= 3) {
        outs() << "Pointers are safe\n";
      }
      if(debug >= 4) {
        outs() << "fc: " << fc->body << "\n";
        outs() << "tr: " << tr->body << "\n";
        if(br != nullptr) outs() << "br: " << br->body << "\n";
        outs() << "qr: " << qr->body << "\n";
      }
      if(debug>= 3) outs() << "\n\n";
    }

    bool multiHoudiniExtr(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      //GF: to check -- if this weaken is needed
      // ExprSet e1, e2;
      // for (auto & c : candidates[specDecl])
      // {
      //   if (isOpX<LT>(c)) e1.insert(mk<LEQ>(c->left(), c->right()));
      //   if (isOpX<GT>(c)) e1.insert(mk<GEQ>(c->left(), c->right()));
      // }
      //
      // candidates[specDecl].insert(e1.begin(), e1.end());
      //
      // for (auto & c : candidates[invDecl])
      // {
      //   if (isOpX<LT>(c)) e2.insert(mk<LEQ>(c->left(), c->right()));
      //   if (isOpX<GT>(c)) e2.insert(mk<GEQ>(c->left(), c->right()));
      // }
      //
      // candidates[invDecl].insert(e2.begin(), e2.end());

      // printCandsEx();
      return multiHoudini(worklist, recur);
    }

    // adapted from RndLearnerV3
    bool multiHoudini(vector<HornRuleExt*>& worklist, bool recur = true)
    {
      if(debug >= 7) {
        outs() << "\n**** WORKLIST ****\n\n";
        for(auto& v: worklist) {
          outs() << v->body << "\n\n";
        }
        outs() << "\n****          ****\n\n";
      }

      if (!anyProgress(worklist)) {
        if (debug >= 5) outs() << "No progress\n";
        return false;
      }
      auto candidatesTmp = candidates;
      bool res1 = true;
      for (auto & hr : worklist)
      {
        if (hr->isQuery) continue;
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

    Result_t elba(ExprSet& third, Expr src, Expr dst)
    {
      if (debug >= 3)
        outs() << "\n  ===================\n" <<
                    "  ||    E L B A    || \n" <<
                    "  ===================\n\n";

      filterUnsat();
      Expr pc = ghostVars[0];
      Expr rel = tr->srcRelation;
      vector<HornRuleExt*> worklist;
      for (auto & hr : ruleManager.chcs)
      {
        if (containsOp<ARRAY_TY>(hr.body)) hasArrays = true;
        if((hr.isInductive/* && hr.srcRelation == rel*/) || hr.isFact || hr.isQuery) {
          worklist.push_back(&hr);
        }
      }
      if (debug > 1) outs () << "stage 0\n";
      auto candidatesTmp = candidates;
      multiHoudiniExtr(worklist);


      // stage 0:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 0) return Result_t::UNKNOWN;

      Expr learnedLemmasInv = conjoin(candidates[invDecl], m_efac);
      candidates = candidatesTmp;
      for (auto & a : candidatesTmp[invDecl])
      {
        if (!isOp<ComparissonOp>(a)) continue;
        if (isOpX<EQ>(a)) continue;
        if (contains(a, pc)) continue;
        ExprVector vars, varsPr;
        for (int i = 0; i < tr->dstVars.size(); i++)
        {
          if (!contains(a, tr->srcVars[i])) continue;
          vars.push_back(tr->srcVars[i]);
          varsPr.push_back(tr->dstVars[i]);
        }

        // if (vars.size() > 2) continue;  GF: to check if uncommenting this line helps anywhere
        auto b = replaceAll(
                  keepQuantifiers(mk<AND>(a, learnedLemmasInv, tr->body), varsPr),
                  varsPr, vars);
        getConj(mk<AND>(a, b), candidates[invDecl]);
      }

      if (debug > 1) outs () << "stage 1\n";
      candidatesTmp = candidates;
      multiHoudiniExtr(worklist);

      // stage 1:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 1) return Result_t::UNKNOWN;


      candidates = candidatesTmp;
      for (auto & c : third)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }

      if (debug > 1) outs () << "stage 2\n";
      multiHoudiniExtr(worklist);

      // stage 2:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      if (strenBound == 2) return Result_t::UNKNOWN;


      ExprSet cnjs, cnjsUpd;
      getConj(stren[dst], cnjs);
      for (auto s : cnjs)
      {
        s = simplifyArithm(u.removeITE(u.simplifiedAnd(
          mkNeg(keepQuantifiers(mkNeg(mk<IMPL>(tr->body,
                    replaceAll(s, tr->srcVars, tr->dstVars))),
                      tr->srcVars)),
          replaceAll(conjoin(candidates[specDecl], m_efac),
                      fc->srcVars, tr->srcVars))));

        getConj(s, cnjsUpd);
      }
      for (auto & c : cnjsUpd)
      {
        candidates[specDecl].insert(replaceAll(c, tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(c);
      }

      if (debug > 1) outs () << "stage 3\n";
      multiHoudiniExtr(worklist);

      // stage 3:
      if (checkAllOver(true, true, src, dst)) return Result_t::UNSAT;

      return Result_t::UNKNOWN;
    }

    void filterBounds(map<Expr,ExprSet> &bounds, ExprSet &grds, ExprVector &boundsV) {
      ExprVector tmpBounds, tmpGuards;

      for (auto& e: bounds[invDecl])
      {
        if (!isOpX<MULT>(e->left()))
        {
          boundsV.push_back(e);
        }
        else if (tmpBounds.empty())
        {
          ExprSet vars;
          filter (e, bind::IsConst (), inserter (vars, vars.begin()));
          if (vars.size() < 3) continue; // hack, to avoid short cands

          if (isOpX<MPZ>(e->left()->left()) && e->left()->right() == ghostVars[0])
          {
            tmpBounds.push_back(mk<EQ>(ghostVars[0], mk<IDIV>(e->right(), e->left()->left())));
            tmpGuards.push_back(mk<EQ>(mk<MOD>(e->right(), e->left()->left()), mkMPZ(0, m_efac)));
            if (debug > 2) outs () << "  IDIVs:\n    " << tmpBounds.back() << "\n    " << tmpGuards.back() << "\n";
          }
        }
      }

      if (strenBound == 10 && boundsV.empty() && !tmpBounds.empty())
      {
        boundsV.push_back(tmpBounds[0]);
        grds.insert(tmpGuards.begin(), tmpGuards.end());
      }

      ExprSet nb;
      for (auto & a : boundsV)
        for (auto & z : zs)
          nb.insert(mk<EQ>(a->left(), mk<PLUS>(a->right(), z)));

      boundsV.insert(boundsV.end(), nb.begin(), nb.end());
      sortBounds(boundsV);
    }

    ExprSet zs;
    boost::tribool boundSolve(Expr src, Expr dst, Expr block, int lvl = 0) {
      map<Expr,ExprSet> bounds;
      dataGrds.clear();

      outs() << "loopGuard: " << loopGuard << "\n";
      outs() << "fcBodyInvVars: " << fcBodyInvVars << "\n";

      if (!u.isSat(fcBodyInvVars,loopGuard)) {
        if (debug >= 2) outs() << "PROGRAM WILL NEVER ENTER LOOP\n";
        return true;
      }
      if (debug >= 2) {
        outs() << "  boundSolve [" << lvl << "]:\n    " << block << "\n";
      }

      if (isOpX<FALSE>(dst))
      {
        grds2gh[src] = mkMPZ(0, m_efac);
        if (debug >= 2) outs () << "  assign 0 grds2gh (0) for " << src << "\n";
        return true;
      }

      outs() << "entering exploreBounds\n";
      boost::tribool res = exploreBounds(src, dst, bounds, block);
      if (res == false)
      {
        outs() << "false\n";
        return true;
      }
      else if (res == indeterminate) {
        outs () << "unknown\n";     // TODO: actually some backtracking !!
        exit(0);
        // return indeterminate;
      }

      ExprSet grds, grdsDst;
      getConj(dst, grdsDst);
      genCands(grdsDst, ghostVars[0]);
      getConj(src, grds);

      zs.clear();
      if (dg) {
        for (auto& e: dataGrds) {

          ExprSet vars;
          filter (e, bind::IsConst (), inserter (vars, vars.begin()));

          if (isOpX<EQ>(e)){

           if (!hasMPZ(e) && vars.size() > 1)
            {
              grds.insert(e);
              if (debug >= 3)
                outs() << "Adding guard from data: " << e << "\n";
            }
            else {
              if (lexical_cast<string>(e->right()) == "0" && vars.size() == 1)
                zs.insert(*vars.begin());
            }
          }
        }
      }
      if (debug >= 2)
        for (auto& e: grds) outs() << "    grd: " << e << "\n";

      if (bounds[invDecl].size() == 0) res = false;

      ExprVector boundsV;
      filterBounds(bounds,grds,boundsV);

      if (debug >= 2) {  //GF
        outs() << "\n  Bounds found this iteration\n";
        for (auto& e: boundsV) {
          outs() << "    " << e << "\n";
        }
      }

      bool rerun = false;
      // Loop through bounds.

      for(int i = 0; i < boundsV.size() && res; i++) {
        candidates.clear();

        if (rerun) {
          if (debug >= 3) outs() << "RERUN\n=====\n";
          i--;
          for (auto& e: fgrds2gh) { // There is never anything added to fgrds2gh... but the rerun seems to help in some cases.
            candidates[invDecl].insert(e.first);
          }
        }
        else {
          for (auto& e: grds) {
            candidates[specDecl].insert(replaceAll(e, tr->srcVars, fc->srcVars));
            candidates[invDecl].insert(e);
          }
        }
        candidates[specDecl].insert(replaceAll(boundsV[i], tr->srcVars, fc->srcVars));
        candidates[invDecl].insert(boundsV[i]);

        // ExprSet factCands;
        // getConj(keepQuantifiers(fc->body, fc->srcVars), factCands);
        // for (auto & c : factCands)
        // {
        //   candidates[specDecl].insert(c);
        //   candidates[invDecl].insert(replaceAll(c, fc->srcVars, tr->srcVars));
        // }

        if (debug >= 2) outs() << "\n  >> Considering bound " << boundsV[i] << "\n\n";

        Result_t res_t = elba(grdsDst, // SyntInv
          mk<AND>(src, replaceAll(src, tr->srcVars, fc->srcVars)), dst);

        if (debug >= 3) {
          outs() << "==================\n";
          printCandsEx();
          outs() << "==================\n";
        }

        if (res_t == Result_t::UNKNOWN) {
          candidates.clear();
          if (!rerun) {
            rerun = true;
          }
          else {
            rerun = false;
          }
          if (debug >= 2) outs() << "  unknown\n\n";
          if (i+1 == boundsV.size()) {
            if (phaseNum < phases.size())
              block = mk<TRUE>(m_efac);
              //continue;
              //boundSolve(src, dst, mk<TRUE>(m_efac), lvl); // refactor to remove this recursion.
          }
          continue;
        }

        // If you're here then G&S returned UNSAT
        // Yes, I'm here.
        if (debug >= 2) outs() << "  >> unsat (bound is good)\n";
        rerun = false;

        parseForGuards(); // Associates guards (pre(Vars)) with Expr gh = f()
                          // They are stored in grds2gh map.

        if (debug >= 2) {
         outs() << "  Guards/bounds:\n";
         for (auto& g: grds2gh) {
           outs() << "    (*)  " << g.first << "\n";
           outs() << "         ->  " << g.second << "\n";
         }
        }

        ExprSet grds2;
        for (auto& g: grds2gh) {
         if (u.implies(g.first, src))
           grds2.insert(g.first);
        }
        Expr grd = disjoin(grds2,m_efac);
        if (debug >= 4) outs() << "grd: " << grd << "\n";
        if (u.isSat(mkNeg(grd), src)) { // More exploration needed.
          // block = mkNeg(grd);
          // lvl++;
          // bounds.clear();
          // res = exploreBounds(src, dst, bounds, block);
          // for (auto& e: dataGrds) {
          //
          //   ExprSet vars;
          //   filter (e, bind::IsConst (), inserter (vars, vars.begin()));
          //
          //   if (isOpX<EQ>(e)){
          //
          //    if (!hasMPZ(e) && vars.size() > 1)
          //     {
          //       grds.insert(e);
          //       if (debug >= 3)
          //         outs() << "Adding guard from data: " << e << "\n";
          //     }
          //     else {
          //       if (lexical_cast<string>(e->right()) == "0" && vars.size() == 1)
          //         zs.insert(*vars.begin());
          //     }
          //   }
          // }
          // filterBounds(bounds,grds,boundsV);
          if (boundSolve(src, dst, mkNeg(grd), lvl + 1)) { // refactor to remove this recursion.
            return true;
          }
        }
        else
        {
         return true;
        }

      }

      outs() << "exiting boundSolve\n";
      return true;
    }

    map<Expr,ExprSet> allFinals;
    void pathsSolve(Expr rel) {
      ExprSet finals;
      grds2gh.clear();
      for(auto& p: pathsMap[rel]) {
        if (debug >= 2) {
          outs () << "\n===== NEXT PATH =====\n    ";
          for (auto & pp : p)
          outs () << pp << " -> ";
          outs () << "\n";
        }

        assert(p.size() > 1);
        Expr res;
        int i;
        for (i = p.size() - 2; i >= 0; i--)
        {
          if (p[i] == fcBodyInvVars)
          {
            assert(i == 0);
            break;
          }
          boundSolve(p[i], p[i+1], eTrue);

          res = NULL;
          ExprSet pre;
          outs() << "SIZE: " << grds2gh.size() << "\n";
          for (auto& g: grds2gh)
          {
            outs() << g.first << " => " << p[i] << "  ??\n";
            if (u.implies(g.first, p[i]))
            {
              pre.insert(g.first);
              if (res == NULL) res = g.second;
              else res = mk<ITE>(g.first, g.second, res);   // GF
            }
          }
          stren[p[i]] = simplifyBool(distribDisjoin(pre, m_efac));
          if(debug >= 3) outs() << "stren[p[" << i << "]]: " << stren[p[i]] << "\n";
          if (i != 0) grds2gh[p[i]] = res;
        }

        if(res == NULL) outs() << "\n***** RES IS NULL *****\n" << std::endl;
        finals.insert(mk<IMPL>(stren[p[1]], mk<EQ>(ghostVars[0], res)));
        grds2gh.clear();
        stren.clear();
      }
      outs () << "FINAL:\n";
      pprint(finals, 5);
      allFinals[rel] = finals;
    }

    // void makeHyperChains(std::set<int> cycles) {
    //   if(debug >= 2) outs() << "\n=== MAKE HYPER CHAINS ===\n\n";
    //   if(debug >= 3) printPathsMap();
    //
    //   auto cycle = cycles.rbegin();
    //
    //   for(auto& pm: pathsMap) {
    //     if(pathsMap.size() == 1) {
    //       for(auto& m: pm.second) {
    //         ExprVector hc;
    //         hc.insert(hc.end(), m.begin(), m.end());
    //         hyperChains.push_back(hc);
    //       }
    //       return;
    //     }
    //     for(auto& pm2: pathsMap) {
    //       if(pm == pm2) continue;
    //       setPointers(1 + 2*(getVarIndex(pm2.first, decls)));
    //
    //       // Now link up the chains for each loop together
    //       // to make Hyper Chains.
    //       for(auto& vpm: pm.second) {
    //         for(auto& vpm2: pm2.second) {
    //           Expr last = *(++(vpm.rbegin()));
    //           Expr first = *(++(vpm2.begin()));
    //           if(last == first) {
    //             // Now connect the chains.
    //             ExprVector chain1, chain2;
    //             chain1.insert(chain1.end(), vpm.begin(), --(vpm.end()));
    //             chain2.insert(chain2.end(), ++(++(vpm2.begin())), vpm2.end());
    //             ExprSet conjs;
    //             getConj(tr->body,conjs);
    //             getConj(chain1.back(),conjs);
    //             getConj(replaceAll(chain2.front(), invVars, invVarsPr),conjs);
    //             if(u.isSat(conjs)) {
    //               if(debug >= 3) outs() << "ADDING TO HYPER CHAIN\n";
    //               if(*(chain1.end()) != *(chain2.begin())) {
    //                 ExprVector hc;
    //                 if(debug >= 5) {
    //                   outs() << "\n=== CONNECT CHAINS ===\n\n";
    //                   for(auto& v: chain1) outs() << v << " -> ";
    //                   outs() << "\n";
    //                   for(auto& v: chain2) outs() << v << " -> ";
    //                   outs() << "\n";
    //                 }
    //                 hc.insert(hc.end(), chain1.begin(), chain1.end());
    //                 hc.insert(hc.end(), chain2.begin(), chain2.end());
    //                 hyperChains.push_back(hc);
    //               }
    //             }
    //           }
    //         }
    //       }
    //     }
    //     cycle++;
    //   }
    //   if(debug >= 4) {
    //     outs() << "\n=== HYPER CHAINS FOUND ===\n\n";
    //     for(auto& v: hyperChains) {
    //       for(auto& hc: v) {
    //         outs() << "  " << hc << " -> ";
    //       }
    //       outs() << "\n";
    //     }
    //   }
    // }

    int lastCycle;
    void startPathFinding() {
      std::set<int> cycles;
      if(debug >= 3) outs() << "cycles size: " << ruleManager.cycles.size() << "\n";

      for(auto& c: ruleManager.cycles) {
        for(auto& cc: c) {
          cycles.insert(cc);
        }
      }

      // At this point we have the CHCs set up with ghost vars.
      // Now we need to collect the possible paths through the program.
      // Done in a general way, this should collect "Predicate chains"
      // for each loop, with no assumptions made on the input.
      // Then, beginning at the first loop, the Init condition is considered.
      // Each of the potential paths through the loops are connected by
      // considering the last link in the previous loop and the first link
      // in the next loop.

      lastCycle = *cycles.rbegin();
      Expr lastRel = ruleManager.chcs[lastCycle].srcRelation;
      allFinals[lastRel].insert(mk<EQ>(ghostVars[0], mpzZero));

      collectPhaseAtomics(cycles);
      makeCombs();
      pairLinks(cycles);
      makePredicateChains();

      for(auto i = cycles.rbegin(); i != cycles.rend(); i++) {
        Expr rel = ruleManager.chcs[*i].srcRelation;
        // If there are many previous bounds then they all need to be used in the qr.
        ExprSet lastFinals = allFinals[lastRel];
        for(auto bi = lastFinals.begin(); bi != lastFinals.end(); bi++) {
          setPointers(*i, *bi); // This is where the QR is set for the next run.
          pathsSolve(rel);
        }

        lastCycle = *i;
        lastRel = rel;
      }
    }

    void printCandsEx(bool ppr = true) {
      for (auto& a: candidates) {
        outs() << "(define-fun " << *a.first << " (";
        for (auto & b : ruleManager.invVars[a.first])
        {
          outs() << "(" << *b << " " << u.varType(b) << ")";
        }
        outs() << ") Bool\n";

        if (ppr) pprint(a.second, 3);
        else u.print(conjoin(a.second,m_efac));
        outs() << "\n\n";
      }
    }

  }; // end class BoundSolver

  inline void findBounds(string smt, int inv, int stren, bool dg,
                          bool data2, bool doPhases, int debug = 0)
  {
    ExprFactory m_efac;
    EZ3 z3(m_efac);
    CHCs ruleManager(m_efac, z3, debug);
    ruleManager.parse(smt);
    BoundSolver spec(ruleManager, stren, dg, data2, doPhases, debug);
    if (!ruleManager.hasQuery) { // Horn.hpp has been changed to omit queries.
      if(debug >= 2) {
        if (ruleManager.decls.size() > 1) {
          outs() << "Multiple loops\n";
  //        return;
        }
        else {
          outs() << "Single loop\n";
        }
      }
      // refactor to ELBA to use ruleManager properly instead of using
      // HornRuleExt pointers for only 3 rules at a time.
      if (debug >= 3) ruleManager.print(true);
    }
    else {
      outs() << "Contains Query\n";
//      return;
    }
    spec.setUpQueryAndSpec();
    if(debug >= 3) outs() << "startPathFinding\n";
    spec.startPathFinding();
    // for(auto& c: ruleManager.cycles) {
    //   for(auto& cc: c) {
    //     spec.collectPhaseGuards(cc); // needs to move to cycle through each TR.
    //     outs() << "cycle: " << cc << "\n";
    //   }
    // }
//    if (debug >= 2) spec.printPhases();
    // spec.pathsSolve();
  }
} // end namespace ufo

#endif
