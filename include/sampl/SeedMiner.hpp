#ifndef SEEDMINER__HPP__
#define SEEDMINER__HPP__

#include "ae/AeValSolver.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  class SeedMiner
  {
    public:

    // for arrays
    ExprSet arrCands;
    ExprSet arrSelects;
    ExprSet arrIterRanges;
    ExprSet arrAccessVars;
    ExprSet arrFs;

    ExprSet candidates;
    set<cpp_int> intConsts;
    set<cpp_int> intCoefs;

    HornRuleExt& hr;
    Expr invRel;
    map<int, Expr>& invVars;
    ExprMap& extraVars;

    ExprFactory &m_efac;

    SeedMiner(HornRuleExt& r, Expr& d, map<int, Expr>& v, ExprMap& e) :
      hr(r), invRel(d), invVars(v), extraVars(e), m_efac(d->getFactory()) {};

    void getArrRange (Expr tmpl)
    {
      // keep using this method for a while; to replace by something smarter
      ExprSet dsjs;
      ExprSet tmp;
      getDisj(tmpl, dsjs);
      ExprVector invAndIterVarsAll;
      for (auto & a : invVars) invAndIterVarsAll.push_back(a.second);

      for (auto dsj : dsjs)
      {
        ExprSet se;
        filter (dsj, bind::IsSelect (), inserter(se, se.begin()));
        if (se.size() == 0)
        {
          tmp.insert(mkNeg(dsj));
          continue;
        }

        for (auto & a : se)
        {
          Expr var = a->right();
          if (isOpX<MPZ>(var))
          {
            string varName = "_FH_tmp_iter_" + lexical_cast<string>(var);
            Expr newVar = bind::intConst(mkTerm<string> (varName, m_efac));
            tmp.insert(mk<EQ>(newVar, var));
            var = newVar;
          }
          if (bind::isIntConst(var) && find(invAndIterVarsAll.begin(),
                    invAndIterVarsAll.end(), var) == invAndIterVarsAll.end())
          {
            arrAccessVars.insert(var);
            if (find(invAndIterVarsAll.begin(), invAndIterVarsAll.end(),
                     var) == invAndIterVarsAll.end())
              invAndIterVarsAll.push_back(var);
          }
        }
      }

      for (auto & e : tmp)
      {
        if (emptyIntersect(e, arrAccessVars)) continue;
        ExprSet rangeTmp;
        getConj(convertToGEandGT(e), rangeTmp);
        for (auto & a : rangeTmp) arrIterRanges.insert(normalizeDisj(a, invAndIterVarsAll));
      }
    }

    void addArrCand (Expr tmpl)
    {
      if (!emptyIntersect(tmpl, hr.dstVars)) return;

      ExprSet dsjs;
      ExprSet newDsjs;
      getDisj(tmpl, dsjs);

      for (auto dsj : dsjs)
      {
        ExprSet se;
        filter (dsj, bind::IsSelect (), inserter(se, se.begin()));
        if (se.size() == 0) continue;

        ExprVector invAndIterVars;
        for (auto & a : invVars) invAndIterVars.push_back(a.second);

        for (auto & a : se)
        {
          if (isOpX<STORE>(a->first()) ||
              isOpX<ITE>(a->first()))
          {
            // FIXME: should not fall here
            return;
          }
          arrSelects.insert(a);
          unique_push_back(a, invAndIterVars);

          ExprSet vrs;
          filter (a, bind::IsConst(), std::inserter (vrs, vrs.begin ()));
          for (auto & v : vrs) unique_push_back(v, invAndIterVars);
        }

        ExprSet arrCandsTmp;
        getConj(convertToGEandGT(dsj), arrCandsTmp);
        for (auto & a : arrCandsTmp)
        {
          Expr tmpl = findNonlinAndRewrite(a, invAndIterVars, extraVars);
          for (auto &b : extraVars) invAndIterVars.push_back(b.second);
          Expr normalized = normalizeDisj(tmpl, invAndIterVars);
          if (!containsOp<SELECT>(normalized)) continue;

          ExprSet vrs;
          filter (normalized, bind::IsConst(), std::inserter (vrs, vrs.begin ()));
          bool sanitized = true;
          for (auto & b : vrs)
          {
            if (emptyIntersect(b, invAndIterVars))
            {
              sanitized = false;
              break;
            }
          }
          if (sanitized) newDsjs.insert(normalized);
        }
      }

      if (newDsjs.size() > 0)
      {
        Expr cand = disjoin(newDsjs, m_efac);
        arrCands.insert(cand);
      }
    }

    void addSeedHlp(Expr tmpl, ExprVector& vars, ExprSet& actualVars)
    {
      // outs() << "getting seeds from: " << tmpl << "\n";
      ExprSet dsjs;
      ExprSet newDsjs;
      getDisj(tmpl, dsjs);
      for (auto & dsj : dsjs)
      {
        // outs() << "dsj: " << dsj << "\n";
        ExprSet vrs;
        // check isconst.
        filter (dsj, bind::IsConst(), std::inserter (vrs, vrs.begin ()));
        bool found = true;

        for (auto & a : vrs)
        {
          // outs() << "var: " << a << "\n";
          if (std::find(std::begin(vars), std::end (vars), a)
              == std::end(vars)) { found = false; break; }
        }
        if (found) newDsjs.insert(dsj);
      }

      // outs() << "newDsjs.size(): " << newDsjs.size() << "\n";

      if (newDsjs.size() == 0) return;

      ExprVector invVarsCstm;
      for (auto & a : invVars) invVarsCstm.push_back(a.second);

      tmpl = disjoin (newDsjs, m_efac);

      for (auto &v : actualVars)
      {
        int index = getVarIndex(v, vars);
        if (index >= 0)
        {
          tmpl = replaceAll(tmpl, v, invVars[index]);
        }
      }

      tmpl = findNonlinAndRewrite(tmpl, invVarsCstm, extraVars, true);
      // outs() << "tmpl: " << tmpl << "\n";

      for (auto &a : extraVars) invVarsCstm.push_back(a.second);
      tmpl = normalizeDisj(tmpl, invVarsCstm);
      // outs() << "after normalized: " << tmpl << "\n";

      if (!isOpX<FALSE> (tmpl) && !isOpX<TRUE> (tmpl))
      {
        // get int constants from the normalized candidate
        ExprSet intConstsE;
        if(has_bvsort(tmpl))
        {
          filter (tmpl, bind::IsBVConst(), std::inserter (intConstsE, intConstsE.begin ()));
          for (auto &a : intConstsE)
          {
            intConsts.insert(lexical_cast<cpp_int>(toMpz(a)));
          }
          if (getBVCombCoefs(tmpl, intCoefs))
          {
            // outs() << "\n*** adding cand: " << tmpl << "\n";
            candidates.insert(tmpl);
          } 
        }
        else
        {
          filter (tmpl, bind::IsHardIntConst(), std::inserter (intConstsE, intConstsE.begin ()));
          for (auto &a : intConstsE) intConsts.insert(lexical_cast<cpp_int>(a));
          if (getLinCombCoefs(tmpl, intCoefs))
          {
            // outs() << "Adding LIA cand: " << tmpl << "\n";
            candidates.insert(tmpl);
          } 
        }
      }
    }

    void addSeed(Expr fla)
    {
      if (containsOp<SELECT>(fla) || containsOp<STORE>(fla))
      {
        if (containsOp<STORE>(fla) || containsOp<ITE>(fla) || containsOp<AND>(fla))
        {
          Expr term2 = unfoldITE(rewriteSelectStore(unfoldITE(fla)));
          if (fla == term2)
            return;
          else  // mutual recursive call: extra processing for arrays
            obtainSeeds(term2);
        }
        else
          addArrCand(fla);
      }

      ExprSet actualVars;
      filter (fla, bind::IsConst(), std::inserter (actualVars, actualVars.begin ()));

      fla = rewriteMultAdd(fla);

      bool locals = false;
      if (actualVars.size() == 0 || isTautology(fla)) return;

      // split each fla to two seeds (for srcVars and dstVars)

      if (hr.srcRelation == invRel)
      {
        addSeedHlp(fla, hr.srcVars, actualVars);
      }

      if (hr.dstRelation == invRel)
      {
        addSeedHlp(fla, hr.dstVars, actualVars);
      }
    }

    void obtainSeeds(Expr fla)
    {
      if (bind::isBoolConst(fla))
      {
        addSeed(fla);
      }
      else if (isOpX<NEG>(fla))
      {
        Expr negged = fla->last();
        if (bind::isBoolConst(negged))
          addSeed(fla);
        else if (isOp<ComparissonOp>(negged) || isOpX<BvOp>(negged))
          obtainSeeds(mkNeg(negged));
        else
          obtainSeeds(negged);
      }
      else if (isOpX<OR>(fla))
      {
        if (containsOp<AND>(fla))
        {
          Expr term2 = convertToGEandGT(rewriteOrAnd(fla));
          obtainSeeds(term2);
        }
        else
        {
          // outs() << "fla: " << fla << "\n";
          Expr simplified = simplifyArithmDisjunctions(fla);
          // outs() << "simplified: " << simplified << "\n";
          simplified = convertToGEandGT(simplified);
          // outs() << "simplified: " << simplified << "\n";
          simplified = normalize(simplified);
          // outs() << "Normalized: " << simplified << "\n";
          addSeed(simplified);
        }
      }
      else if (isOpX<AND>(fla))
      {
        for (int i = 0; i < fla->arity(); i++)
        {
          obtainSeeds(fla->arg(i));
        }
      }
      else if (isOpX<IMPL>(fla))
      {
        Expr term2 = mk<OR>(mkNeg(fla->left()), fla->right());
        obtainSeeds(term2);
      }
      else if (isOpX<GT>(fla) || isOpX<GEQ>(fla))
      {
        addSeed(fla);      // get rid of ITEs first
      }
      else if (isOpX<BUGT>(fla) || isOpX<BUGE>(fla))
      {
        addSeed(fla);      // get rid of ITEs first
      }
      else if (isOp<ComparissonOp>(fla) || isOpX<BvOp>(fla))
      {
        if (containsOp<ARRAY_TY>(fla)) addSeed(fla);
        else
        {
          Expr tmp = convertToGEandGT(fla);
          if (tmp != fla)
          {
            obtainSeeds(tmp);
          }
          else
          {
            errs () << "COULD NOT SEEDMINE: " << *tmp << "\n";
            return;
          }
        }
      }
    }

    void coreProcess(Expr e)
    {
      e = rewriteBoolEq(e);
      e = moveInsideITE(e);
      e = unfoldITE(e);
      e = convertToGEandGT(e);
      e = rewriteNegAnd(e);
      obtainSeeds(e);
    }

    void analyzeExtra(Expr extra)
    {
      Expr e = propagateEqualities(extra);
      e = rewriteSelectStore(e);
      coreProcess(e);
    }

    void analyzeExtras(ExprSet& extra)
    {
      for (auto &cnj : extra) analyzeExtra(cnj);
    }

    Expr removeRedundant(Expr e)
    {
      // remove Exprs like x > x
      ExprSet conjs, res;
      getConj(e, conjs);
      for (auto &a : conjs)
      {
        Expr left = a->left();
        Expr right = a->right();
        if (left == right)
        {
          continue;
        }
        else
        {
          res.insert(rewriteMultAddBV(a));
        }
      }

      return conjoin(res, m_efac);
    }

    void analyzeCode()
    {
      if (containsOp<FORALL>(hr.body) || containsOp<EXISTS>(hr.body)) return;
      // todo: support

      Expr body = hr.body;

      // outs() << "Analyzing: " << body << "\n";

      // get a set of all access functions before any transformation
      // since some sensitive information can be lost:
      retrieveAccFuns(body, arrFs);

      ExprSet quantified;
      for (auto &v : hr.locVars) quantified.insert(v);
      if (hr.srcRelation != invRel) for (auto &v : hr.srcVars) quantified.insert(v);
      if (hr.dstRelation != invRel) for (auto &v : hr.dstVars) quantified.insert(v);

      if (hr.srcRelation == invRel)
        for (int i = 0; i < hr.srcVars.size(); i++)
          if (invVars[i] == NULL) quantified.insert(hr.srcVars[i]);

      if (hr.dstRelation == invRel)
        for (int i = 0; i < hr.dstVars.size(); i++)
          if (invVars[i] == NULL) quantified.insert(hr.dstVars[i]);

      body = rewriteSelectStore(body);
      body = eliminateQuantifiers(body, quantified);
      body = weakenForVars(body, quantified);

      // outs() << "body after some processing: " << body << "\n";


      // get seeds and normalize
      ExprSet conds;
      retrieveConds(body, conds);
      // outs() << "conds: \n";
      // for(auto& c: conds)
      //   outs() << "cond: " << c << "\n";

      for (auto & a : conds) obtainSeeds(a);

      // for the query: add a negation of the entire non-recursive part:
      if (hr.isQuery)
      {
        // outs() << "analyzing query\n";
        if(has_bvsort(body))
        {
          Expr e = mkNeg(propagateEqualities(hr.body)); 
          e = unfoldITE(e);
          e = convertToGEandGT(e);
          // outs() << "obtaining seed from query: " << e << "\n";
          obtainSeeds(e);
        }
        else
        {
          Expr massaged = mkNeg(propagateEqualities(hr.body));
          // outs() << "massaged: " << massaged << "\n";
          coreProcess(massaged);
          getArrRange(massaged);
        }
      }
      else if (hr.isFact)
      {
        Expr e = unfoldITE(body); 
        e = propagateEqualities(e);

        if (has_bvsort(body))
        {
          e = convertToGEandGT(e);
          // outs() << "obtaining seed from fact: " << e << "\n";
          obtainSeeds(e);
        }
        else
        {
          coreProcess(e);
        }
      }
      else
      {
        // hr.isInductive
        Expr e = unfoldITE(body);
        // outs() << "After unfoldITE: " << e << "\n";
        ExprSet deltas; // some magic here for enhancing the grammar
        retrieveDeltas(e, hr.srcVars, hr.dstVars, deltas);
        for (auto & a : deltas) obtainSeeds(a);
        ExprVector vars2elim;
        int varslimit = hr.srcVars.size() < hr.dstVars.size() ?
                        hr.srcVars.size() : hr.dstVars.size();
        for (int i = 0; i < varslimit; i++)
          if (containsOp<ARRAY_TY>(hr.srcVars[i]))
            vars2elim.push_back(hr.srcVars[i]);
          else
            vars2elim.push_back(hr.dstVars[i]);
        
        if(has_bvsort(e))
        {
          // outs() << "After has_bvsort: " << e << "\n";
          e = eliminateQuantifiersRepl(e, vars2elim);
          // outs() << "After eliminateQuantifiersRepl: " << e << "\n";
          e = convertToGEandGT(e);
          // outs() << "After convertToGEandGT: " << e << "\n";
          e = replaceAll(e, hr.dstVars, hr.srcVars);
          // outs() << "After replaceAll: " << e << "\n";
          e = removeRedundant(e);
          // outs() << "obtaining seed from TR: " << e << "\n";
        }
        else
        {
          e = eliminateQuantifiersRepl(e, vars2elim);
          e = simplifyBool(e);
          e = rewriteBoolEq(e);
          e = convertToGEandGT(e);
          e = rewriteNegAnd(e);
        }
        // outs() << "Obtaining seeds from: " << e << "\n";
        obtainSeeds(e);
      }

      // outs() << "Finished analyzing: " << body << "\n";
      // for(auto& c: candidates)
      // {
      //   outs() << "  Candidate: " << c << "\n";
      // }
    }
  };
}

#endif
