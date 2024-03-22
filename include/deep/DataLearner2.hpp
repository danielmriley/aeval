#ifndef DATALEARNER2__HPP__
#define DATALEARNER2__HPP__

#include <vector>

#include "Horn.hpp"
#include "BndExpl.hpp"

using namespace std;
using namespace boost;
using namespace boost::multiprecision;

namespace ufo
{
  class DataLearner2
  {
  private:
    CHCs& ruleManager;
    BndExpl bnd;
    ExprFactory &m_efac;
    map<Expr, vector< vector< double> > > models;
    map <Expr, ExprVector> invVars;
    map<Expr, ExprSet> dc;
    int debug;

    void createCandsFromData(Expr srcRel)
    {
      if(debug > 0) outs() << "Creating candidates from data for " << *srcRel << "\n";

      dc.clear();
      if (models[srcRel].size() < 2)
      {
        vector<double> e1 = *models[srcRel].rbegin();
        for(int i = 0; i < e1.size(); i++)
        {
          // Expr e = mk<EQ>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]), m_efac));
          // dc[srcRel].insert(e);
          // if(debug > 0) outs() << "  CONNECT: " << *e << "\n";
          ExprSet ev;
          for(int j = 0; j < e1.size(); j++)
          {
            if(i == j) continue;
            Expr r = mk<MINUS>(invVars[srcRel][i], invVars[srcRel][j]);
            Expr l = mk<MINUS>(mkMPZ(cpp_int(e1[i]), m_efac), mkMPZ(cpp_int(e1[j]), m_efac));
            l = mk<EQ>(l, r);
            l = simplifyArithm(l);
            l = normalize(l);
            if(l == mk<TRUE>(m_efac)) continue;
            ev.insert(l);
            if(debug >= 4) outs() << "  CONNECT: " << l << "\n";
          }
          for(auto it = ev.begin(); it != ev.end(); it++)
          {
            dc[srcRel].insert(*it);
          }
        }
        return;
      }
      auto ritr = models[srcRel].rbegin();
      vector<double> e1 = *ritr;
      ritr++;
      vector<double> e2 = *ritr;
      ExprVector ev;

      int n = invVars[srcRel].size();
      if(debug > 3) outs() << "n: " << n << "\n";
      // make Exprs.
      /*
      for (int i = 0; i < n-1; i++) {
        for (int j = i + 1; j < n-1; j++) {
          if (e1[i]==e1[j]) {
            Expr r2 = mk<MINUS>(invVars[srcRel][i], invVars[srcRel][j]);
            dc[srcRel].insert(mk<EQ>(invVars[srcRel][n-1], r2));
            r2 = mk<MINUS>(invVars[srcRel][j], invVars[srcRel][i]);
            dc[srcRel].insert(mk<EQ>(invVars[srcRel][n-1], r2));
          }
        }
      }
      */
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          Expr r1,r2,l1,l2,l,r;
          r1 = mkMPZ(cpp_int(e2[j] - e1[j]),m_efac);
          r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]),m_efac));
          l1 = mkMPZ(cpp_int(e2[i] - e1[i]),m_efac);
          l2 = mk<MINUS>(invVars[srcRel][j], mkMPZ(cpp_int(e1[j]),m_efac));
          if (e2[j] - e1[j] == 0) {
            r1 = mkMPZ(0,m_efac);
          }
          else {
            r1 = mk<MULT>(r1,r2);
          }
          if (e2[i] - e1[i] == 0) {
            l1 = mkMPZ(0,m_efac);
          }
          else {
            l1 = mk<MULT>(l1,l2);
          }
          l = mk<EQ>(r1,l1);
          l = simplifyArithm(l);
          l = normalize(l);
          if (l == mk<TRUE>(m_efac)) continue;
          ev.push_back(l);
          if (debug >= 4) outs() << "  CONNECT: " << *ev.back() << "\n";
        }
      }
      if (debug >= 4) outs() << "\n";
      // ADD or SUBTRACT each equation from another to generate data candidates.
      for (int i = 0; i < ev.size(); i++) {
        dc[srcRel].insert(normalize(ev[i]));
        for (int j = i + 1; j < ev.size(); j++) {
          Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
          Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l,r);
          l = normalize(l);
          if (l == mk<TRUE>(m_efac)) continue;
          dc[srcRel].insert(l);
          if (debug >= 4) outs() << "  CONNECT: " << l << "\n";

          r = mk<PLUS>(ev[i]->right(), ev[j]->right());
          l = mk<PLUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l,r);
          l = normalize(l);
          if (l == mk<TRUE>(m_efac)) continue;
          dc[srcRel].insert(l);
          if (debug >= 4) outs() << "  CONNECT: " << l << "\n";
        }
      }

      // for (int i = 0; i < n - 1; i++) {
      //   for (int j = i + 1; j < n - 1; j++) {
      //     if(cpp_int(e1[i] * e1[j]) == cpp_int(e1[e1.size() - 1])) {
      //       Expr expr = mk<EQ>(invVars[srcRel][e1.size() - 1],
      //                    mk<MULT>(invVars[srcRel][i], invVars[srcRel][j]));
      //       dc[srcRel].insert(expr);
      //       if (debug >= 4) outs() << "  CONNECT*: " << expr << "\n";
      //     }
      //   }
      // }

    }

  public:
    DataLearner2(CHCs& r, EZ3& z3, int _debug) :
      ruleManager(r), bnd(ruleManager, (_debug > 0)), m_efac(r.m_efac), debug(_debug) {}

      boost::tribool connectPhase(Expr src, Expr dst, int k = 1,
                    Expr srcRel = NULL, Expr block = NULL, Expr invs = NULL,
                    Expr preCond = NULL)
      {
        // Get data matrix.
        // Refactor so that the matrix isn't built over and over.
        // seperate the BndExpl from DL2 so that DL2 is provided with the matrix rather
        // than creating it each time itself.
        boost::tribool res = bnd.unrollAndExecuteTermPhase
          (src, dst, srcRel, invVars[srcRel], models[srcRel], block, k);

        if(debug > 0 && res) {
          outs() << "RES IS TRUE\n";
        }
        else if(debug > 0 && !res) {
          outs() << "RES IS FALSE\n";
        }

        if (res) {
          createCandsFromData(srcRel);
        }
        return res;
      }

      void makeModel(Expr srcRel, ExprVector& forms)
      {
        ExprVector vars;
        filter(forms.front(), IsConst(), inserter(vars, vars.begin()));
        invVars[srcRel] = vars;
        // Expects normalized exprs.
        ExprVector conjs;
        for(auto it = forms.begin(); it != forms.end(); it++)
        {
          conjs.clear();
          getConj(*it, conjs);
          if(conjs.size() != 2) 
          {
            if(debug > 0) outs() << "Cannot process at this time: " << *it << "\n";
            return;
          }
          vector<double> row;
          for(int j = 0; j < conjs.size(); j++)
          {
            if(conjs[j]->left() == vars[j])
            {
              row.push_back(lexical_cast<double>(conjs[j]->right()));
            }
            else 
            {
              outs() << "ERROR\n";
              return;
            }
          }
          models[srcRel].push_back(row);
        }

        if(debug > 4) printModel(srcRel);

        createCandsFromData(srcRel);

        ExprSet alts;
        for(auto it: dc[srcRel])
        {
          Expr fla = conjs[0];
          Expr e;
          if (it->right() == mkMPZ(1, m_efac) && isOpX<GT>(fla))
          {
            e = mk<GEQ>(mkMPZ(0, m_efac), it->left());
            alts.insert(normalize(e, vars[0]));
          }
          else if (it->right() == mkMPZ(1, m_efac) && isOpX<LT>(fla))
          {
            e = mk<LEQ>(mkMPZ(0, m_efac), it->left());
            alts.insert(normalize(e, vars[0]));
          }
          else
          {
            alts.insert(reBuildCmp(fla, it->left(), it->right()));
          }
        }
        dc[srcRel] = alts;

        for (auto &it : dc[srcRel])
        {
          if (debug > 0)
            outs() << "Data candidate: " << normalize(it, vars[0]) << "\n";
        }
      }

      void printModel(Expr rel)
      {
        outs() << "Model for " << *rel << ":\n";
        for(auto it = models[rel].begin(); it != models[rel].end(); it++)
        {
          for(auto jt = it->begin(); jt != it->end(); jt++)
          {
            outs() << *jt << " ";
          }
          outs() << "\n";
        }
      } 

      void addModel(Expr rel, vector< vector< double> > model) { models[rel] = model; }

      void getDataCands(ExprSet& cands, Expr rel) { cands = dc[rel]; }
  };

}

#endif
