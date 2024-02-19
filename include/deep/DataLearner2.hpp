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
      dc.clear();
      auto ritr = models[srcRel].rbegin();
      vector<double> e1 = *ritr;
      ritr++;
      vector<double> e2 = *ritr;
      ExprVector ev;

      int n = invVars[srcRel].size();
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

      void getDataCands(ExprSet& cands, Expr rel) { cands = dc[rel]; }
  };

}

#endif
