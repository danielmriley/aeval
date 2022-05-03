#ifndef DATALEARNER2__HPP__
#define DATALEARNER2__HPP__

#include <vector>

#include "HornNonlin.hpp"
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

  public:
    DataLearner2(CHCs& r, EZ3& z3, int debug = 0) :
      ruleManager(r), bnd(ruleManager, (debug > 0)), m_efac(r.m_efac) {}

      boost::tribool connect(Expr srcRel = NULL, Expr block = NULL,
        Expr invs = NULL, Expr preCond = NULL)
      {
        // Get data matrix.
        boost::tribool res = bnd.unrollAndExecuteTerm(srcRel, invVars[srcRel], models[srcRel], block, invs, preCond);

        if(res) {
          auto ritr = models[srcRel].rbegin();
          vector<double> e1 = *ritr;
          ritr++;
          vector<double> e2 = *ritr;
          ExprVector ev;

          // make Exprs.
          int n = invVars[srcRel].size();
          for(int i = 0; i < n; i++) {
            for(int j = i + 1; j < n; j++) {
              Expr r1,r2,l1,l2;
              r1 = mkMPZ(cpp_int(e2[j] - e1[j]),m_efac);
              r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]),m_efac));
              l1 = mkMPZ(cpp_int(e2[i] - e1[i]),m_efac);
              l2 = mk<MINUS>(invVars[srcRel][j], mkMPZ(cpp_int(e1[j]),m_efac));
              if(e2[j] - e1[j] == 0) {
                r1 = mkTerm(0,m_efac);
              }
              else {
                r1 = mk<MULT>(r1,r2);
              }
              if(e2[i] - e1[i] == 0) {
                l1 = mkTerm(0,m_efac);
              }
              else {
                l1 = mk<MULT>(l1,l2);
              }
              l1 = mk<EQ>(r1,l1);
              l1 = simplifyArithm(l1);
              l1 = normalize(l1);
              ev.push_back(l1);
              if(debug >= 2) outs() << "  CONNECT: " << *ev.back() << "\n";

            }
          }
          outs() << "\n";
          // ADD or SUBTRACT each equation from another to generate data candidates.
          for(int i = 0; i < ev.size(); i++) {
            dc[srcRel].insert(normalize(ev[i]));
            for(int j = i + 1; j < ev.size(); j++) {
              Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
              Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
              l = mk<EQ>(l,r);
              l = normalize(l);
              dc[srcRel].insert(l);
              if(debug >= 2) outs() << "  CONNECT: " << l << "\n";

              r = mk<PLUS>(ev[i]->right(), ev[j]->right());
              l = mk<PLUS>(ev[i]->left(), ev[j]->left());
              l = mk<EQ>(l,r);
              l = normalize(l);
              dc[srcRel].insert(l);
              if(debug >= 2) outs() << "  CONNECT: " << l << "\n";
            }
          }
        }
        return res;
      }

      ExprSet getDataCands(Expr rel) { return dc[rel]; }
  };

}

#endif
