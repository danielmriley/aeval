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
          int n = invVars[srcRel].size() - 1;
          for(int i = 0; i < n; i++) {
            Expr r1,r2,l1,l2;
            r1 = mkMPZ(cpp_int(e2[n] - e1[n]),m_efac);
            r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]),m_efac));
            l1 = mkMPZ(cpp_int(e2[i] - e1[i]),m_efac);
            l2 = mk<MINUS>(invVars[srcRel][n], mkMPZ(cpp_int(e1[n]),m_efac));
            r1 = mk<MULT>(r1,r2);
            l1 = mk<MULT>(l1,l2);
            ev.push_back(mk<EQ>(simplifyArithm(r1),simplifyArithm(l1)));
          }

          // ADD or SUBTRACT each equation from another to generate data candidates.
          for(int i = 0; i < ev.size(); i++) {
            dc[srcRel].insert(normalize(ev[i]));
            for(int j = i + 1; j < ev.size(); j++) {
              Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
              r = simplifyArithm(r);
              Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
              l = simplifyArithm(l);
              dc[srcRel].insert(normalize(mk<EQ>(l,r)));

            }
          }
        }

        return res;
      }

      ExprSet getDataCands(Expr rel) { return dc[rel]; }
  };

}

#endif
