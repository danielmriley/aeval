#ifndef DATALEARNERTOO__HPP__
#define DATALEARNERTOO__HPP__

/*
**  Things to fix:
**    - Decimals in the matrix. Currently this can happen, but we want to stick to whole Ints.
**    - On occasion the wrong move is taken in simplifying the matrix
**      - ex split_45
*/


#include <cmath>
#include <vector>
#include <algorithm>

#include "Horn.hpp"
#include "BndExpl.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;
using namespace boost::multiprecision;

namespace ufo
{
  class DataLearnerToo
  {

    typedef double NUMTYPE; //  boost rational type!
    typedef vector< vector < NUMTYPE > > matrix;

  private:
    CHCs& ruleManager;
    BndExpl bnd;
    ExprFactory &m_efac;
    map<Expr, matrix > basis;
    map<Expr, matrix > models;
    map<Expr, ExprVector> invVars;
    map<Expr, ExprSet> dataCands;
    vector<NUMTYPE> firstRow;
    int debug;

    int numVars;
    int numRows;
    int roundNum = 1000000;

    void connectCands(Expr srcRel)
    {
      //dataCands.clear();
      if(models[srcRel].size() < 2) {
        return;
      } 
      
      auto ritr = models[srcRel].rbegin();
      vector<NUMTYPE> e1 = *ritr;
      ritr++;
      vector<NUMTYPE> e2 = *ritr;
      ExprVector ev;

      int n = invVars[srcRel].size();
      outs() << "n: " << n << "\n";
      // make Exprs.
      /*
      for(int i = 0; i < n-1; i++) {
        for(int j = i + 1; j < n-1; j++) {
          if(e1[i]==e1[j]) {
            Expr r2 = mk<MINUS>(invVars[srcRel][i], invVars[srcRel][j]);
            dataCands[srcRel].insert(mk<EQ>(invVars[srcRel][n-1], r2));
            r2 = mk<MINUS>(invVars[srcRel][j], invVars[srcRel][i]);
            dataCands[srcRel].insert(mk<EQ>(invVars[srcRel][n-1], r2));
          }
        }
      }
      */
      for(int i = 0; i < n; i++) {
        for(int j = i + 1; j < n; j++) {
          Expr r1,r2,l1,l2,l,r;
          r1 = mkMPZ(cpp_int(e2[j] - e1[j]),m_efac);
          outs() << "r1: " << r1 << "\n";
          r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]),m_efac));
          l1 = mkMPZ(cpp_int(e2[i] - e1[i]),m_efac);
          l2 = mk<MINUS>(invVars[srcRel][j], mkMPZ(cpp_int(e1[j]),m_efac));
          if(e2[j] - e1[j] == 0) {
            r1 = mkMPZ(0,m_efac);
          }
          else {
            r1 = mk<MULT>(r1,r2);
          }
          if(e2[i] - e1[i] == 0) {
            l1 = mkMPZ(0,m_efac);
          }
          else {
            l1 = mk<MULT>(l1,l2);
          }
          l = mk<EQ>(r1,l1);
          //l = simplifyArithm(l);
          //l = normalize(l);
          ev.push_back(l);
          if(debug >= 1) outs() << "  CONNECT: " << *ev.back() << "\n";
        }
      }
      if(debug >= 4) outs() << "\n";
      outs() << "ev.size(): " << ev.size() << "\n";
      // ADD or SUBTRACT each equation from another to generate data candidates.
      for(int i = 0; i < ev.size(); i++) {
        dataCands[srcRel].insert(normalize(ev[i]));
        for(int j = i + 1; j < ev.size(); j++) {
          Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
          Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l,r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if(debug >= 1) outs() << "  CONNECT: " << l << "\n";

          r = mk<PLUS>(ev[i]->right(), ev[j]->right());
          l = mk<PLUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l,r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if(debug >= 1) outs() << "  CONNECT: " << l << "\n";
        }
      }
    }

    // Start Gauss Jordan implementation.
    NUMTYPE gcd(NUMTYPE x, NUMTYPE y)
    {
      if(x == 0) return y;
      return gcd(std::fmod(y,x), x);
    }

    NUMTYPE gcd(vector<NUMTYPE> v)
    {
      NUMTYPE res = 0;
      if(!v.empty()) {
        res = v[0];
        for(int i = 1; i < v.size(); i++) {
          res = gcd(v[i],res);
          if(res == 1) return res;
        }
      }
      return res;
    }

    void printMatrix(matrix& A) {
      if(A.empty()) return;
      outs() << "==  MATRIX  ==\n";
      int n = A.size();
      int m = A[0].size();
      for(int i = 0; i < n; i++) {
        for(int j = 0; j < m; j++) {
          if(j > 0) cout << " ";
          cout << A[i][j];
        }
        cout << "\n";
      }
      cout << "\n";
    }

    int findRowToSwap(matrix& A, const int p) {
      int pivotRow = p;
      // NUMTYPE curMax = A[pivotRow][p];
      // for(int i = p + 1; i < numRows; i++) {
      //   if(abs(A[i][p]) > curMax) {
      //     curMax = A[i][p];
      //     pivotRow = i;
      //   }
      // }

      for(int i = p; i < numRows; i++) {
        if(A[i][p] != 0) {
          pivotRow = i;
          break;  
        }
      }

      return pivotRow;
    }

    void tolerance(matrix& A, int i, int j) {
      A[i][j] = std::round(A[i][j] * roundNum) / roundNum;
      if(A[i][j] == 0) A[i][j] = 0.0;
    }

    NUMTYPE tolerance(NUMTYPE d) {
      d = std::round(d * roundNum / roundNum);
      if(d == 0) d = 0;
      return d;
    }

    int pivotIndex(matrix& A, int r) {
      for(int j = 0; j < numVars; j++) {
        if(A[r][j] != 0) return j;
      }
      return -1;
    }

    void invertRow(matrix& A, int r) {
      bool invert = false;

      if(A[r][pivotIndex(A,r)] < 0) {
        invert = true;
      }

      for(int j = 0; invert && j < numVars; j++) {
        A[r][j] = tolerance(A[r][j] * -1);
      }
    }

    void reduceRowsBelow(matrix& A, int r) {
      for(int i = r + 1; i < numRows; i++) {
        int pivot = pivotIndex(A,r);
        if(pivot < 0) continue;
        NUMTYPE divisor = A[i][pivot];
        divisor = tolerance(divisor);
    //    cout << "divisor: " << divisor << "\n";
        if(divisor == 0) continue; // have a condition for a tolerance on the divisor, not just if it is 0.

        for(int j = r; j < numVars; j++) {
          A[i][j] = A[i][j] / divisor;
    //      cout << "A[i][j] = " << A[i][j] <<"\n";
          A[i][j] = A[r][j] - A[r][pivot] * A[i][j];
          A[i][j] = A[i][j] * divisor;
          tolerance(A, i, j);
        }
      }
    }

    bool reduceRowsAbove(matrix& A, int r) {
      NUMTYPE factor = gcd(A[r]);
      if(debug >= 4) cout << "gcd above: " << factor << "\n";
      if(factor == 0.0) return false;

      vector<NUMTYPE> temp = A[r];
      for(int j = 0; j < temp.size(); j++) { // reduce the current column by gcd.
        temp[j] = temp[j] / factor;
        temp[j] = tolerance(temp[j]);
      }
      A[r] = temp;

      if(debug) {
        printMatrix(A);
        cout << endl;
      }
      for(int i = 0; i < r; i++) {
        int pivot = pivotIndex(A,r);
        if(pivot < 0) continue;
        NUMTYPE multiplier;
        if(factor == 1) {
          multiplier = 1;
        }
        else if(factor == -1) {
          multiplier = -1;
        }
        else {
          multiplier = A[i][pivot];
        }
        if(debug) cout << "mult: " << multiplier << "\n";
        for(int j = 0; j < numVars; j++) {
          A[i][j] = A[i][j] - temp[j] * multiplier;
          A[i][j] = tolerance(A[i][j]);
        }
        invertRow(A,i);
      }
      if(debug) {
        printMatrix(A);
        cout << endl;
      }

      return true;
    }

    void simplifyRow(matrix& A, int s, int i, int j) {
      NUMTYPE multiplier = A[i][j];
      for(int k = j; k < numVars; k++) {
        if(debug) cout << A[i][k] << " - " << multiplier << " * " << A[s][k] << "\n";
        A[i][k] = A[i][k] - multiplier * A[s][k];
        A[i][k] = tolerance(A[i][k]);
      }

      int pi = pivotIndex(A,i);
      multiplier = A[i][pi];
      for(int k = 0; k < numVars; k++) {
        A[i][k] = A[i][k] / multiplier;
      }
    }

    void simplify(matrix& A) {
      for(int i = 0; i < numRows; i++) {
        NUMTYPE factor = gcd(A[i]);
        if(debug >= 4) cout << i << ": gcd: " << factor << "\n";
        if(factor == 0.0 || factor == 1 || factor == -1) continue;
        for(int j = 0; j < numVars; j++) {
          A[i][j] = A[i][j] / factor;
          tolerance(A, i, j);
        }
        invertRow(A,i);
      }
      // Below might not be what needs to be checked.
      // next attempt to simplify by using already simplified rows.
      int s = -1;
      for(int i = 0; i < numRows; i++) {
        int pi = pivotIndex(A,i);
        if(pi < 0) continue;
        if(A[i][pi] != 1) {
          for(int j = pi + 1; j < numVars; j++) {
            // find pivot == 1 below non-zero entries.
            if(A[i][j] != 0) {
              for(int k = i + 1; k < numRows; k++) {
                int pk = pivotIndex(A,k);
                if(pk < 0) continue;
                if(A[k][pk] == 1) {
                  s = k;
                  break;
                }
              }
              if(s >= 0) {
                simplifyRow(A,s,i,j);
                break;
              }
              if(debug) printMatrix(A);
            }
            s = -1;
          }
        }
      }
    }

    void finalSimplify(matrix& A) {
      for(int i = 0; i < numRows; i++) {
        int pi = pivotIndex(A,i);
        if(pi < 0) continue;

        int pivotVal = A[i][pi];
        for(int j = pivotIndex(A,i); j < numVars; j++) {
          A[i][j] = A[i][j] / pivotVal;
        }
      }
    }

    int gaussJordanElimination(matrix& A) { // bring matrix to row echelon form.
      for(int r = 0; r < numRows; r++) {
        int pivot = findRowToSwap(A, r);
        if(pivot != r) std::swap(A[pivot], A[r]); // Bring greatest valued pivot up.

        reduceRowsBelow(A, r);
      }

      for(int r = 0; r < numRows; r++) {
        if(!reduceRowsAbove(A, r)) break;
      }

      simplify(A);
      finalSimplify(A);
      if(debug >= 1) outs() << "after finalSimplify\n";
      if(debug >= 1) printMatrix(A);
      return 0;
    }

    int rank(matrix& A) {
      int r = 0;
      for(int i = 0; i < numRows; i++) {
        if(pivotIndex(A, i) > -1) r++;
      }
      return r;
    }

    vector<bool> freeVars;
    void initFreeVars() {
      for(int i = 0; i < numVars; i++) {
        freeVars.push_back(true);
      }
    }

    void determineFreeVars(matrix& A) {
      initFreeVars();
      for(int i = 0; i < numRows; i++) {
        int pivot = pivotIndex(A,i);
        if(pivot >= 0) {
          freeVars[pivot] = false;
        }
      }
    }

    void printFreeVars() {
      bool pr = false;
      cout << "==  FREE VARS  ==\n";
      for(int i = 0; i < freeVars.size(); i++) {
        if(freeVars[i]) {
          if(pr) cout << ", ";
          cout << "x" << i;
          pr = true;
        }
      }
      if(pr) cout << "\n\n";
    }

    void printVector(vector<NUMTYPE> bv) {
      cout << "==  VECTOR  ==\n";
      for(auto v: bv) {
        cout << v << "\n";
      }
      cout << "\n";
    }

    matrix kernelBasis(matrix& A) {
      matrix basis;
      vector<NUMTYPE> basisVector;

      for(int b = 0; b < freeVars.size(); b++) {
        if(!freeVars[b]) continue;
        for(int i = 0; i < numVars; i++) {
          if(b == i) {
            basisVector.push_back(1);
          }
          else {
            basisVector.push_back(0);
          }
        } // fill in zeros for all vector vars.

        // Change var values that are not zero. Namely values from pivot rows and a 1 for the var itself.
        for(int i = 0; i < numRows; i++) {
          int pivot = pivotIndex(A,i);
          if(pivot >= 0 && basisVector[pivot] == 0) {
            NUMTYPE val = A[i][b];
            if(val == 0) basisVector[pivot] = val;
            else basisVector[pivot] = -val;
          }
          else { break; }
        }

        basis.push_back(basisVector);
        if(debug >= 1) printVector(basisVector);
        basisVector.clear();
      }

      return basis;
    }

    matrix findBasis(matrix& A) {
      // identify free vars and extract basis vectors
      determineFreeVars(A);
      if(debug >= 1) printFreeVars();
      matrix basis = kernelBasis(A);
      return basis;
    }

    void printCands(matrix& B) {
      int n = B.size();
      int m = B[0].size();

      if(debug >= 1) {
        cout << "==  CANDS  ==\n";
        for(int i = 0; i < n; i++) {
          for(int j = 0; j < m; j++) {
            cout << B[i][j] << "* x" << j << " + ";
          }
          cout << " = 0\n";
        }
      }
    }

    matrix gaussJordan(Expr srcRel)
    {
      matrix A = models[srcRel];
      gaussJordanElimination(A);
      return A;
    }

    void dotProd(Expr srcRel, vector<double> firstRow) {
      ExprVector terms;
      int n = 0;
      for(int i = 0; i < invVars[srcRel].size(); i++) {
        terms.clear();
        terms.push_back(invVars[srcRel][i]);
        terms.push_back(mkMPZ(-firstRow[i], srcRel->getFactory()));
        dataCands[srcRel].insert(simplifyArithm(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory()))));
        n++;
      }
      if(debug >= 1) outs() << "CANDS FROM DOTPROD: " << n << "\n";
    }

    void candsFromBasis(Expr srcRel) {
      ExprVector terms;
      dotProd(srcRel, firstRow);
      if(basis[srcRel].empty()) {
        if(debug >= 1) outs() << "BASIS was empty\n";
        return;
      }
      int i = 0;
      for(auto& v: basis[srcRel]) {
        terms.clear();
        for(int i = 0; i < v.size(); i++) {
          Expr cnst = mkMPZ(v[i], srcRel->getFactory());
          Expr term = mk<MULT>(cnst, invVars[srcRel][i]);
          terms.push_back(term);
        }
        i++;
        dataCands[srcRel].insert(simplifyArithm(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory()))));
//        dataCands[srcRel].insert(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory())));
      }
      if(debug >= 1) outs() << "CANDS FROM BASIS: " << i << "\n";
    }

    void computeData(Expr srcRel) {
      matrix A = models[srcRel];
      if(A.empty()) return;
      dotProd(srcRel, *A.begin());
      firstRow = *A.begin();
      if(firstRow.empty()) return;

      numVars = A[0].size();
      numRows = A.size();
      A = gaussJordan(srcRel);

      // Now make cands from the reduced matrix.
      basis[srcRel] = findBasis(A);
      if(debug) if(!basis[srcRel].empty()) printMatrix(basis[srcRel]);
      candsFromBasis(srcRel);
      if(debug >= 1) for(auto& c: dataCands[srcRel]) outs() << "Cand from data: " << c << "\n";
    }

  public:
    DataLearnerToo(CHCs& r, EZ3& z3, int _debug = 0) :
      ruleManager(r), bnd(ruleManager, (_debug > 0)), m_efac(r.m_efac), debug(_debug) {}

      boost::tribool connectPhase(Expr srcRel, Expr splitter, Expr invs, bool fwd, ExprSet& constr)
      {
        BndExpl bnd(ruleManager, (debug > 0));
        // Get data matrix.
        if(debug >= 1) outs() << "\n======== CONNECT ========\n";
        //models.clear();
        if(debug >= 1) printMatrix(models[srcRel]);
        //invVars.clear();
        boost::tribool res = bnd.unrollAndExecuteSplitter
          (srcRel, invVars[srcRel], models[srcRel], splitter, invs, fwd, constr);
        if(!res) {
          if(debug >= 1) outs () << "BMC formula unsat\n";
          return res;
        }

        if(models[srcRel].empty()) return false;
        firstRow = models[srcRel][0];
        connectCands(srcRel);
        return res;
      }

      boost::tribool computeData(Expr srcRel, map<Expr, ExprVector>& arrRanges, map<Expr, ExprSet>& constr)
      {
        if(debug >= 1) outs() << "\n======== COMPUTE DATA ========\n";
        models.clear();
        //invVars.clear();
        boost::tribool res = bnd.unrollAndExecuteMultiple(invVars, models, arrRanges, constr);

        if(!res) {
          if(debug >= 1) outs () << "BMC formula unsat\n";
          return res;
        }

        computeData(srcRel);

        return res;
      }

      boost::tribool computeDataPhase(Expr srcRel, Expr splitter, Expr invs, bool fwd, ExprSet& constr)
      {
        if(debug >= 1) outs() << "\n======== COMPUTE DATA PHASE ========\n";
        models.clear();
        //invVars.clear();
        // Get data matrix.
        boost::tribool res = bnd.unrollAndExecuteSplitter
          (srcRel, invVars[srcRel], models[srcRel], splitter, invs, fwd, constr);

        if(!res) {
          if(debug >= 1) outs () << "BMC formula unsat\n";
          return res;
        }
        
        computeData(srcRel);

        return res;
      }

      ExprSet getDataCands(Expr rel) { return dataCands[rel]; }
  }; // End class DataLearnerToo

  // class basisFinder {

  // }; // End class basisFinder

}

#endif
