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
#include <numeric> // For std::iota
#include <stdexcept> // For exceptions
#include <algorithm>

#include "Horn.hpp"
#include "BndExpl.hpp"
#include "ae/ExprSimpl.hpp"

using namespace std;
using namespace boost;
using namespace boost::multiprecision;

typedef boost::multiprecision::cpp_int CPPINT;
typedef boost::multiprecision::cpp_rational RATIONAL;
typedef vector<vector<RATIONAL>> matrix;
typedef vector<vector<double>> matrix_double; // For linear regression

namespace ufo
{
  class BasisFinder
  {
  private:
    int numVars;
    int numRows;
    matrix A;
    vector<bool> freeVars;
    vector<int> pivotColumns;
    int debug;

    RATIONAL gcd(RATIONAL x, RATIONAL y)
    {
      RATIONAL g = boost::multiprecision::gcd(numerator(x), numerator(y));
      RATIONAL l = boost::multiprecision::lcm(denominator(x), denominator(y));
      return g / l;
    }

    RATIONAL gcd(vector<RATIONAL> v)
    {
      RATIONAL res = 0;
      if (!v.empty())
      {
        res = v[0];
        for (int i = 1; i < v.size(); i++)
        {
          res = gcd(v[i], res);
          if (res == 1)
            return res;
        }
      }
      return res;
    }

    cpp_int lcm(vector<cpp_int> v)
    {
      cpp_int res = 1;
      if (!v.empty())
      {
        res = v[0];
        for (int i = 1; i < v.size(); i++)
        {
          res = boost::multiprecision::lcm(res, v[i]);
        }
      }
      return res;
    }

    int pivotIndex(matrix &A, int r)
    {
      for (int j = 0; j < numVars; j++)
      {
        if (A[r][j] != 0)
          return j;
      }
      return -1;
    }

    void removeZeroRows(matrix &A)
    {
      A.erase(std::remove_if(A.begin(), A.end(), [](const vector<RATIONAL> &row)
                             { return all_of(row.begin(), row.end(), [](RATIONAL val)
                                             { return val == 0; }); }),
              A.end());
      numRows = A.size();
    }

    void reducedRowEchelonForm(matrix &A)
    {
      unsigned int cur_row = 0;
      for (unsigned int cur_col = 0; cur_col < numVars && cur_row < numRows; ++cur_col)
      {
        int pivot_row = cur_row;
        for (int i = cur_row; i < numRows; ++i)
        {
          if (A[i][cur_col] != 0)
          {
            pivot_row = i;
            break;
          }
        }
        if (A[pivot_row][cur_col] == 0)
          continue; // Skip column with no pivot

        if (pivot_row != cur_row)
        {
          std::swap(A[pivot_row], A[cur_row]);
        }

        // Normalize pivot to 1
        RATIONAL divisor = A[cur_row][cur_col];
        for (int j = 0; j < numVars; ++j)
        {
          A[cur_row][j] /= divisor;
        }

        // Eliminate above and below
        for (int i = 0; i < numRows; ++i)
        {
          if (i != cur_row && A[i][cur_col] != 0)
          {
            RATIONAL factor = A[i][cur_col];
            for (int j = 0; j < numVars; ++j)
            {
              A[i][j] -= factor * A[cur_row][j];
            }
          }
        }
        ++cur_row;
      }
    }

    void initFreeVars()
    {
      freeVars.assign(numVars, true);
    }

    void determineFreeVars(matrix &A)
    {
      initFreeVars();
      pivotColumns.clear();
      for (int i = 0; i < numRows; i++)
      {
        int pivot = pivotIndex(A, i);
        if (pivot >= 0)
        {
          freeVars[pivot] = false;
          pivotColumns.push_back(pivot);
        }
      }
    }

    void printFreeVars()
    {
      bool pr = false;
      cout << "==  FREE VARS  ==\n";
      for (int i = 0; i < freeVars.size(); i++)
      {
        if (freeVars[i])
        {
          if (pr)
            cout << ", ";
          cout << "x" << i;
          pr = true;
        }
      }
      if (pr)
        cout << "\n\n";
    }

    void printVector(vector<RATIONAL> bv)
    {
      cout << "==  VECTOR  ==\n";
      for (auto v : bv)
      {
        cout << v << "\n";
      }
      cout << "\n";
    }

    matrix kernelBasis(matrix &A)
    {
      matrix basis;
      vector<RATIONAL> basisVector(numVars, 0);

      for (int b = 0; b < freeVars.size(); b++)
      {
        if (!freeVars[b])
          continue;
        fill(basisVector.begin(), basisVector.end(), 0);
        basisVector[b] = 1;
        for (int i = 0; i < pivotColumns.size(); i++)
        {
          int pivot = pivotColumns[i];
          if (pivot < b)
          {
            RATIONAL val = A[i][b];
            basisVector[pivot] = -val;
          }
        }
        basis.push_back(basisVector);
        if (debug >= 1)
          printVector(basisVector);
      }
      return basis;
    }

    matrix findBasis(matrix &A)
    {
      determineFreeVars(A);
      if (debug >= 1)
      {
        printFreeVars();
        cout << "\n";
      }
      return kernelBasis(A);
    }

    void printCands(matrix &B)
    {
      int n = B.size();
      int m = n > 0 ? B[0].size() : 0;
      cout << "==  CANDS  ==\n";
      for (int i = 0; i < n; i++)
      {
        for (int j = 0; j < m; j++)
        {
          cout << B[i][j] << "* x" << j << " + ";
        }
        cout << " = 0\n";
      }
    }

    void removeFractions(matrix &A)
    {
      if (A.empty())
        return;
      vector<cpp_int> denominators;
      for (const auto &row : A)
      {
        for (const auto &val : row)
        {
          denominators.push_back(denominator(val));
        }
      }
      cpp_int multiplier = lcm(denominators);
      for (auto &row : A)
      {
        for (auto &val : row)
        {
          val *= multiplier;
        }
      }
      if (debug >= 1)
      {
        printMatrix(A);
        cout << "\n";
      }
    }

  public:
    BasisFinder(matrix &_A, int dbg = 0) : A(_A), debug(dbg)
    {
      if (A.empty())
      {
        numVars = numRows = 0;
        return;
      }
      numVars = A[0].size();
      numRows = A.size();
    }

    void printMatrix(matrix &A)
    {
      outs() << "==  MATRIX  ==\n";
      int n = A.size();
      int m = A[0].size();
      for (int i = 0; i < n; i++)
      {
        outs() << "  ";
        for (int j = 0; j < m; j++)
        {
          if (j > 0)
            cout << " ";
          cout << A[i][j];
        }
        cout << "\n";
      }
    }

    matrix findKernelBasis()
    {
      if (A.empty())
        return matrix();
      removeZeroRows(A);
      if (A.empty())
        return matrix(); // All rows were zero
      reducedRowEchelonForm(A);
      removeZeroRows(A);
      if (debug >= 1)
      {
        printMatrix(A);
        cout << "\n";
      }
      matrix basis = findBasis(A);
      if (!basis.empty())
        removeFractions(basis);
      if (debug >= 1)
        printCands(basis);
      return basis;
    }
  }; // End class BasisFinder

  class LinearRegressor
  {
  private:
      vector<RATIONAL> coefficients; // Use RATIONAL
      // Store the mapping of coefficient index to term type/variable indices
      // 0: linear (var_idx), 1: square (var_idx), 2: interaction (var_idx1, var_idx2), 3: intercept
      struct TermInfo {
          int type; // 0: linear, 1: square, 2: interaction, 3: intercept
          int idx1 = -1, idx2 = -1; // Original variable indices (relative to independent vars)

          TermInfo() : type(-1), idx1(-1), idx2(-1) {}

          // Constructor for intercept (type 3)
          TermInfo(int t) : type(t), idx1(-1), idx2(-1) {}

          // Constructor for linear (type 0) and square (type 1)
          TermInfo(int t, int i1) : type(t), idx1(i1), idx2(-1) {}

          // Constructor for interaction (type 2)
          TermInfo(int t, int i1, int i2) : type(t), idx1(i1), idx2(i2) {}
      };
      vector<TermInfo> term_mapping;
      int debug;
      const int STRASSEN_THRESHOLD = 64; // Threshold for switching to naive multiplication

      // --- Matrix Operations for RATIONAL matrices ---

      // Naive matrix multiplication (for base case and smaller matrices)
      matrix multiply_naive(const matrix& A, const matrix& B) {
          if (A.empty() || B.empty()) return {};
          size_t rowsA = A.size();
          size_t colsA = A[0].size();
          size_t rowsB = B.size();
          size_t colsB = B[0].size();

          if (colsA != rowsB) {
              throw std::runtime_error("Matrix dimensions mismatch for naive multiplication");
          }

          matrix C(rowsA, vector<RATIONAL>(colsB, 0));
          for (size_t i = 0; i < rowsA; ++i) {
              for (size_t j = 0; j < colsB; ++j) {
                  for (size_t k = 0; k < colsA; ++k) {
                      C[i][j] += A[i][k] * B[k][j];
                  }
              }
          }
          return C;
      }

      // Matrix addition: C = A + B
      void add(matrix& C, const matrix& A, const matrix& B) {
          size_t n = A.size();
          for (size_t i = 0; i < n; ++i) {
              for (size_t j = 0; j < n; ++j) {
                  C[i][j] = A[i][j] + B[i][j];
              }
          }
      }

      // Matrix subtraction: C = A - B
      void subtract(matrix& C, const matrix& A, const matrix& B) {
          size_t n = A.size();
          for (size_t i = 0; i < n; ++i) {
              for (size_t j = 0; j < n; ++j) {
                  C[i][j] = A[i][j] - B[i][j];
              }
          }
      }

      // Partition matrix M into four sub-matrices A, B, C, D
      void partition(const matrix& M, matrix& A, matrix& B, matrix& C, matrix& D, int half_size) {
          for (int i = 0; i < half_size; ++i) {
              for (int j = 0; j < half_size; ++j) {
                  A[i][j] = M[i][j];
                  B[i][j] = M[i][j + half_size];
                  C[i][j] = M[i + half_size][j];
                  D[i][j] = M[i + half_size][j + half_size];
              }
          }
      }

      // Combine four sub-matrices A, B, C, D into matrix M
      void combine(matrix& M, const matrix& A, const matrix& B, const matrix& C, const matrix& D, int half_size) {
          for (int i = 0; i < half_size; ++i) {
              for (int j = 0; j < half_size; ++j) {
                  M[i][j] = A[i][j];
                  M[i][j + half_size] = B[i][j];
                  M[i + half_size][j] = C[i][j];
                  M[i + half_size][j + half_size] = D[i][j];
              }
          }
      }

       // Recursive Strassen multiplication
      matrix multiply_strassen(const matrix& A, const matrix& B) {
          size_t n = A.size();
          matrix C(n, vector<RATIONAL>(n));

          // Base case
          if (n <= STRASSEN_THRESHOLD) {
              return multiply_naive(A, B);
          }

          int half_size = n / 2;

          // Allocate sub-matrices
          matrix A11(half_size, vector<RATIONAL>(half_size));
          matrix A12(half_size, vector<RATIONAL>(half_size));
          matrix A21(half_size, vector<RATIONAL>(half_size));
          matrix A22(half_size, vector<RATIONAL>(half_size));
          matrix B11(half_size, vector<RATIONAL>(half_size));
          matrix B12(half_size, vector<RATIONAL>(half_size));
          matrix B21(half_size, vector<RATIONAL>(half_size));
          matrix B22(half_size, vector<RATIONAL>(half_size));

          // Partition A and B
          partition(A, A11, A12, A21, A22, half_size);
          partition(B, B11, B12, B21, B22, half_size);

          // Temporary matrices for intermediate results
          matrix temp1(half_size, vector<RATIONAL>(half_size));
          matrix temp2(half_size, vector<RATIONAL>(half_size));

          // Calculate Strassen products P1-P7 recursively
          subtract(temp1, B12, B22); // S1 = B12 - B22
          matrix P1 = multiply_strassen(A11, temp1); // P1 = A11 * S1

          add(temp1, A11, A12); // S2 = A11 + A12
          matrix P2 = multiply_strassen(temp1, B22); // P2 = S2 * B22

          add(temp1, A21, A22); // S3 = A21 + A22
          matrix P3 = multiply_strassen(temp1, B11); // P3 = S3 * B11

          subtract(temp1, B21, B11); // S4 = B21 - B11
          matrix P4 = multiply_strassen(A22, temp1); // P4 = A22 * S4

          add(temp1, A11, A22); // S5 = A11 + A22
          add(temp2, B11, B22); // S6 = B11 + B22
          matrix P5 = multiply_strassen(temp1, temp2); // P5 = S5 * S6

          subtract(temp1, A12, A22); // S7 = A12 - A22
          add(temp2, B21, B22);      // S8 = B21 + B22
          matrix P6 = multiply_strassen(temp1, temp2); // P6 = S7 * S8

          subtract(temp1, A11, A21); // S9 = A11 - A21
          add(temp2, B11, B12);      // S10 = B11 + B12
          matrix P7 = multiply_strassen(temp1, temp2); // P7 = S9 * S10

          // Calculate result quadrants C11, C12, C21, C22
          matrix C11(half_size, vector<RATIONAL>(half_size));
          matrix C12(half_size, vector<RATIONAL>(half_size));
          matrix C21(half_size, vector<RATIONAL>(half_size));
          matrix C22(half_size, vector<RATIONAL>(half_size));

          // C11 = P5 + P4 - P2 + P6
          add(temp1, P5, P4);
          subtract(temp2, temp1, P2);
          add(C11, temp2, P6);

          // C12 = P1 + P2
          add(C12, P1, P2);

          // C21 = P3 + P4
          add(C21, P3, P4);

          // C22 = P5 + P1 - P3 - P7
          add(temp1, P5, P1);
          subtract(temp2, temp1, P3);
          subtract(C22, temp2, P7);

          // Combine result quadrants into C
          combine(C, C11, C12, C21, C22, half_size);

          return C;
      }

      // Helper to find next power of 2
      int nextPowerOf2(int n) {
          int power = 1;
          while (power < n) {
              power *= 2;
          }
          return power;
      }

      // Pad matrix with zeros
      matrix pad(const matrix& M, int new_size) {
          size_t rows = M.size();
          size_t cols = rows > 0 ? M[0].size() : 0;
          matrix Padded(new_size, vector<RATIONAL>(new_size, 0));
          for (size_t i = 0; i < rows; ++i) {
              for (size_t j = 0; j < cols; ++j) {
                  Padded[i][j] = M[i][j];
              }
          }
          return Padded;
      }

      // Unpad matrix
      matrix unpad(const matrix& M, int orig_rows, int orig_cols) {
          matrix Unpadded(orig_rows, vector<RATIONAL>(orig_cols));
          for (int i = 0; i < orig_rows; ++i) {
              for (int j = 0; j < orig_cols; ++j) {
                  Unpadded[i][j] = M[i][j];
              }
          }
          return Unpadded;
      }


      matrix transpose(const matrix& A) { // Input/Output is matrix (RATIONAL)
          if (A.empty()) return {};
          size_t rows = A.size();
          size_t cols = A[0].size();
          matrix T(cols, vector<RATIONAL>(rows)); // Use RATIONAL
          for (size_t i = 0; i < rows; ++i) {
              for (size_t j = 0; j < cols; ++j) {
                  T[j][i] = A[i][j];
              }
          }
          return T;
      }

      // Main multiply function using Strassen
      matrix multiply(const matrix& A, const matrix& B) {
           if (A.empty() || B.empty()) return {};
           size_t rowsA = A.size();
           size_t colsA = A[0].size();
           size_t rowsB = B.size();
           size_t colsB = B[0].size();

           if (colsA != rowsB) {
               throw std::runtime_error("Matrix dimensions mismatch for multiplication");
           }

           // For Strassen, we ideally work with square matrices.
           // Find max dimension and pad to next power of 2.
           int max_dim = std::max({rowsA, colsA, rowsB, colsB});
           int padded_size = nextPowerOf2(max_dim);

           matrix APadded = pad(A, padded_size);
           matrix BPadded = pad(B, padded_size);

           matrix CPadded = multiply_strassen(APadded, BPadded);

           // Unpad the result to the original expected size (rowsA x colsB)
           return unpad(CPadded, rowsA, colsB);
      }


      // Inversion using Gaussian elimination with RATIONAL
      matrix invert(matrix A) { // Input/Output is matrix (RATIONAL)
          size_t n = A.size();
          if (n == 0 || A[0].size() != n) {
              throw std::runtime_error("Matrix must be square for inversion");
          }

          matrix I(n, vector<RATIONAL>(n, 0)); // Use RATIONAL
          for (size_t i = 0; i < n; ++i) I[i][i] = 1;

          for (size_t i = 0; i < n; ++i) {
              // Find pivot (row with largest absolute value in current column)
              size_t pivot = i;
              for (size_t j = i + 1; j < n; ++j) {
                  // Using abs() for rationals
                  if (boost::multiprecision::abs(A[j][i]) > boost::multiprecision::abs(A[pivot][i])) {
                      pivot = j;
                  }
              }
              std::swap(A[i], A[pivot]);
              std::swap(I[i], I[pivot]);

              // Check for singularity (pivot is zero)
              if (A[i][i] == 0) {
                  return {}; // Return empty matrix indicating singular
              }

              // Normalize row i (make pivot 1)
              RATIONAL div = A[i][i]; // Use RATIONAL
              for (size_t j = 0; j < n; ++j) {
                  A[i][j] /= div;
                  I[i][j] /= div;
              }

              // Eliminate other rows
              for (size_t j = 0; j < n; ++j) {
                  if (i != j) {
                      RATIONAL mult = A[j][i]; // Use RATIONAL
                      if (mult == 0) continue; // Skip if element is already zero
                      for (size_t k = 0; k < n; ++k) {
                          A[j][k] -= mult * A[i][k];
                          I[j][k] -= mult * I[i][k];
                      }
                  }
              }
          }
          return I;
      }

      // Print RATIONAL matrix
      void printMatrixR(const matrix& A, const string& label = "Matrix") {
          if (debug < 2) return;
          outs() << "== " << label << " ==\n";
          if (A.empty()) {
              outs() << "  (empty)\n";
              return;
          }
          int n = A.size();
          int m = A[0].size();
          for (int i = 0; i < n; i++) {
              outs() << "  ";
              for (int j = 0; j < m; j++) {
                  // Potentially simplify output for readability if needed
                  outs() << A[i][j] << " ";
              }
              outs() << "\n";
          }
      }

  public:
      LinearRegressor(int dbg = 0) : debug(dbg) {}

      // Performs linear regression: y = X * beta, potentially adding quadratic features
      // models_rational: rows are data points, columns are variables (using RATIONAL)
      // y_col_idx: index of the dependent variable column
      // add_quadratic_terms: flag to enable adding x_i^2 and x_i*x_j terms
      // Returns true on success, false on failure
      bool performRegression(const matrix& models_rational, int y_col_idx, bool add_quadratic_terms = true) { // Added add_quadratic_terms flag
          coefficients.clear();
          term_mapping.clear();
          if (models_rational.empty()) return false;

          size_t num_points = models_rational.size();
          size_t num_vars_total = models_rational[0].size();

          if (y_col_idx < 0 || y_col_idx >= num_vars_total) {
              outs() << "Error: Invalid dependent variable index.\n";
              return false;
          }

          size_t num_independent_vars = num_vars_total - 1;
          if (num_independent_vars == 0) {
               if (debug >= 1) outs() << "Warning: No independent variables for regression.\n";
               return false; // Need at least one independent variable
          }

          // --- Prepare initial X matrix (independent vars only) and y vector ---
          matrix X_orig(num_points, vector<RATIONAL>(num_independent_vars));
          matrix y(num_points, vector<RATIONAL>(1));
          vector<int> independent_var_indices; // Store original indices of independent vars

          for (size_t i = 0; i < num_points; ++i) {
              y[i][0] = models_rational[i][y_col_idx];
              int current_x_col = 0;
              for (size_t j = 0; j < num_vars_total; ++j) {
                  if (j != y_col_idx) {
                      X_orig[i][current_x_col++] = models_rational[i][j];
                      if (i == 0) independent_var_indices.push_back(j); // Store indices on first pass
                  }
              }
          }

          // --- Augment X matrix with non-linear terms and intercept ---
          size_t num_augmented_features = 0;
          vector<vector<RATIONAL>> X_augmented_data(num_points); // Build row by row

          // 1. Add Linear Terms
          for(size_t j=0; j < num_independent_vars; ++j) {
              term_mapping.push_back(TermInfo(0, (int)j)); // Use constructor
              num_augmented_features++;
          }

          // 2. Add Quadratic Terms (if enabled)
          if (add_quadratic_terms) {
              // 2a. Squared terms (x_i^2)
              for(size_t j=0; j < num_independent_vars; ++j) {
                  term_mapping.push_back(TermInfo(1, (int)j)); // Use constructor
                  num_augmented_features++;
              }
              // 2b. Interaction terms (x_i * x_j, i < j)
              for(size_t j=0; j < num_independent_vars; ++j) {
                  for (size_t k = j + 1; k < num_independent_vars; ++k) {
                      term_mapping.push_back(TermInfo(2, (int)j, (int)k)); // Use constructor
                      num_augmented_features++;
                  }
              }
          }

          // 3. Add Intercept Term placeholder
          term_mapping.push_back(TermInfo(3)); // Use constructor
          num_augmented_features++;

          // Check if enough data points for the number of features
          if (num_points <= num_augmented_features -1) { // Need points > features
               if (debug >= 1) outs() << "Warning: Not enough data points (" << num_points
                                      << ") for regression with " << num_augmented_features
                                      << " features (including intercept). Need > " << num_augmented_features -1 << ".\n";
              return false;
          }


          // Populate the augmented matrix data
          for (size_t i = 0; i < num_points; ++i) {
              X_augmented_data[i].resize(num_augmented_features);
              int current_aug_col = 0;

              // 1. Linear terms
              for(size_t j=0; j < num_independent_vars; ++j) {
                  X_augmented_data[i][current_aug_col++] = X_orig[i][j];
              }

              // 2. Quadratic terms (if enabled)
              if (add_quadratic_terms) {
                  // 2a. Squared terms
                  for(size_t j=0; j < num_independent_vars; ++j) {
                      X_augmented_data[i][current_aug_col++] = X_orig[i][j] * X_orig[i][j];
                  }
                  // 2b. Interaction terms
                  for(size_t j=0; j < num_independent_vars; ++j) {
                      for (size_t k = j + 1; k < num_independent_vars; ++k) {
                          X_augmented_data[i][current_aug_col++] = X_orig[i][j] * X_orig[i][k];
                      }
                  }
              }

              // 3. Intercept term
              X_augmented_data[i][current_aug_col++] = 1; // RATIONAL 1
          }

          // Create the final augmented matrix object
          matrix X_augmented = X_augmented_data;


          if (debug >= 2) {
              printMatrixR(X_augmented, "X Augmented Matrix (Rational)");
              printMatrixR(y, "y Vector (Rational)");
          }

          matrix Xt = transpose(X_augmented); // Use augmented matrix
          printMatrixR(Xt, "X_Augmented Transpose (Rational)");

          matrix XtX = multiply(Xt, X_augmented); // Use augmented matrix
          printMatrixR(XtX, "X_Augmented_Transpose * X_Augmented (Rational)");

          matrix XtX_inv = invert(XtX); // Use RATIONAL inversion
            if (XtX_inv.empty()) {
                if (debug >= 1) outs() << "Warning: (X_Augmented^T * X_Augmented) matrix is singular, cannot perform regression.\n";
                return false;
            }
          printMatrixR(XtX_inv, "(X_Augmented_Transpose * X_Augmented)^-1 (Rational)");

          matrix XtY = multiply(Xt, y); // Uses Strassen potentially
          printMatrixR(XtY, "X_Augmented_Transpose * y (Rational)");

          matrix beta_matrix = multiply(XtX_inv, XtY); // Uses Strassen potentially
          printMatrixR(beta_matrix, "Beta Coefficients Matrix (Rational)");

          // Extract coefficients
          coefficients.resize(beta_matrix.size());
          for(size_t i = 0; i < beta_matrix.size(); ++i) {
              coefficients[i] = beta_matrix[i][0]; // Store RATIONAL coefficients
          }

          if (debug >= 1) {
              outs() << "Regression Coefficients (Beta - Rational): [";
              for(size_t i=0; i < coefficients.size(); ++i) {
                  outs() << coefficients[i] << (i == coefficients.size() - 1 ? "" : ", ");
              }
              outs() << "]\n";
              if (debug >= 2) {
                  outs() << "Coefficient Term Mapping:\n";
                  for(size_t i=0; i < coefficients.size(); ++i) {
                      outs() << "  coeff[" << i << "] (" << coefficients[i] << "): ";
                      const auto& term = term_mapping[i];
                      if (term.type == 0) outs() << "linear(x" << term.idx1 << ")\n";
                      else if (term.type == 1) outs() << "square(x" << term.idx1 << "^2)\n";
                      else if (term.type == 2) outs() << "interaction(x" << term.idx1 << "*x" << term.idx2 << ")\n";
                      else if (term.type == 3) outs() << "intercept\n";
                  }
              }
          }
          return true;

      }

      // Constructs an expression like y = c0*x0 + c1*x1 + ... + c_k*x0^2 + c_{k+1}*x0*x1 + ... + intercept using RATIONAL
      Expr getRegressionExpr(const ExprVector& invVars, int y_col_idx, ExprFactory& efac) {
          if (coefficients.empty() || term_mapping.empty() || coefficients.size() != term_mapping.size()) {
              return mk<TRUE>(efac);
          }

          size_t num_vars_total = invVars.size();
          if (y_col_idx < 0 || y_col_idx >= num_vars_total) return mk<TRUE>(efac);

          Expr y_var = invVars[y_col_idx];
          ExprVector rhs_terms;

          // Map independent variable indices from original list (invVars) to the 0-based indices used in regression (X_orig)
          vector<Expr> independent_vars_exprs;
          vector<int> independent_var_orig_indices;
          for(size_t i = 0; i < num_vars_total; ++i) {
              if (i != y_col_idx) {
                  independent_vars_exprs.push_back(invVars[i]);
                  independent_var_orig_indices.push_back(i);
              }
          }

          // Build RHS terms based on coefficients and term_mapping
          for (size_t coeff_idx = 0; coeff_idx < coefficients.size(); ++coeff_idx) {
              RATIONAL coeff_rat = coefficients[coeff_idx];
              if (numerator(coeff_rat) == 0) continue; // Skip zero coefficients

              Expr coeff_expr = mkMPZ(numerator(coeff_rat), denominator(coeff_rat), efac);
              const auto& term = term_mapping[coeff_idx];
              Expr term_expr;

              if (term.type == 0) { // Linear term: coeff * x_i
                  term_expr = mk<MULT>(coeff_expr, independent_vars_exprs[term.idx1]);
              } else if (term.type == 1) { // Squared term: coeff * x_i^2
                  Expr var = independent_vars_exprs[term.idx1];
                  term_expr = mk<MULT>(coeff_expr, mk<MULT>(var, var));
              } else if (term.type == 2) { // Interaction term: coeff * x_i * x_j
                  Expr var1 = independent_vars_exprs[term.idx1];
                  Expr var2 = independent_vars_exprs[term.idx2];
                  term_expr = mk<MULT>(coeff_expr, mk<MULT>(var1, var2));
              } else if (term.type == 3) { // Intercept term: coeff
                  term_expr = coeff_expr;
              }

              if (term_expr) {
                  rhs_terms.push_back(term_expr);
              }
          }


          Expr rhs_expr = mkplus(rhs_terms, efac);
          // Handle case where all coefficients were zero (or only intercept was zero)
          if (!rhs_expr) rhs_expr = mkMPZ(0, efac);

          Expr regression_eq = mk<EQ>(y_var, rhs_expr);

          Expr norm_expr = normalize(regression_eq);

          if (debug >= 1) {
              outs() << "Generated Regression Equation (Rational, potentially non-linear): " << *norm_expr << "\n";
          }

          return norm_expr;
      }
  }; // End class LinearRegressor

  class DataLearner2
  {
  private:
    CHCs &ruleManager;
    BndExpl bnd;
    ExprFactory &m_efac;
    map<Expr, matrix> basis;
    map<Expr, vector<vector<double>>> models; // Changed to matrix_double
    map<Expr, ExprVector> invVars;
    map<Expr, ExprSet> dataCands;
    vector<RATIONAL> firstRow;
    int debug;

    void connectCands(Expr srcRel)
    {
      // dataCands.clear();
      if(debug >= 3) 
      {
        matrix A = doubleToRational(models[srcRel]);
        BasisFinder bf(A, debug);
        bf.printMatrix(A);
      }

      if (models[srcRel].size() < 2)
      {
        return;
      }

      auto ritr = models[srcRel].rbegin();
      vector<double> e1 = *ritr;
      ritr++;
      vector<double> e2 = *ritr;
      ExprVector ev;

      int n = invVars[srcRel].size();
      // outs() << "n: " << n << "\n";
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
      for (int i = 0; i < n; i++)
      {
        for (int j = i + 1; j < n; j++)
        {
          Expr r1, r2, l1, l2, l, r;
          r1 = mkMPZ(cpp_int(e2[j] - e1[j]), m_efac);
          // outs() << "r1: " << r1 << "\n";
          r2 = mk<MINUS>(invVars[srcRel][i], mkMPZ(cpp_int(e1[i]), m_efac));
          l1 = mkMPZ(cpp_int(e2[i] - e1[i]), m_efac);
          l2 = mk<MINUS>(invVars[srcRel][j], mkMPZ(cpp_int(e1[j]), m_efac));
          if (e2[j] - e1[j] == 0)
          {
            r1 = mkMPZ(0, m_efac);
          }
          else
          {
            r1 = mk<MULT>(r1, r2);
          }
          if (e2[i] - e1[i] == 0)
          {
            l1 = mkMPZ(0, m_efac);
          }
          else
          {
            l1 = mk<MULT>(l1, l2);
          }
          l = mk<EQ>(r1, l1);
          // l = simplifyArithm(l);
          // l = normalize(l);
          ev.push_back(l);
          if (debug >= 1)
            outs() << "  CONNECT: " << *ev.back() << "\n";
        }
      }
      if (debug >= 1)
        outs() << "\n";
      // ADD or SUBTRACT each equation from another to generate data candidates.
      for (int i = 0; i < ev.size(); i++)
      {
        dataCands[srcRel].insert(normalize(ev[i]));
        for (int j = i + 1; j < ev.size(); j++)
        {
          Expr r = mk<MINUS>(ev[i]->right(), ev[j]->right());
          Expr l = mk<MINUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l, r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if (debug >= 1)
            outs() << "  CONNECT(-): " << l << "\n";

          r = mk<PLUS>(ev[i]->right(), ev[j]->right());
          l = mk<PLUS>(ev[i]->left(), ev[j]->left());
          l = mk<EQ>(l, r);
          l = normalize(l);
          dataCands[srcRel].insert(l);
          if (debug >= 1)
            outs() << "  CONNECT(+): " << l << "\n";
        }
      }
    }

    Expr dotProduct(Expr srcRel, vector<RATIONAL> row, bool addToDataCands = true)
    {
      ExprVector terms;
      ExprSet cands;
      int n = 0;
      for (int i = 0; i < invVars[srcRel].size(); i++)
      {
        terms.clear();
        terms.push_back(invVars[srcRel][i]);
        terms.push_back(mkMPZ(-numerator(row[i+1]), srcRel->getFactory()));
        cands.insert(simplifyArithm(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory()))));
        n++;
      }
      if (debug >= 3)
      {
        outs() << "CANDS FROM dotProduct: " << n << "\n";
        for(auto &c : cands) {
          outs() << "  " << *c << "\n";
        }
      }

      if (addToDataCands) dataCands[srcRel].insert(cands.begin(), cands.end());

      return conjoin(cands, srcRel->getFactory());
    }

    void candsFromBasis(Expr srcRel)
    {
      ExprVector terms;
      ExprSet cands;
      if (basis[srcRel].empty())
      {
        if (debug >= 1)
          outs() << "BASIS was empty\n";
        return;
      }
      int cnt = 0;
      for (auto &v : basis[srcRel])
      {
        terms.clear();
        for (int i = 1; i < v.size(); i++)
        {
          Expr cnst = mkMPZ(numerator(v[i]), srcRel->getFactory());
          Expr term = mk<MULT>(cnst, invVars[srcRel][i - 1]);
          terms.push_back(term);
        }
        cnt++;
        Expr cnst = mkMPZ(-numerator(v[0]), srcRel->getFactory());
        Expr datcand = mk<EQ>(mkplus(terms, srcRel->getFactory()), cnst);
        cands.insert(normalize(datcand));
        // dataCands[srcRel].insert(mk<EQ>(mkplus(terms, srcRel->getFactory()), mkMPZ(0, srcRel->getFactory())));
      }
      if (debug >= 1)
        outs() << "CANDS FROM BASIS: " << cnt << "\n";
      if(debug >= 2) {
        for(auto &c : cands) {
          outs() << "  " << *c << "\n";
        }
      }
      dataCands[srcRel].insert(cands.begin(), cands.end());
    }

    matrix doubleToRational(const matrix_double& models_double) // Updated signature
    {
      matrix A;
      if (models_double.empty()) return A;
      for (int i = 0; i < models_double.size(); i++)
      {
        vector<RATIONAL> temp;
        temp.push_back(static_cast<RATIONAL>(1));
        for (int j = 0; j < models_double[0].size(); j++)
        {
          // Handle potential precision issues or provide better conversion if needed
          temp.push_back(static_cast<RATIONAL>(models_double[i][j]));
        }
        A.push_back(temp);
      }
      return A;
    }

    void computeData(Expr srcRel)
    {
      // Convert double models to rational for BasisFinder (includes leading 1)
      matrix A_basis = doubleToRational(models[srcRel]);

      if (A_basis.empty())
        return;
      BasisFinder bf(A_basis, debug);

      // Keep track of the first row if needed (already rational here)
      firstRow = *A_basis.begin();
      // auto row = firstRow; // This seems unused later, maybe remove?

      // if (row.empty()) // Check based on A_basis instead
      //   return;

      // dotProduct(srcRel, row); // This seems to use only the first row, purpose unclear?

      // Now make cands from the reduced matrix.
      basis[srcRel] = bf.findKernelBasis(); // bf works on A_basis
      candsFromBasis(srcRel); // Uses basis[srcRel]
    }

  public:
    DataLearner2(CHCs &r, EZ3 &z3, int _debug = 0) : ruleManager(r), bnd(ruleManager, (_debug > 0)), m_efac(r.m_efac), debug(_debug) {}

    // DR: unrollAndExecuteTermPhase is not used in this version of BndExpl. To be added later.
    // boost::tribool connectPhase(Expr src, Expr dst, int k = 1,
    //                 Expr srcRel = NULL, Expr block = NULL, Expr invs = NULL,
    //                 Expr preCond = NULL, bool doGJ = false, bool doConnect = false,
    //                 bool doRegression = false) // Added doRegression flag
    //   {
    //     // Get data matrix.
    //     // Refactor so that the matrix isn't built over and over.
    //     // seperate the BndExpl from DL2 so that DL2 is provided with the matrix rather
    //     // than creating it each time itself.
    //     boost::tribool res = bnd.unrollAndExecuteTermPhase
    //       (src, dst, srcRel, invVars[srcRel], models[srcRel], block, k);

    //   if (!res)
    //   {
    //     if (debug >= 1)
    //       outs() << "BMC formula unsat\n";
    //     return res;
    //   }

    //   if (models[srcRel].empty()) return false;

    //   // firstRow = models[srcRel][0];
    //   if(doConnect) connectCands(srcRel);
    //   if(doGJ) computeData(srcRel); // Gauss Jordan Elimination method.
    //   if(doRegression) computeLinearRegressionCands(srcRel); // Linear Regression method

    //   return res;
    // }

    void computeLinearRegressionCands(Expr srcRel) {
        if (debug >= 1) outs() << "\n======== COMPUTE LINEAR REGRESSION (RATIONAL, QUADRATIC ENABLED) ========\n";
        if (models.find(srcRel) == models.end() || invVars.find(srcRel) == invVars.end()) {
            if (debug >= 1) outs() << "No model or variables found for " << *srcRel << "\n";
            return;
        }

        const matrix_double& model_data_double = models[srcRel];
        const ExprVector& variables = invVars[srcRel];

        if (model_data_double.empty() || variables.empty()) {
             if (debug >= 1) outs() << "Model data or variables are empty for " << *srcRel << "\n";
            return;
        }

        size_t num_vars = variables.size();
        if (num_vars < 2) {
             if (debug >= 1) outs() << "Need at least 2 variables for linear regression.\n";
            return; // Need at least one independent and one dependent variable
        }

        // Convert model data from double to rational for the regressor
        matrix model_data_rational = doubleToRational(model_data_double);

        LinearRegressor regressor(debug);

        // Try regressing each variable against the others using rational data
        for (size_t y_idx = 0; y_idx < num_vars; ++y_idx) {
            if (debug >= 1) outs() << "--- Regressing on variable: " << *variables[y_idx] << " (Rational, Quadratic) ---\n";
            // Pass the rational matrix to performRegression, enable quadratic terms (default)
            bool success = regressor.performRegression(model_data_rational, y_idx, true); // Pass true for quadratic
            if (success) {
                Expr cand_expr = regressor.getRegressionExpr(variables, y_idx, m_efac);
                if (!isOpX<TRUE>(cand_expr)) { // Avoid adding trivial TRUE
                   dataCands[srcRel].insert(cand_expr);
                   if (debug >= 1) outs() << "Added regression candidate: " << *cand_expr << "\n";
                }
            } else {
                 if (debug >= 1) outs() << "Regression failed for variable " << *variables[y_idx] << "\n";
            }
        }
         if (debug >= 1) outs() << "=======================================================================\n";
    }


    ExprVector exprForRows(Expr srcRel)
    {
      if(models[srcRel].empty()) return ExprVector();

      matrix A = doubleToRational(models[srcRel]);

      ExprVector rowsExpr;
      for(auto &row : A) 
      {
        rowsExpr.push_back(dotProduct(srcRel, row, false));
      }

      return rowsExpr;
    }

    boost::tribool computeData(Expr srcRel, map<Expr, ExprVector> &arrRanges, map<Expr, ExprSet> &constr, 
                               bool doGJ = true, bool doRegression = false, bool doConnect = false)
    {
      if (debug >= 1)
        outs() << "\n======== COMPUTE DATA ========\n";
      models.clear();
      // invVars.clear();
      boost::tribool res = bnd.unrollAndExecuteMultiple(invVars, models, arrRanges, constr);

      if (!res)
      {
        if (debug >= 1)
          outs() << "BMC formula unsat\n";
        return res;
      }

      if(doGJ) computeData(srcRel);
      if(doRegression) computeLinearRegressionCands(srcRel); // Linear Regression method
      if(doConnect) connectCands(srcRel); // Connect phase

      return res;
    }

    boost::tribool computeDataPhase(Expr srcRel, Expr splitter, Expr invs, bool fwd, ExprSet &constr,
                                    bool doGJ = true, bool doRegression = false, bool doConnect = false)
    {
      if (debug >= 1)
        outs() << "\n======== COMPUTE DATA PHASE ========\n";
      models.clear();
      // invVars.clear();
      //  Get data matrix.
      boost::tribool res = bnd.unrollAndExecuteSplitter(srcRel, invVars[srcRel], models[srcRel], splitter, invs, fwd, constr);

      if (!res)
      {
        if (debug >= 1)
          outs() << "BMC formula unsat\n";
        return res;
      }

      if(doGJ) computeData(srcRel);
      if(doRegression) computeLinearRegressionCands(srcRel); // Linear Regression method
      if(doConnect) connectCands(srcRel); // Connect phase

      return res;
    }

    void getDataCands(ExprSet& cands, Expr rel) { cands = dataCands[rel]; }

  }; // End class DataLearner2

}

#endif