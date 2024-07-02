#include "deep/MultiBoundSolver.hpp"

using namespace ufo;
using namespace std;

static inline bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return atoi(argv[i+1]);
    }
  }
  return defValue;
}

string getStrValue(const char * opt, string defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return string(argv[i+1]);
    }
  }
  return defValue;
}

vector<string> getCommaSepStrValues(const char * opt, vector<string> defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      stringstream tmpss(argv[i+1]);
      vector<string> values;
      while (tmpss.good()) {
        string tmpstr;
        getline(tmpss, tmpstr, ',');
        values.push_back(tmpstr);
      }
      return values;
    }
  }
  return defValue;
}

int main (int argc, char ** argv)
{
  if (getBoolValue("--help", false, argc, argv) || argc == 1){
    outs () <<   "TODO                                \n";
    return 0;
  }

  int cex = getIntValue("--cex", 0, argc, argv);
  int limit = getIntValue("--limit", 3, argc, argv);
  int str = getIntValue("--stren", 5, argc, argv);
  int debug = getIntValue("--debug", 0, argc, argv);
  bool useDataGrds = !getBoolValue("--data-guards", false, argc, argv);
  bool gj = getBoolValue("--gj", false, argc, argv);  // do Gauss Jordan
  bool dc = getBoolValue("--dc", false, argc, argv);  // do connect
  bool ac = getBoolValue("--ac", false, argc, argv);  // abstract large constants
  bool iwd = getBoolValue("--di", false, argc, argv); // data inference
  bool imp = getBoolValue("--ei", false, argc, argv); // enable second implication
  bool mi = getBoolValue("--mi", false, argc, argv);  // mutate inferred
  bool so = getBoolValue("--so", false, argc, argv);  // separate ops.
  bool tk = getBoolValue("--tk", false, argc, argv);  // check projections from abduction.
  int md = getIntValue("--md", 0, argc, argv);        // mutate results from data.
  bool data2 = getBoolValue("--data2", false, argc, argv);
  bool doPhases = getBoolValue("--phase-data", false, argc, argv);

  std::ifstream infile(argv[argc-1]);
  if (!infile.good())
  {
    outs() << "Could not read file \"" << argv[argc-1] << "\"\n";
    return 0;
  }

  learnMultipleBounds(string(argv[argc - 1]), cex, str, useDataGrds, data2, doPhases, limit,
                      gj, dc, ac, iwd, imp, mi, so, tk, md, debug);

  return 0;
}
