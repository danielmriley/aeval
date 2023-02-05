#include "deep/BoundSolver.hpp"

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
  int str = getIntValue("--stren", 5, argc, argv);
  int debug = getIntValue("--debug", 0, argc, argv);
  bool useDataGrds = !getBoolValue("--data-guards", false, argc, argv);
  bool data2 = getBoolValue("--data2", false, argc, argv);
  bool doPhases = getBoolValue("--phase-data", false, argc, argv);

  std::ifstream infile(argv[argc-1]);
  if (!infile.good())
  {
    outs() << "Could not read file \"" << argv[argc-1] << "\"\n";
    return 0;
  }

  findBounds(string(argv[argc-1]), cex, str, useDataGrds, data2, doPhases, debug);
  return 0;
}
