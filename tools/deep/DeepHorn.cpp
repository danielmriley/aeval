#include "deep/RndLearnerV4.hpp"
#include "deep/BitHorn.hpp"
#include "deep/BndExpl.hpp"
#include <chrono>

using namespace ufo;
using namespace std;

bool getBoolValue(const char * opt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], opt) == 0) return true;
  }
  return defValue;
}

// Get boolean with support for both --flag (true) and --no-flag (false) syntax
bool getBoolValueWithNegation(const char * posOpt, const char * negOpt, bool defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc; i++)
  {
    if (strcmp(argv[i], posOpt) == 0) return true;
    if (strcmp(argv[i], negOpt) == 0) return false;
  }
  return defValue;
}

char * getStrValue(const char * opt, char * defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      return argv[i+1];
    }
  }
  return defValue;
}

int getIntValue(const char * opt, int defValue, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      char* p;
      int num = strtol(argv[i+1], &p, 10);
      if (*p) return 1;      // if used w/o arg, return boolean
      else return num;
    }
  }
  return defValue;
}

void getStrValues(const char * opt, vector<string> & values, int argc, char ** argv)
{
  for (int i = 1; i < argc-1; i++)
  {
    if (strcmp(argv[i], opt) == 0)
    {
      values.push_back(string(argv[i+1]));
    }
  }
}

int main (int argc, char ** argv)
{
  const char *OPT_HELP = "--help";
  const char *OPT_V1 = "--v1";
  const char *OPT_V2 = "--v2";
  const char *OPT_V3 = "--v3";
  const char *OPT_V4 = "--v4";
  const char *OPT_V5 = "--bv";
  const char *OPT_MAX_ATTEMPTS = "--attempts";
  const char *OPT_TO = "--to";
  const char *OPT_K_IND = "--kind";
  const char *OPT_ITP = "--itp";
  const char *OPT_BATCH = "--batch";
  const char *OPT_RETRY = "--retry";
  const char *OPT_ELIM = "--skip-elim";
  const char *OPT_ARITHM = "--skip-arithm";
  const char *OPT_SEED = "--skip-syntax";
  const char *OPT_GET_FREQS = "--freqs";
  const char *OPT_ADD_EPSILON = "--eps";
  const char *OPT_AGG_PRUNING = "--aggp";
  const char *OPT_DATA_LEARNING = "--data";
  const char *OPT_MUT = "--mut";
  const char *OPT_PROP = "--prop";
  const char *OPT_DISJ = "--disj";
  const char *OPT_D1 = "--all-mbp";
  const char *OPT_D2 = "--phase-prop";
  const char *OPT_D3 = "--phase-data";
  const char *OPT_D4 = "--stren-mbp";
  const char *OPT_D5 = "--fwd";
  const char *OPT_D6 = "--prune";
  const char *OPT_REC = "--re";
  const char *OPT_MBP = "--eqs-mbp";
  const char *OPT_SER = "--serialize";
  const char *OPT_SERTRANS = "--serialize-translation";
  const char *OPT_LIA2BV = "--lia2bv";
  const char *OPT_HORN = "--horn";
  const char *OPT_SYGUS = "--sygus";
  const char *OPT_SYGUS_TR = "--sygus-tr";
  const char *OPT_SYGUS_FULL = "--sygus-full";
  const char *OPT_SYGUS_FULL_BOUND = "--sygus-full-bound";
  const char *OPT_SYGUS_SPARSE = "--sygus-sparse";
  const char *OPT_SYGUS_POINTS = "--sygus-points";
  const char *OPT_SYGUS_BITWIDTH = "--sygus-bitwidth";
  const char *OPT_SYGUS_RUN = "--sygus-run";
  const char *OPT_SYGUS_VALIDATE = "--sygus-validate";
  const char *OPT_SYGUS_CCEX = "--sygus-ccex";
  const char *OPT_SYGUS_MBP = "--sygus-mbp";
  const char *OPT_NO_SYGUS_MBP = "--no-sygus-mbp";
  const char *OPT_SYGUS_INVARIANTS = "--sygus-invariants";
  const char *OPT_NO_SYGUS_INVARIANTS = "--no-sygus-invariants";
  const char *OPT_DEBUG = "--debug";
  if (getBoolValue(OPT_HELP, false, argc, argv) || argc == 1){
    outs () <<
        "* * *                                 FreqHorn v.0.6 - Copyright (C) 2021                                 * * *\n" <<
        "                                           Grigory Fedyukovich et al                                      \n\n" <<
        "Usage:                          Purpose:\n" <<
        " freqhorn [--help]               show help\n" <<
        " freqhorn [options] <file.smt2>  discover invariants for a system of constrained Horn clauses\n\n" <<
        "Options:\n" <<
        " " << OPT_V1 << "                            original version (one-by-one sampling)\n"
        " " << OPT_V2 << "                            optimized version for transition systems (+ bootstrapping)\n"
        " " << OPT_V3 << "                            optimized version (+ bootstrapping, propagation, and data candidates)\n"
        " " << OPT_V4 << " (default)                  optimized version (+ multi-phase loops)\n"
        " " << OPT_V5 << "                            optimized version (+ bit vectors)\n"
        " " << OPT_GET_FREQS << "                         calculate frequency distributions and sample from them\n" <<
        " " << OPT_AGG_PRUNING << "                          prioritize and prune the search space aggressively\n" <<
        "                                 (if not specified, sample from uniform distributions)\n" <<
        " " << OPT_MAX_ATTEMPTS << " <N>                  maximal number of candidates to sample and check\n" <<
        " " << OPT_ELIM << "                     do not minimize CHC rules (and do not slice)\n" <<
        " " << OPT_ARITHM << "                   do not apply arithmetic constant propagation during parsing\n" <<
        " " << OPT_TO << "                            timeout for each Z3 run in ms (default: 1000)\n" <<
        " " << OPT_SER << "                     serialize the intermediate CHC representation to `chc.smt2` (and exit)\n" <<
        " " << OPT_DEBUG << " <LVL>                   print debugging information during run (default level: 0)\n\n" <<
        "V1 options only:\n" <<
        " " << OPT_ADD_EPSILON << "                           add small probabilities to features that never happen in the code\n" <<
        " " << OPT_K_IND << "                          run k-induction after each learned lemma\n\n" <<
        "V2 options only:\n" <<
        " " << OPT_ITP << "                           bound for itp-based proofs\n" <<
        " " << OPT_BATCH << "                         threshold for how many candidates to check at once\n" <<
        " " << OPT_RETRY << "                         threshold for how many lemmas to wait before giving failures a second chance\n\n" <<
        "V3 and V4 options:\n" <<
        " " << OPT_DATA_LEARNING << " <N>                      bootstrap candidates from behaviors (0: no, NUM: rounds)\n" <<
        "                                 (if \"" << OPT_DISJ <<"\" is enabled, then default is 1; otherwise, 0)\n\n" <<
        " " << OPT_MUT << "                           level of mutation for bootstrapped candidates (0: no, 1: (default), 2: full)\n" <<
        " " << OPT_SEED << "                   do not analyze syntax for seeds mining, except of the query\n" <<
        "                                 (thus, will disable quantified invariants)\n" <<
        " " << OPT_PROP << " <N>                      rounds of candidate propagation before bootstrapping\n" <<
        "                                 (if \"" << OPT_DISJ <<"\" is enabled, then default is 1; otherwise, 0)\n\n" <<
        "ImplCheck (V4) options only (\"" << OPT_DATA_LEARNING << "\" will be enabled automatically):\n" <<
        " " << OPT_MBP << "                       break equalities while MBP generation (0: no (default), 1: yes, 2: both)\n" <<
        " " << OPT_REC << "                            weaken and recycle data candidates\n" <<
        " " << OPT_DISJ << "                          generate disjunctive invariants\n" <<
        " " << OPT_D1 << "                       search for phases among all MBPs\n" <<
        " " << OPT_D2 << "                    propagate phase lemmas across guards\n" <<
        " " << OPT_D3 << "                    datalearn phase lemmas\n" <<
        " " << OPT_D4 << "                     strengthen MBP with abduction\n" <<
        " " << OPT_D5 << "                           direction of phase discovery (0: backward, 1: forward (default), 2: both)\n" <<
        " " << OPT_D6 << "                         do not consider duplicates of data candidates (needs \"" << OPT_DATA_LEARNING <<"\")\n\n" <<
        "SyGuS counterexample synthesis options (for BV):\n" <<
        " " << OPT_SYGUS << " [file]                   generate SyGuS file using PBE (point-based enumeration)\n" <<
        " " << OPT_SYGUS_TR << " [file]                generate SyGuS file using TR (transition relation)\n" <<
        " " << OPT_SYGUS_FULL << "                generate SyGuS file from full BndExpl trace\n" <<
        " " << OPT_SYGUS_FULL_BOUND << " <N>       max steps to explore for full trace (default: 1000)\n" <<
        " " << OPT_SYGUS_SPARSE << " <N>           sample every Nth point (default: 1 = all)\n" <<
        " " << OPT_SYGUS_POINTS << " <N>            number of trace points for PBE mode (default: 16)\n" <<
        " " << OPT_SYGUS_BITWIDTH << " <N>          bit-width for step parameter (default: auto)\n" <<
        " " << OPT_SYGUS_RUN << "                     also run CVC5 on the generated SyGuS file\n" <<
        " " << OPT_SYGUS_VALIDATE << "              synthesize and validate CEX inductively\n" <<
        " " << OPT_SYGUS_CCEX << " <file>           output CCEX file from synthesis (for validation)\n" <<
        " " << OPT_SYGUS_MBP << ", " << OPT_NO_SYGUS_MBP << "    seed grammar with MBP guards (default: enabled)\n" <<
        " " << OPT_SYGUS_INVARIANTS << ", " << OPT_NO_SYGUS_INVARIANTS << "  seed grammar with bootstrap invariants (default: disabled)\n" <<
        " " << OPT_LIA2BV << "                         translate LIA input to BV before SyGuS synthesis\n";

    return 0;
  }

  bool vers1 = getBoolValue(OPT_V1, false, argc, argv);
  bool vers2 = getBoolValue(OPT_V2, false, argc, argv);
  bool vers3 = getBoolValue(OPT_V3, false, argc, argv);
  bool vers4 = getBoolValue(OPT_V4, false, argc, argv);
  bool bv_solver = getBoolValue(OPT_V5, false, argc, argv);
  if (vers1 + vers2 + vers3 + vers4 + bv_solver > 1)
  {
    outs() << "Only one version of the algorithm can be chosen.\n";
    return 0;
  }

  if (!vers1 && !vers2 && !vers3 && !vers4 && !bv_solver)
    bv_solver = true; // default

  int max_attempts = getIntValue(OPT_MAX_ATTEMPTS, 2000000, argc, argv);
  int to = getIntValue(OPT_TO, 1000, argc, argv);
  bool kinduction = getBoolValue(OPT_K_IND, false, argc, argv);
  bool densecode = getBoolValue(OPT_GET_FREQS, false, argc, argv);
  bool addepsilon = getBoolValue(OPT_ADD_EPSILON, false, argc, argv);
  bool aggressivepruning = getBoolValue(OPT_AGG_PRUNING, false, argc, argv);
  int itp = getIntValue(OPT_ITP, 0, argc, argv);
  int batch = getIntValue(OPT_BATCH, 3, argc, argv);
  int retry = getIntValue(OPT_RETRY, 3, argc, argv);
  bool do_elim = !getBoolValue(OPT_ELIM, false, argc, argv);
  bool do_arithm = !getBoolValue(OPT_ARITHM, false, argc, argv);
  bool d_se = !getBoolValue(OPT_SEED, false, argc, argv);
  int do_prop = getIntValue(OPT_PROP, 0, argc, argv);
  int do_disj = getBoolValue(OPT_DISJ, false, argc, argv);
  int do_dl = getIntValue(OPT_DATA_LEARNING, 0, argc, argv);
  int do_mu = getIntValue(OPT_MUT, 1, argc, argv);
  int mbp_eqs = getIntValue(OPT_MBP, 1, argc, argv);
  bool d_m = getBoolValue(OPT_D1, false, argc, argv);
  bool d_p = getBoolValue(OPT_D2, false, argc, argv);
  bool d_d = getBoolValue(OPT_D3, false, argc, argv);
  bool d_s = getBoolValue(OPT_D4, false, argc, argv);
  int d_f = getIntValue(OPT_D5, 1, argc, argv);
  bool d_g = !getBoolValue(OPT_D6, false, argc, argv);
  bool d_r = getBoolValue(OPT_REC, false, argc, argv);
  bool d_ser = getBoolValue(OPT_SER, false, argc, argv);
  bool d_sertrans = getBoolValue(OPT_SERTRANS, false, argc, argv);
  bool d_lia2bv = getBoolValue(OPT_LIA2BV, false, argc, argv);
  bool d_horn = getBoolValue(OPT_HORN, false, argc, argv);
  bool d2 = getBoolValue("--data2", false, argc, argv);
  bool doReg = getBoolValue("--lin-reg", false, argc, argv);
  bool doCon = getBoolValue("--connect", false, argc, argv);
  bool doGJ = getBoolValue("--gj", false, argc, argv);
  bool skipTranslation = getBoolValue("--skip-translation", false, argc, argv);
  bool skipSampling = getBoolValue("--skip-sampling", false, argc, argv);
  int debug = getIntValue(OPT_DEBUG, 0, argc, argv);
  string ccex = getStrValue("--ccex", "", argc, argv);
  // CCEX validation methods: inductive is default (handles large traces), unrolling is opt-in
  // Supports both --use-ccex-inductive/--no-ccex-inductive and --use-ccex-unrolling/--no-ccex-unrolling
  bool ccexInductive = getBoolValueWithNegation("--use-ccex-inductive", "--no-ccex-inductive", true, argc, argv);
  bool ccexUnrolling = getBoolValueWithNegation("--use-ccex-unrolling", "--no-ccex-unrolling", false, argc, argv);

  // SyGuS counterexample synthesis options
  // --sygus (PBE mode) or --sygus-tr (TR mode) or --sygus-full (BndExpl mode)
  bool do_sygus = getBoolValue(OPT_SYGUS, false, argc, argv);
  bool do_sygus_tr = getBoolValue(OPT_SYGUS_TR, false, argc, argv);
  bool do_sygus_full = getBoolValue(OPT_SYGUS_FULL, false, argc, argv);
  int sygus_full_bound = getIntValue(OPT_SYGUS_FULL_BOUND, 1000, argc, argv);
  int sygus_sparse = getIntValue(OPT_SYGUS_SPARSE, 1, argc, argv);  // 1 = all points
  string sygus_file = "counterexample.sygus";  // default
  // Check if --sygus or --sygus-tr or --sygus-full has a following argument that is a custom filename
  // (not another option starting with '-' and not the input .smt2 file)
  for (int i = 1; i < argc - 1; i++)
  {
    if (strcmp(argv[i], OPT_SYGUS) == 0 || strcmp(argv[i], OPT_SYGUS_TR) == 0 || strcmp(argv[i], OPT_SYGUS_FULL) == 0)
    {
      string next_arg = string(argv[i+1]);
      // Check it's not an option and not the input file (which ends in .smt2)
      if (next_arg[0] != '-' && 
          (next_arg.length() < 5 || next_arg.substr(next_arg.length() - 5) != ".smt2"))
      {
        sygus_file = next_arg;
      }
      break;
    }
  }
  int sygus_points = getIntValue(OPT_SYGUS_POINTS, -1, argc, argv);  // -1 = auto-detect
  int sygus_bitwidth = getIntValue(OPT_SYGUS_BITWIDTH, -1, argc, argv);  // -1 = auto-detect
  bool sygus_run = getBoolValue(OPT_SYGUS_RUN, false, argc, argv);
  bool sygus_validate = getBoolValue(OPT_SYGUS_VALIDATE, false, argc, argv);
  bool sygus_mbp = getBoolValueWithNegation(OPT_SYGUS_MBP, OPT_NO_SYGUS_MBP, true, argc, argv);  // Default: enabled
  bool sygus_invariants = getBoolValueWithNegation(OPT_SYGUS_INVARIANTS, OPT_NO_SYGUS_INVARIANTS, false, argc, argv);  // Default: disabled
  string sygus_ccex_file = getStrValue(OPT_SYGUS_CCEX, "", argc, argv);

  if (d_m || d_p || d_d || d_s) do_disj = true;
  if (do_disj)
  {
    if (!d_p && !d_d)
    {
      if (debug) errs() << "WARNING: either \"" << OPT_D2 << "\" or \"" << OPT_D3 << "\" should be enabled. "
                        << "Enabling \"" << OPT_D3 << "\".\n";
      d_d = true;
    }
    if (!d_se)
    {
      if (debug) errs() << "WARNING: \"" << OPT_SEED << "\" and \"" << OPT_DISJ << "\" are incompatible. "
                        << "Ignoring \"" << OPT_SEED << "\".\n";
      d_se = true;
    }
    if (do_prop == 0) do_prop = 1;
    if (do_dl == 0) do_dl = 1;
  }

  if(doGJ || doReg || doCon)
  {
    d2 = true;
    if(do_dl < 1) do_dl = 1;
  }

  // Handle SyGuS Full mode (BndExpl-based concrete trace extraction)
  if (do_sygus_full)
  {
    outs() << "[DEBUG] Entering sygus-full mode\n";
    outs() << "[DEBUG] Input file: " << string(argv[argc - 1]) << "\n";
    outs() << "[DEBUG] Creating ExprFactory...\n";
    ExprFactory efac;
    outs() << "[DEBUG] Creating EZ3...\n";
    EZ3 z3(efac);
    outs() << "[DEBUG] Creating CHCs...\n";
    CHCs ruleManager(efac, z3, debug);
    
    outs() << "[DEBUG] Parsing file...\n";
    if (!ruleManager.parse(string(argv[argc - 1]), do_elim, do_arithm))
    {
      outs() << "Error parsing input file\n";
      return 1;
    }
    outs() << "[DEBUG] Parse successful\n";
    
    // LIA→BV translation if requested
    if (d_lia2bv)
    {
      if (!ruleManager.hasBV)
      {
        outs() << "\n=== Translating LIA to BV for SyGuS ===\n";
        Lia2BvTranslator translator(efac, z3, 4, debug);
        CHCs bvManager = translator.translate(ruleManager);
        ruleManager = bvManager;
        outs() << "  LIA→BV translation complete (hasBV=" << ruleManager.hasBV << ")\n";
      }
      else
      {
        if (debug)
          outs() << "  Input already in BV format, skipping LIA→BV translation\n";
      }
    }

    if (debug)
      outs() << "\n=== SyGuS Full Mode (BndExpl Trace Extraction) ===\n";
    
    // Instantiate BndExpl
    BndExpl bndExpl(ruleManager, to, debug);
    
    auto t_start = std::chrono::high_resolution_clock::now();

    // Extract concrete trace
    std::vector<std::map<Expr, Expr>> trace;
    ExprVector stateVars;
    
    if (!bndExpl.extractConcreteTrace(sygus_full_bound, trace, stateVars, sygus_sparse))
    {
      outs() << "Failed to extract concrete trace\n";
      return 1;
    }
    auto t_trace = std::chrono::high_resolution_clock::now();
    outs() << "  [Timing] Trace Extraction: " << std::chrono::duration_cast<std::chrono::milliseconds>(t_trace - t_start).count() << "ms\n";
    
    outs() << "  Extracted " << trace.size() << " trace points\n";
    outs() << "  State variables: " << stateVars.size() << "\n";
    
    // Determine step bitwidth
    int step_bw = sygus_bitwidth;
    if (step_bw < 0)
    {
      // Auto-detect: enough bits to represent trace size
      int bits_needed = 1;
      int64_t temp = trace.size() - 1;
      while (temp > 1) { temp >>= 1; bits_needed++; }
      if (bits_needed <= 8) step_bw = 8;
      else if (bits_needed <= 16) step_bw = 16;
      else step_bw = 32;
    }
    
    // Set default output filename
    string output_file = (sygus_file != "counterexample.sygus") ? sygus_file : "full_trace.sygus";
    
    // Extract MBP guards for grammar seeding if enabled
    ExprSet seedConstants;  // TODO: extract from CHC bodies
    ExprVector mbpGuards;
    ExprVector bootstrapInvariants;
    
    if (sygus_mbp)
    {
      if (debug)
        outs() << "\n=== Extracting MBP Guards for Grammar ===\n";
      
      if (bndExpl.extractMBPGuards(mbpGuards))
      {
        outs() << "  Extracted " << mbpGuards.size() << " MBP guards for grammar\n";
      }
      else
      {
        if (debug)
          outs() << "  No MBP guards extracted (using generic grammar)\n";
      }
    }
    
    if (sygus_invariants)
    {
      if (debug)
        outs() << "\n=== Extracting Bootstrap Invariants for Grammar ===\n";
      
      if (bndExpl.extractBootstrapInvariants(bootstrapInvariants))
      {
        outs() << "  Extracted " << bootstrapInvariants.size() << " bootstrap invariants for grammar\n";
      }
      else
      {
        if (debug)
          outs() << "  No invariants extracted (using generic grammar)\n";
      }
    }
    
    if (!bndExpl.writeSyGuSFromTrace(output_file, trace, stateVars, step_bw, seedConstants, mbpGuards, bootstrapInvariants))
    {
      outs() << "Failed to write SyGuS file\n";
      return 1;
    }
    auto t_gen = std::chrono::high_resolution_clock::now();
    outs() << "  [Timing] SyGuS Gen: " << std::chrono::duration_cast<std::chrono::milliseconds>(t_gen - t_trace).count() << "ms\n";
    
    outs() << "  Generated SyGuS file: " << output_file << "\n";
    
    // Optionally run CVC5 to synthesize closed-form functions
    if (sygus_run)
    {
      outs() << "  Running CVC5 on " << output_file << "...\n";
      auto t_cvc_start = std::chrono::high_resolution_clock::now();
      auto result = ruleManager.runCVC5SyGuS(output_file, 180);
      auto t_cvc_end = std::chrono::high_resolution_clock::now();
      outs() << "  [Timing] CVC5 Synthesis: " << std::chrono::duration_cast<std::chrono::milliseconds>(t_cvc_end - t_cvc_start).count() << "ms\n";
      if (result.empty())
      {
        outs() << "CVC5 did not find a solution\n";
        return 1;
      }
      outs() << "\nSynthesized functions:\n";
      for (const auto& kv : result)
      {
        outs() << "  " << kv.first << ": " << kv.second << "\n";
      }
      
      // Generate CCEX file if requested
      if (sygus_ccex_file != "" || sygus_validate)
      {
        string ccex_output = (sygus_ccex_file != "") ? sygus_ccex_file : "synthesized_ccex.smt2";
        bool ccex_ok = ruleManager.generateCCEXFromSynthesis(result, ccex_output, trace.size() - 1, sygus_bitwidth);
        if (!ccex_ok)
        {
          outs() << "Failed to generate CCEX file\n";
          return 1;
        }
        outs() << "Generated CCEX file: " << ccex_output << "\n";
        
        // Validate if requested
        if (sygus_validate)
        {
          outs() << "\nValidating counterexample inductively...\n";
          auto t_val_start = std::chrono::high_resolution_clock::now();
          
          // Load the CCEX file
          ZSolver<EZ3> solver(z3);
          ExprVector ccexExprs = solver.loadFromFile(ccex_output);
          
          // Create BndExpl for validation
          BndExpl bnd(ruleManager, 0, debug);
          tribool inductiveResult = bnd.validateCEXInductive(ccexExprs);
          
          auto t_val_end = std::chrono::high_resolution_clock::now();
          outs() << "  [Timing] Validation: " << std::chrono::duration_cast<std::chrono::milliseconds>(t_val_end - t_val_start).count() << "ms\n";

          if (inductiveResult == true)
          {
            outs() << "✓ Counterexample is INDUCTIVE - property is FALSE\n";
            
            // Update CCEX file if a tighter bound was found during validation
            if (bnd.validatedTraceBound != -1 && bnd.validatedTraceBound != (int)(trace.size() - 1))
            {
              outs() << "  [Deep] Updating CCEX file with refined bound N=" << bnd.validatedTraceBound << "\n";
              ruleManager.generateCCEXFromSynthesis(result, ccex_output, bnd.validatedTraceBound, sygus_bitwidth);
            }
          }
          else if (inductiveResult == false)
          {
            outs() << "✗ Counterexample is NOT inductive\n";
          }
          else
          {
            outs() << "? Counterexample validation is UNKNOWN\n";
          }
        }
      }
    }
    else
    {
      outs() << "  Run with: cvc5 --lang=sygus2 " << output_file << "\n";
    }
    
    return 0;
  }

  // Handle SyGuS counterexample synthesis mode (PBE or TR)
  if (do_sygus || do_sygus_tr)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3, debug);
    
    if (!ruleManager.parse(string(argv[argc - 1]), do_elim, do_arithm))
    {
      outs() << "Error parsing input file\n";
      return 1;
    }
    
    // LIA→BV translation if requested
    if (d_lia2bv)
    {
      if (!ruleManager.hasBV)
      {
        outs() << "\n=== Translating LIA to BV for SyGuS ===\n";
        Lia2BvTranslator translator(efac, z3, 4, debug);
        CHCs bvManager = translator.translate(ruleManager);
        ruleManager = bvManager;
        outs() << "  LIA→BV translation complete (hasBV=" << ruleManager.hasBV << ")\n";
      }
      else
      {
        if (debug)
          outs() << "  Input already in BV format, skipping LIA→BV translation\n";
      }
    }

    // Set default output filename if not specified
    string output_file = (sygus_file != "") ? sygus_file : "counterexample.sygus";
    
    bool success;
    if (do_sygus_tr)
    {
      // TR mode: use transition relation constraints
      success = ruleManager.generateCounterexampleSyGuSTR(
        output_file, 
        sygus_bitwidth
      );
    }
    else
    {
      // PBE mode: use point-based enumeration
      success = ruleManager.generateCounterexampleSyGuS(
        output_file, 
        sygus_points, 
        sygus_bitwidth, 
        true  // include_bad_check
      );
    }
    
    if (!success)
    {
      outs() << "Failed to generate SyGuS file\n";
      return 1;
    }
    
    // Optionally run CVC5
    if (sygus_run)
    {
      auto result = ruleManager.runCVC5SyGuS(output_file, 180);
      if (result.empty())
      {
        outs() << "CVC5 did not find a solution\n";
        return 1;
      }
      outs() << "\nSynthesized functions:\n";
      for (const auto& kv : result)
      {
        outs() << "  " << kv.first << ": " << kv.second << "\n";
      }
      
      // Generate CCEX file if requested
      if (sygus_ccex_file != "" || sygus_validate)
      {
        string ccex_output = (sygus_ccex_file != "") ? sygus_ccex_file : "synthesized_ccex.smt2";
        bool ccex_ok = ruleManager.generateCCEXFromSynthesis(result, ccex_output, -1, sygus_bitwidth);
        if (!ccex_ok)
        {
          outs() << "Failed to generate CCEX file\n";
          return 1;
        }
        outs() << "Generated CCEX file: " << ccex_output << "\n";
        
        // Validate if requested
        if (sygus_validate)
        {
          outs() << "\nValidating counterexample inductively...\n";
          
          // Load the CCEX file
          ZSolver<EZ3> solver(z3);
          ExprVector ccexExprs = solver.loadFromFile(ccex_output);
          
          // Create BndExpl for validation
          BndExpl bnd(ruleManager, 0, debug);
          tribool inductiveResult = bnd.validateCEXInductive(ccexExprs);
          
          if (inductiveResult == true)
          {
            outs() << "✓ Counterexample is INDUCTIVE - property is FALSE\n";

            // Update CCEX file if a tighter bound was found during validation
            if (bnd.validatedTraceBound != -1)
            {
               outs() << "  [Deep] Updating CCEX file with refined bound N=" << bnd.validatedTraceBound << "\n";
               ruleManager.generateCCEXFromSynthesis(result, ccex_output, bnd.validatedTraceBound, sygus_bitwidth);
            }
          }
          else if (inductiveResult == false)
          {
            outs() << "✗ Counterexample is NOT inductive\n";
          }
          else
          {
            outs() << "? Counterexample validation is UNKNOWN\n";
          }
        }
      }
    }
    
    return 0;
  }

  bool res = false;
  if(bv_solver)
    res = learnInvariants5(string(argv[argc - 1]), ccex, ccexInductive, ccexUnrolling, max_attempts, to, densecode, aggressivepruning,
                           do_dl, do_mu, do_elim, do_arithm, do_disj, do_prop, mbp_eqs,
                           d_m, d_p, d_d, d_s, d_f, d_r, d_g, d_se, d_ser, d_horn, d_sertrans,
                           d2, doGJ, doReg, doCon, d_lia2bv, skipSampling, debug);
  else if (vers4)      // MBP-based, path-sensitive algorithms
    learnInvariants4(string(argv[argc-1]), max_attempts, to, densecode, aggressivepruning,
                   do_dl, do_mu, do_elim, do_arithm, do_disj, do_prop, mbp_eqs,
                   d_m, d_p, d_d, d_s, d_f, d_r, d_g, d_se, d_ser, d2, doGJ, doReg, doCon, debug);
  else if (vers3) // FMCAD'18 + CAV'19 + experiments with data
    learnInvariants3(string(argv[argc-1]), max_attempts, to, densecode, aggressivepruning,
                     do_dl, do_mu, do_elim, do_arithm, do_prop, d_se, d_ser, debug);
  else if (vers2) // run the TACAS'18 algorithm
    learnInvariants2(string(argv[argc-1]), to, max_attempts,
                  itp, batch, retry, densecode, aggressivepruning, debug);
  else            // run the FMCAD'17 algorithm
    learnInvariants(string(argv[argc-1]), to, max_attempts,
                  kinduction, itp, densecode, addepsilon, aggressivepruning, debug);
  
  if(res) return 0;
  else return 1;
}
