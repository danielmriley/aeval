#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include "Horn.hpp"
#include "simpl/Bv2Lia.hpp"
#include "simpl/Lia2Bv.hpp"

using namespace std;

namespace ufo
{
  class BitHorn 
  {
    private:
    ExprFactory &m_efac;
    EZ3 &m_z3;
    CHCs m_liaChcs;  // Original LIA program
    CHCs m_bvChcs;   // Translated BV program
    CHCs m_liaChcsBack; // Back-translated LIA program
    Lia2BvTranslator m_Lia2BvTranslator;
    Bv2LiaTranslator m_Bv2LiaTranslator;
    int debug; 

    public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) : 
      m_efac(efac), 
      m_z3(z3),
      m_liaChcs(input), // Make a copy
      m_bvChcs(input), // Make a copy 
      m_liaChcsBack(input),
      m_Lia2BvTranslator(efac, z3, 4, _debug),  // Pass debug parameter
      m_Bv2LiaTranslator(efac, z3),
      debug(_debug) { outs() << "CONSTRUCTOR\n"; }

    bool translateToBv()
    {
      // Translate LIA to BV
      if(debug >= 3)
      {
        outs() << "Beginning translation\n";
      }
      m_bvChcs = m_Lia2BvTranslator.translate(m_bvChcs);
      if (debug >= 3)
      {
        outs() << "Ending translation\n";
        m_bvChcs.print(true);
      }

      // Serialize the translated program
      m_bvChcs.serialize(false);

      return true;
    }

    bool translateToLia()
    {
      if (debug >= 2)
      {
        outs() << "Translating BV back to LIA\n";
      }

      m_liaChcsBack = m_Bv2LiaTranslator.translate(m_bvChcs);
      return true;
    }

    CHCs& getLiaChcs() { return m_liaChcs; }
    CHCs& getBvChcs() { return m_bvChcs; }
    CHCs& getLiaChcsBack() { return m_liaChcsBack; }

    void solve() {
      outs() << "Starting BitHorn solver\n";
    }
  };

  // Main entry point for BV translation and solving
  inline void learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, int debug)
  {
    // Create factories and parse input
    ExprFactory efac;
    EZ3 z3(efac); 

    // Parse the original CHC system
    CHCs ruleManager(efac, z3, debug);
    if (!ruleManager.parse(smt, doElim, doArithm))
    {
      outs() << "Error parsing input file\n";
      return;
    }

    // For non-serialization case, check if input is BV format
    if (!ruleManager.hasBV)
    {
      outs() << "Input is not in BV format\n";
      return;
    }

    // Create BitHorn solver
    BitHorn bh(efac, z3, ruleManager, debug);

    if (ser) {
      // When ser is true, just translate and serialize
      if (!bh.translateToBv()) {
        outs() << "Error translating LIA to BV\n"; 
        return;
      }
      bh.getBvChcs().serialize(false);
      if(debug >= 2) outs() << "Serialized BV translation\n";
      return;
    }

    // Solve BV system
    bh.solve();
  }
}

#endif
