#ifndef BITHORN__HPP__
#define BITHORN__HPP__

#include "Horn.hpp"
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
    Lia2BvTranslator m_translator;
    int debug; 

    public:
    BitHorn(ExprFactory &efac, EZ3 &z3, CHCs &input, int _debug = 0) : 
      m_efac(efac), 
      m_z3(z3),
      m_liaChcs(input), // Make a copy
      m_bvChcs(input), // Make a copy 
      m_translator(efac, z3),
      debug(_debug) { outs() << "CONSTRUCTOR\n"; }

    bool translateToBv()
    {
      // Translate LIA to BV
      if(debug >= 3)
      {
        outs() << "Beginning translation\n";
      }
      m_bvChcs = m_translator.translate(m_bvChcs);
      if (debug >= 3)
      {
        outs() << "Ending translation\n";
        m_bvChcs.print(true);
      }

      // Serialize the translated program
      m_bvChcs.serialize(false);

      return true;
    }

    CHCs& getLiaChcs() { return m_liaChcs; }
    CHCs& getBvChcs() { return m_bvChcs; }
  };

  // Main entry point for BV translation and solving
  inline void learnInvariants5(string smt, unsigned maxAttempts, unsigned to,
                               bool freqs, bool aggp, int dat, int mut, bool doElim, bool doArithm,
                               bool doDisj, int doProp, int mbpEqs, bool dAllMbp, bool dAddProp,
                               bool dAddDat, bool dStrenMbp, int dFwd, bool dRec, bool dGenerous,
                               bool dSee, bool ser, bool horn, bool serTrans, int debug)
  {
    // Create factories
    ExprFactory efac;
    EZ3 z3(efac); 

    // Parse the original CHC system
    CHCs liaSystem(efac, z3, debug);
    if (!liaSystem.parse(smt, doElim, doArithm))
    {
      outs() << "Error parsing input file\n";
      return;
    }

    if (debug >= 3)
    {
      outs() << "Original system:\n";
      liaSystem.print(true);
    }

    outs() << "TESTING\n";

    // Create BitHorn solver and give it the parsed system
    BitHorn bh(efac, z3, liaSystem, debug);

    if(debug >= 2)
    {
      outs() << "Moving to translation\n";
    }

    // Translate LIA to BV
    if (!bh.translateToBv())
    {
      outs() << "Error translating LIA to BV\n";
      return;
    }
    else
    {
      outs() << "Translated successfully!\n";
      CHCs testBVParsing(efac, z3, debug);
      testBVParsing.parse("chc.smt2");
    }
  }
}

#endif
