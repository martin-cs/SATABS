/*******************************************************************\

Module: Parse Command Line Options for CEGAR

Author: Daniel Kroening
        Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_CMDLINE_OPTIONS_H
#define CPROVER_CEGAR_CMDLINE_OPTIONS_H

#include <parseoptions.h>
#include <config.h>

#include <cbmc/xml_interface.h>

class cmdline_optionst:
  public parseoptions_baset,
  public xml_interfacet
{
public:
  virtual int doit();
  virtual void help();

  cmdline_optionst(int argc, const char **argv):
    parseoptions_baset("(v):(gui)(show-loops)"
    "(floatbv)(fixedbv)"
    "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)"
    "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)"
    "(ppc-macos)(unsigned-char)"
    "(round-to-nearest)(round-to-plus-inf)(round-to-minus-inf)(round-to-zero)"
    "(show-final-program)(modelchecker):"
    "(string-abstraction)(no-simplify)"
    "(string-abstraction)(full-inlining)"
    "(predicates):(show-claims)(bounds-check)(no-library)"
    "(no-invariant-sets)"
    "(xml-ui)(xml-interface)"
    "(show-equations)(show-value-sets)(show-invariant-sets)"
    "(div-by-zero-check)(pointer-check)"
    "(signed-overflow-check)(unsigned-overflow-check)"
    "(no-assertions)(no-assumptions)"
    "(iterations):(function):"
    "(show-adjusted-functions)(refiner):(ipplimit):"
    "(show-goto-functions)(simulator):"
    "(abstractor):I:D:(claim):(little-endian)(big-endian)"
    "(loop-detection)(no-slicing)"
    "(nan-check)(error-label):(prefix-first)(no-arch)"
    "(no-path-slicing)(version)(shortest-prefix)"
    "(save-bps)(max-threads):(max-new-predicates):(prefer-non-pointer-predicates)"
    "(no-mixed-predicates)"
    "(max-cube-length):(concurrency)(passive-nondet)(csv-stats)",
    argc, argv),
    xml_interfacet(cmdline)
  {
  }

protected:
  void get_command_line_options(class optionst &options);
};

#endif
