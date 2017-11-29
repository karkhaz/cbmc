/*******************************************************************\

Module: JBMC Command Line Option Processing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JBMC Command Line Option Processing

#ifndef CPROVER_JBMC_JBMC_PARSE_OPTIONS_H
#define CPROVER_JBMC_JBMC_PARSE_OPTIONS_H

#include <util/ui_message.h>
#include <util/parse_options.h>
#include <util/language.h>

#include <analyses/goto_check.h>

#include <cbmc/bmc.h>

#include <java_bytecode/java_bytecode_language.h>

class bmct;
class goto_functionst;
class optionst;

#define JBMC_OPTIONS \
  OPT_BMC \
  "(preprocess)(slice-by-trace):" \
  OPT_FUNCTIONS \
  "(no-simplify)(full-slice)" \
  "(debug-level):(no-propagation)(no-simplify-if)" \
  "(document-subgoals)(outfile):" \
  "(object-bits):" \
  "(classpath):(cp):(main-class):" \
  "(partial-loops)" \
  OPT_GOTO_CHECK \
  "(no-assertions)(no-assumptions)" \
  "(no-built-in-assertions)" \
  "(xml-ui)(json-ui)" \
  "(smt1)(smt2)(fpa)(cvc3)(cvc4)(boolector)(yices)(z3)(opensmt)(mathsat)" \
  "(no-sat-preprocessor)" \
  "(beautify)" \
  "(dimacs)(refine)(max-node-refinement):(refine-arrays)(refine-arithmetic)"\
  "(refine-strings)" \
  "(string-non-empty)" \
  "(string-printable)" \
  "(string-max-length):" \
  "(string-max-input-length):" \
  "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
  "(show-goto-functions)" \
  "(show-symbol-table)(show-parse-tree)" \
  "(show-properties)" \
  "(drop-unused-functions)" \
  "(property):(stop-on-fail)(trace)" \
  "(verbosity):(no-library)" \
  "(version)" \
  "(cover):(symex-coverage-report):" \
  "(i386-linux)(i386-macos)(i386-win32)(win32)(winx64)" \
  "(ppc-macos)" \
  "(arrays-uf-always)(arrays-uf-never)" \
  "(string-abstraction)(no-arch)(arch):" \
  JAVA_BYTECODE_LANGUAGE_OPTIONS \
  "(java-unwind-enum-static)" \
  "(localize-faults)(localize-faults-method):"

class jbmc_parse_optionst:
  public parse_options_baset,
  public messaget
{
public:
  virtual int doit() override;
  virtual void help() override;

  jbmc_parse_optionst(int argc, const char **argv);
  jbmc_parse_optionst(
    int argc,
    const char **argv,
    const std::string &extra_options);

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler;

  void eval_verbosity();
  void get_command_line_options(optionst &);
  int get_goto_program(const optionst &);
  bool process_goto_program(const optionst &);
  bool set_properties();
};

#endif // CPROVER_JBMC_JBMC_PARSE_OPTIONS_H
