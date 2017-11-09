/*******************************************************************\

Module: Bounded Model Checking for ANSI-C + HDL

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking for ANSI-C + HDL

#ifndef CPROVER_CBMC_BMC_H
#define CPROVER_CBMC_BMC_H

#include <list>
#include <map>

#include <util/invariant.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <solvers/prop/prop.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/sat/cnf.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <solvers/smt2/smt2_dec.h>

#include <goto-symex/symex_target_equation.h>
#include <goto-programs/safety_checker.h>

#include "symex_bmc.h"

class goto_modelt;
class cbmc_solverst;

class bmct:public safety_checkert
{
public:

/// \brief Constructor for path exploration with freshly-initialized state
///
/// This constructor should be used for symbolically executing a program
/// from the entry point with fresh state. There are two main behaviours
/// that can happen when constructing an instance of this class:
///
/// - If the `--paths` flag in the `options` argument to this
///   constructor is `false` (unset), an instance of this class will
///   symbolically execute the entire program, performing path merging
///   to build a formula corresponding to all executions of the program
///   up to the unwinding limit. In this case, the `branch_worklist`
///   member shall not be touched; this is enforced by the assertion in
///   this class' implementation of bmct::perform_symbolic_execution().
///
/// - If the `--paths` flag is `true`, this `bmct` object will explore a
///   single path through the codebase without doing any path merging.
///   If some paths were not taken, the state at those branch points
///   will be appended to `branch_worklist`. After the single path that
///   this `bmct` object executed has been model-checked, you can resume
///   exploring further paths by popping an element from
///   `branch_worklist` and using it to construct a path_explorert
///   object.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    goto_symext::branch_worklistt &_branch_worklist):
    safety_checkert(ns, _message_handler),
    options(_options),
    outer_symbol_table(outer_symbol_table),
    ns(outer_symbol_table),
    equation(),
    branch_worklist(_branch_worklist),
    symex(outer_symbol_table, equation, branch_worklist),
    prop_conv(_prop_conv),
    ui(ui_message_handlert::uit::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
    symex.record_coverage=
      !options.get_option("symex-coverage-report").empty();
  }

protected:

/// \brief Constructor for path exploration from saved state
///
/// This constructor exists as a delegate for the path_explorert class.
/// It differs from \ref bmct's public constructor in that it actually
/// does something with the branch_worklistt argument, and also takes a
/// symex_target_equationt. See the documentation for path_explorert for
/// details.
  bmct(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &_equation,
    goto_symext::branch_worklistt &_branch_worklist):
    safety_checkert(ns, _message_handler),
    options(_options),
    outer_symbol_table(outer_symbol_table),
    ns(outer_symbol_table),
    equation(_equation),
    branch_worklist(_branch_worklist),
    symex(outer_symbol_table, equation, branch_worklist),
    prop_conv(_prop_conv),
    ui(ui_message_handlert::uit::PLAIN)
  {
    symex.constant_propagation=options.get_bool_option("propagation");
    symex.record_coverage=
      !options.get_option("symex-coverage-report").empty();
    INVARIANT(options.get_bool_option("paths"),
        "Should only use saved equation & goto_state constructor "
        "when doing path exploration");
  }

public:
  virtual resultt run(
      const goto_functionst &goto_functions);
  virtual ~bmct() { }

  static int do_language_agnostic_bmc(
      const optionst &opts,
      const goto_modelt &goto_model,
      const ui_message_handlert::uit &ui,
      messaget *const message,
      cbmc_solverst &solvers);

  // additional stuff
  expr_listt bmc_constraints;

  void set_ui(ui_message_handlert::uit _ui) { ui=_ui; }

  // the safety_checkert interface
  virtual resultt operator()(
    const goto_functionst &goto_functions)
  {
    return run(goto_functions);
  }

protected:
  const optionst &options;
  /// \brief symbol table for the goto-program that we will execute
  const symbol_tablet &outer_symbol_table;
  /// \brief symbol table generated during symbolic execution
  symbol_tablet new_symbol_table;
  namespacet ns;
  symex_target_equationt equation;
  goto_symext::branch_worklistt &branch_worklist;
  symex_bmct symex;
  prop_convt &prop_conv;

  // use gui format
  ui_message_handlert::uit ui;

  virtual decision_proceduret::resultt
    run_decision_procedure(prop_convt &prop_conv);

  virtual resultt decide(
    const goto_functionst &,
    prop_convt &);

  // unwinding
  virtual void setup_unwind();
  virtual void do_unwind_module();
  void do_conversion();

  virtual void show_vcc();
  virtual void show_vcc_plain(std::ostream &out);
  virtual void show_vcc_json(std::ostream &out);

  virtual resultt all_properties(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual resultt stop_on_fail(
    const goto_functionst &goto_functions,
    prop_convt &solver);
  virtual void show_program();
  virtual void report_success();
  virtual void report_failure();

  virtual void error_trace();
  void output_graphml(
    resultt result,
    const goto_functionst &goto_functions);

  bool cover(
    const goto_functionst &goto_functions,
    const optionst::value_listt &criteria);

  friend class bmc_all_propertiest;
  friend class bmc_covert;
  template <template <class goalt> class covert>
  friend class bmc_goal_covert;
  friend class fault_localizationt;

private:
  /// \brief Class-specific symbolic execution
  ///
  /// This private virtual should be overridden by derived classes to
  /// invoke the symbolic executor in a class-specific way. This
  /// implementation invokes goto_symext::operator() to perform
  /// full-program model-checking from the entry point of the program.
  virtual void perform_symbolic_execution(
      const goto_functionst &goto_functions);
};

/// \brief Symbolic execution from a saved branch point
///
/// Instances of this class execute a single program path from a saved
/// branch point. The saved branch point is supplied to the constructor
/// as a pair of goto_target_equationt (which holds the SSA steps
/// executed so far), and a goto_symex_statet Note that the \ref bmct
/// base class can also execute a single path (it will do so if the
/// `--paths` flag is set in its `options` member), but will always
/// begin symbolic execution from the beginning of the program with
/// fresh state.
class path_explorert:public bmct
{
public:
  path_explorert(
    const optionst &_options,
    const symbol_tablet &outer_symbol_table,
    message_handlert &_message_handler,
    prop_convt &_prop_conv,
    symex_target_equationt &saved_equation,
    const goto_symex_statet &saved_state,
    goto_symext::branch_worklistt &branch_worklist):
    bmct(_options,
        outer_symbol_table,
        _message_handler, _prop_conv,
        saved_equation, branch_worklist),
    saved_state(saved_state)
  { }

protected:
  const goto_symex_statet &saved_state;

private:
  /// \brief Resume symbolic execution from saved branch point
  ///
  /// This overrides the base implementation to call the symbolic executor with
  /// the saved symex_target_equationt, symbol_tablet, and goto_symex_statet
  /// provided as arguments to the constructor of this class.
  void perform_symbolic_execution(
      const goto_functionst &goto_functions) override;
};

#endif // CPROVER_CBMC_BMC_H
