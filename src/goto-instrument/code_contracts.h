/*******************************************************************\

Module: Verify and use annotated invariants and pre/post-conditions

Author: Michael Tautschnig

Date: February 2016

\*******************************************************************/

/// \file
/// Verify and use annotated invariants and pre/post-conditions

#ifndef CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
#define CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H

class goto_modelt;

class code_contractst
{
public:
  code_contractst(
    goto_modelt goto_model,
    messaget &log)
    : ns(goto_model.symbol_table),
      symbol_table(goto_model.symbol_table),
      goto_functions(goto_model.goto_functions),
      temporary_counter(0),
      log(log)
  {
  }

  bool check();

  /// \brief Replace all calls to each function in the list with that function's
  ///        contract
  bool replace(const std::list<std::string> &funs_to_replace);

  /// \brief Replace all calls to all functions that have a contract with the
  ///        contract
  bool replace();

protected:
  namespacet ns;
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  unsigned temporary_counter;
  messaget &log;

  std::unordered_set<irep_idt> summarized;

  void code_contracts(goto_functionst::goto_functiont &goto_function);

  /// \brief Does the named function have a contract?
  bool has_contract(const irep_idt);

  void apply_contract(
    goto_programt &goto_program,
    goto_programt::targett target);

  void add_contract_check(
    const irep_idt &function,
    goto_programt &dest);

  const symbolt &new_tmp_symbol(
    const typet &type,
    const source_locationt &source_location,
    const irep_idt &function_id,
    const irep_idt &mode);
};


#endif // CPROVER_GOTO_INSTRUMENT_CODE_CONTRACTS_H
