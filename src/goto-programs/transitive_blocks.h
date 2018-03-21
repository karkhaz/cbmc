/// \file transitive_blocks.h
/// \brief Lines of code transitively reachable from basic blocks
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_PROGRAMS_TRANSITIVE_BLOCKS_H
#define CPROVER_GOTO_PROGRAMS_TRANSITIVE_BLOCKS_H

#include "goto_model.h"
#include "goto_program.h"

#include <util/message.h>

#include <map>
#include <set>

/// \brief Lines that are transitively touched by executing a lexical block
///
/// This class computes, for each _lexical_ (not basic) block, the lines that
/// might be executed if we were to execute that block. This takes into account
/// all lines that are arbitrarily nested in the block, as well as all lines
/// present in functions that are called from inside the block.
///
/// The tests under regression/cbmc/transitive-blocks-* show which lines should
/// and should not be included in this relation.
class transitive_blockst
{
public:
  explicit transitive_blockst(const abstract_goto_modelt &);

  typedef std::map<source_locationt, std::set<source_locationt>>
    transitive_linest;

  /// Map from source locations at the beginning of a lexical block, to the
  /// source locations that would potentially be touched when executing that
  /// block.
  transitive_linest line_map;

  /// \brief Print code blocks, suitable for invocation from frontend
  static void show_blocks(const abstract_goto_modelt &, messaget &);

  /// \brief Print transitive line reach, suitable for invocation from frontend
  static void show_transitive_blocks(const abstract_goto_modelt &, messaget &);

protected:
  /// \brief Map from function names to lines statically reachable
  typedef std::unordered_map<irep_idt, std::set<source_locationt>, irep_id_hash>
    funs2linest;

  /// \brief Compute what lines could be executed if a function is called
  void
  compute_transitive_function_lines(funs2linest &transitive_function_lines);

  /// \brief The source location of an expr
  ///
  /// Some ireps (in particular, code_ifthenelsets and code_whilets) don't have
  /// a source location associated with them. This function sets the output
  /// argument to be the location of the first descendent of expr that has a
  /// source_location. For guarded code blocks, this will usually be the source
  /// location of the guard expression.
  bool location_of(const exprt &, source_locationt &) const;

  /// \brief Compute line_map for a particular goto function
  void
  compute_blocks(const irep_idt &, const goto_programt &, const funs2linest &);

  /// \brief For each block, compute the union of the lines transitively touched
  /// by its successor blocks
  void transitive_of_successors(
    const codet &,
    std::set<source_locationt> &future_lines);

  /// \brief For each block, compute the union of the lines transitively touched
  /// by its sub-blocks
  void transitive_of_nested(
    const codet &,
    const funs2linest &funs2lines,
    std::set<source_locationt> &my_locations);

  const abstract_goto_modelt &model;
};

#define OPT_TRANSITIVE_BLOCKS "(show-transitive-blocks)(show-blocks)"

#define HELP_TRANSITIVE_BLOCKS                                                 \
  " --show-blocks                print goto-program changed into code blocks"  \
  " --show-transitive-blocks     print lines touched by executing a block"

#endif
