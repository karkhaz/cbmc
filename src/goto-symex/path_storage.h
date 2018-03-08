/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include "goto_symex_state.h"
#include "symex_target_equation.h"

#include <goto-programs/goto_model.h>

#include <util/options.h>
#include <util/cmdline.h>
#include <util/ui_message.h>
#include <util/invariant.h>

#include <memory>

/// \brief Storage for symbolic execution paths to be resumed later
///
/// This data structure supports saving partially-executed symbolic
/// execution \ref path_storaget::patht "paths" so that their execution can
/// be halted and resumed later. The choice of which path should be
/// resumed next is implemented by subtypes of this abstract class.
class path_storaget
{
public:
  /// \brief Information saved at a conditional goto to resume execution
  struct patht
  {
    symex_target_equationt equation;
    goto_symex_statet state;

    explicit patht(const symex_target_equationt &e, const goto_symex_statet &s)
      : equation(e), state(s, &equation)
    {
    }

    explicit patht(const patht &other)
      : equation(other.equation), state(other.state, &equation)
    {
    }
  };

  virtual ~path_storaget() = default;

  path_storaget(const abstract_goto_modelt &model) : model(model)
  {
  }

  /// \brief Reference to the next path to resume
  patht &peek()
  {
    PRECONDITION(!empty());
    return private_peek();
  }

  /// \brief Add paths to resume to the storage
  ///
  /// Symbolic execution is suspended when we reach a conditional goto
  /// instruction with two successors. Thus, we always add a pair of paths to
  /// the path storage.
  ///
  /// \param next_instruction the instruction following the goto instruction
  /// \param jump_target the target instruction of the goto instruction
  virtual void
  push(const patht &next_instruction, const patht &jump_target) = 0;

  /// \brief Remove the next path to resume from the storage
  void pop()
  {
    PRECONDITION(!empty());
    private_pop();
  }

  /// \brief How many paths does this storage contain?
  virtual std::size_t size() const = 0;

  /// \brief Is this storage empty?
  bool empty() const
  {
    return size() == 0;
  };

protected:
  const abstract_goto_modelt &model;

private:
  // Derived classes should override these methods, allowing the base class to
  // enforce preconditions.
  virtual patht &private_peek() = 0;
  virtual void private_pop() = 0;
};

/// \brief FIFO save queue: paths are resumed in the order that they were saved
class path_fifot : public path_storaget
{
public:
  path_fifot(const abstract_goto_modelt &model) : path_storaget(model)
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;

protected:
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Prefer to make progress (skip over loops rather than into them)
class progressive_path_fifot : public path_storaget
{
public:
  progressive_path_fifot(const abstract_goto_modelt &model)
    : path_storaget(model)
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;

protected:
  std::list<patht> jumps;
  std::list<patht> nexts;

  /// \brief Should we pop the `nexts` queue or the `jumps` queue?
  /// If the last path we peeked at was on the next queue, then that's the
  /// path we should pop. This is the case _even if_ a path was added to the
  /// jump queue in the mean time.
  bool pop_next;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Factory and information for path_storaget
class path_strategy_choosert
{
public:
  path_strategy_choosert();

  /// \brief suitable for displaying as a front-end help message
  std::string show_strategies() const;

  /// \brief is there a factory constructor for the named strategy?
  bool is_valid_strategy(const std::string strategy) const
  {
    return strategies.find(strategy) != strategies.end();
  }

  /// \brief Factory for a path_storaget
  ///
  /// Ensure that path_strategy_choosert::is_valid_strategy() returns true for a
  /// particular string before calling this function on that string.
  std::unique_ptr<path_storaget>
  get(const std::string strategy, const abstract_goto_modelt &model) const
  {
    auto found = strategies.find(strategy);
    INVARIANT(
      found != strategies.end(), "Unknown strategy '" + strategy + "'.");
    return found->second.second(model);
  }

  /// \brief add `paths` and `exploration-strategy` option, suitable to be
  /// invoked from front-ends.
  void
  set_path_strategy_options(const cmdlinet &, optionst &, messaget &) const;

protected:
  std::string default_strategy() const
  {
    return "fifo";
  }

  /// Map from the name of a strategy (to be supplied on the command line), to
  /// the help text for that strategy and a factory thunk returning a pointer to
  /// a derived class of path_storaget that implements that strategy.
  std::map<const std::string,
           std::pair<const std::string,
                     const std::function<std::unique_ptr<path_storaget>(
                       const abstract_goto_modelt &)>>>
    strategies;
};

/// \brief Unusable path storage, for clients who don't intend to use it
///
/// This class is intended for clients who don't have a \ref
/// abstract_goto_modelt to initialize a real path_storaget with, and
/// thus cannot call path_strategy_choosert::get().
class degenerate_path_storaget : public path_storaget
{
public:
  degenerate_path_storaget() : path_storaget(model)
  {
  }
  void push(const patht &, const patht &) override
  {
    INVARIANT(false, "Cannot push onto degenerate path storage");
  }
  std::size_t size() const override
  {
    INVARIANT(false, "Cannot take size of degenerate path storage");
  }

private:
  goto_modelt model;
  patht &private_peek() override
  {
    INVARIANT(false, "Cannot peek at degenerate path storage");
  }
  void private_pop() override
  {
    INVARIANT(false, "Cannot pop degenerate path storage");
  }
};

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
