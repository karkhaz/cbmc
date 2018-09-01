/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include "goto_symex_state.h"
#include "symex_target_equation.h"

#include <util/options.h>
#include <util/cmdline.h>
#include <util/ui_message.h>
#include <util/invariant.h>

#include <memory>

/// \brief Storage for symbolic execution paths to be resumed later
///
/// This data structure supports saving partially-executed symbolic
/// execution \ref path_storaget::patht "paths" so that their execution can /// be halted and resumed later. The choice of which path should be
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

  /// \brief Data needed for path_storaget objects to make strategy decisions
  ///
  /// Different path exploration strategies need different information passed to
  /// them when they are constructed in order to decide which paths to resume
  /// next. Simple strategies (LIFO, FIFO etc.) don't need additional
  /// information, while more sophisticated strategies may require arguments
  /// from the command line, a reference to the goto-program, etc.
  ///
  /// This struct collects all this information in one place, so that when a new
  /// strategy needs a new parameter, it can simply be added to this struct. The
  /// alternative is to change the constructor for path_storaget and all of its
  /// subclasses every time we add a new strategy, which obfuscates the git
  /// history.
  struct strategy_contextt
  {
    strategy_contextt(messaget &log, const optionst &options)
      : log(log), options(options)
    {
    }

    messaget &log;
    const optionst &options;
  };

  explicit path_storaget(const strategy_contextt &ctx)
    : context(ctx)
  {
  }

  virtual ~path_storaget() = default;

  /// \brief Reference to the next path to resume
  patht &peek()
  {
    PRECONDITION(!empty());
    return private_peek();
  }

  /// \brief Clear all saved paths
  ///
  /// This is typically used because we want to terminate symbolic execution
  /// early. It doesn't matter too much in terms of memory usage since CBMC
  /// typically exits soon after we do that, however it's nice to have tests
  /// that check that the worklist is always empty when symex finishes.
  virtual void clear() = 0;

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

  /// \brief Callback for clients to notify this path_storaget that we have
  /// symbolically executed to the end of a path, and the path has been
  /// model-checked.
  ///
  /// This implementation does nothing. There is no need for clients to call
  /// this method if path_storaget::interested_in_path_termination() returns
  /// `false`.
  virtual void notify_path_terminated()
  {
  }

  /// \brief Is this path_storaget interested in path termination?
  ///
  /// If this method returns `true`, clients should call the
  /// path_storaget::notify_path_terminated() method whenever the client
  /// finishes symbolically executing a path.
  virtual bool interested_in_path_termination() const
  {
    return false;
  }

protected:
  const strategy_contextt &context;

private:
  // Derived classes should override these methods, allowing the base class to
  // enforce preconditions.
  virtual patht &private_peek() = 0;
  virtual void private_pop() = 0;
};

/// \brief LIFO save queue: depth-first search, try to finish paths
class path_lifot : public path_storaget
{
public:
  explicit path_lifot(const strategy_contextt &ctx)
    : path_storaget(ctx)
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<path_storaget::patht>::iterator last_peeked;
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief FIFO save queue: paths are resumed in the order that they were saved
class path_fifot : public path_storaget
{
public:
  explicit path_fifot(const strategy_contextt &ctx)
    : path_storaget(ctx)
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Hybrid breadth-then-depth search
class breadth_depth_path_storaget : public path_storaget
{
public:
  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;
  explicit breadth_depth_path_storaget(const strategy_contextt &ctx)
  : path_storaget(ctx),
    diameter(
      ctx.options.is_set("bdfs-diameter")
        ? ctx.options.get_unsigned_int_option("bdfs-diameter")
        : 8U),
    depth_list(),
    current_depth_queue(depth_list.end())
  {
  }

  virtual void notify_path_terminated() override;
  virtual bool interested_in_path_termination() const override
  {
    return true;
  }

protected:
  const unsigned diameter;
  std::list<patht> breadth_list;
  std::list<std::list<patht>> depth_list;
  std::list<std::list<patht>>::iterator current_depth_queue;
  std::list<patht>::iterator last_peeked;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Dummy class for clients who will not use path exploration
class degenerate_path_storaget : public path_storaget
{
public:
  explicit degenerate_path_storaget(const strategy_contextt &ctx)
    : path_storaget(ctx)
  {
  }

  void push(const patht &, const patht &) override
  {
    INVARIANT(false, "Cannot push to a degenerate_path_storaget");
  }
  std::size_t size() const override
  {
    INVARIANT(false, "Cannot take the size of a degenerate_path_storaget");
  }
  void clear() override
  {
    INVARIANT(false, "Cannot clear a degenerate_path_storaget");
  }

private:
  patht &private_peek() override
  {
    INVARIANT(false, "Cannot peek at a degenerate_path_storaget");
  }
  void private_pop() override
  {
    INVARIANT(false, "Cannot pop a degenerate_path_storaget");
  }
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
  std::unique_ptr<path_storaget> get(
    const std::string strategy,
    const path_storaget::strategy_contextt &ctx) const
  {
    auto found = strategies.find(strategy);
    INVARIANT(
      found != strategies.end(), "Unknown strategy '" + strategy + "'.");
    return found->second.second(ctx);
  }

  /// \brief add `paths` and `exploration-strategy` option, suitable to be
  /// invoked from front-ends.
  void
  set_path_strategy_options(const cmdlinet &, optionst &, messaget &) const;

protected:
  std::string default_strategy() const
  {
    return "lifo";
  }

  /// Map from the name of a strategy (to be supplied on the command line), to
  /// the help text for that strategy and a factory thunk returning a pointer to
  /// a derived class of path_storaget that implements that strategy.
  std::map<const std::string,
           std::pair<const std::string,
                     const std::function<std::unique_ptr<path_storaget>(
                       const path_storaget::strategy_contextt &ctx)>>>
    strategies;
};

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
