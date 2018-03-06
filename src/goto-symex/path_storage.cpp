/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include <sstream>

#include <util/exit_codes.h>

path_storaget::patht &path_fifot::private_peek()
{
  return paths.front();
}

void path_fifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_fifot::private_pop()
{
  paths.pop_front();
}

std::size_t path_fifot::size() const
{
  return paths.size();
}

path_storaget::patht &progressive_path_fifot::private_peek()
{
  if(jumps.empty())
  {
    INVARIANT(
      !pop_next,
      "Cannot peek at next instruction: you must pop the instruction you had "
      "previously peeked at before peeking at a new one");
    pop_next = true;
    return nexts.front();
  }
  else
  {
    INVARIANT(
      !pop_next,
      "Cannot peek at jump target: you must pop the instruction you had "
      "previously peeked at before peeking at a new one");
    return jumps.front();
  }
  UNREACHABLE;
}

void progressive_path_fifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  nexts.push_back(next_instruction);
  jumps.push_back(jump_target);
}

void progressive_path_fifot::private_pop()
{
  // If the last path we peeked at was on the next queue, then that's
  // the path we should pop. This is the case _even if_ a path was added
  // to the jump queue in the mean time.
  if(pop_next)
  {
    pop_next = false;
    INVARIANT(
      !nexts.empty(),
      "We should be popping the nexts queue, but the nexts queue is empty");
    nexts.pop_front();
  }
  else if(!jumps.empty())
    jumps.pop_front();
  else
    INVARIANT(
      nexts.empty(),
      "Nexts should be empty if both `pop_next` is unset and jumps is empty");
}

std::size_t progressive_path_fifot::size() const
{
  return jumps.size() + nexts.size();
}

std::string path_strategy_choosert::show_strategies() const
{
  std::stringstream ss;
  for(auto &pair : strategies)
    ss << pair.second.first;
  return ss.str();
}

void path_strategy_choosert::set_path_strategy_options(
  const cmdlinet &cmdline,
  optionst &options,
  messaget &message) const
{
  if(cmdline.isset("paths"))
  {
    options.set_option("paths", true);
    std::string strategy = cmdline.get_value("paths");
    if(!is_valid_strategy(strategy))
    {
      message.error() << "Unknown strategy '" << strategy
                      << "'. Pass the --show-symex-strategies flag to list "
                         "available strategies."
                      << message.eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option("exploration-strategy", strategy);
  }
  else
    options.set_option("exploration-strategy", default_strategy());
}

path_strategy_choosert::path_strategy_choosert()
  : strategies(
      {{"fifo",
        {" fifo                         next instruction is pushed before\n"
         "                              goto target; paths are popped in\n"
         "                              first-in, first-out order\n",
         []() { // NOLINT(whitespace/braces)
           return std::unique_ptr<path_fifot>(new path_fifot());
         }}},
       {"progressive-fifo",
        {" progressive-fifo             prefer to make progress: all goto\n"
         "                              targets are popped in fifo order,\n"
         "                              followed by all next instructions\n",
         []() { // NOLINT(whitespace/braces)
           return std::unique_ptr<progressive_path_fifot>(
             new progressive_path_fifot());
         }}}})
{
}
