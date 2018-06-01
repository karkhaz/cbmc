/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include "goto_symex.h"

#include <sstream>

#include <util/exit_codes.h>
#include <util/make_unique.h>

// _____________________________________________________________________________
// path_lifot

path_storaget::patht &path_lifot::private_peek()
{
  last_peeked = paths.end();
  --last_peeked;
  return paths.back();
}

void path_lifot::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_lifot::private_pop()
{
  PRECONDITION(last_peeked != paths.end());
  paths.erase(last_peeked);
  last_peeked = paths.end();
}

std::size_t path_lifot::size() const
{
  return paths.size();
}

void path_lifot::clear()
{
  paths.clear();
}

// _____________________________________________________________________________
// path_fifot

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

void path_fifot::clear()
{
  paths.clear();
}

// _____________________________________________________________________________
// path_end_mergert

void path_end_mergert::customise_goto_symext(goto_symext &symex)
{
  if(switch_to_path_merging)
  {
    context.log.status() << "Switching to path merging" << context.log.eom;
    switch_to_path_merging = false;
    symex.doing_path_exploration = false;
  }
}

void path_end_mergert::notify_path_completion()
{
  // Needs to be one less than merge_depth, since bmct does one more pop after
  // this method returns
  if(size() > merge_depth - 1)
  {
    for(int i = 0; i < merge_depth - 1; ++i)
    {
      peek();
      pop();
    }
    peek();

    switch_to_path_merging = true;
  }
}

// _____________________________________________________________________________
// path_strategy_choosert

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

    if(cmdline.isset("end-merge-depth"))
    {
      if(strategy != "lifo-end-merge")
      {
        message.error()
          << "`--end-merge-depth` must be used with `--paths lifo-end-merge`."
          << message.eom;
        exit(CPROVER_EXIT_USAGE_ERROR);
      }
      if(cmdline.isset("end-merge-depth"))
        options.set_option(
          "end-merge-depth", cmdline.get_value("end-merge-depth"));
      else
        options.set_option("end-merge-depth", 4U);
    }
  }
  else
    options.set_option("exploration-strategy", default_strategy());
}

path_strategy_choosert::path_strategy_choosert()
  : strategies(
      {{"lifo",
        {" lifo                         next instruction is pushed before\n"
         "                              goto target; paths are popped in\n"
         "                              last-in, first-out order. Explores\n"
         "                              the program tree depth-first.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<path_lifot>(ctx);
         }}},
       {"lifo-end-merge",
        {" lifo-end-merge               like lifo, but does path merging\n"
         "                              at the end of each path.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<path_end_mergert>(ctx);
         }}},
       {"fifo",
        {" fifo                         next instruction is pushed before\n"
         "                              goto target; paths are popped in\n"
         "                              first-in, first-out order. Explores\n"
         "                              the program tree breadth-first.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<path_fifot>(ctx);
         }}}})
{
}
