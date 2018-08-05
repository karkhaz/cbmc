/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include "goto_symex.h"

#include <sstream>

#include <util/exit_codes.h>
#include <util/make_unique.h>
#include <util/string2int.h>

// _____________________________________________________________________________
// breadth_depth_path_storaget

inline void breadth_depth_path_storaget::notify_path_terminated()
{
  if(empty())
    return;
  do
  {
    ++current_depth_queue;
    if(current_depth_queue == depth_list.end())
      current_depth_queue = depth_list.begin();
  } while(current_depth_queue->empty());
  last_peeked = current_depth_queue->end();
}

path_storaget::patht &breadth_depth_path_storaget::private_peek()
{
  INVARIANT(
    depth_list.empty() || current_depth_queue != depth_list.end(),
    "We have paths to explore DFS, but no pointer to which path to start with");

  if(depth_list.empty())
    return breadth_list.front();

  INVARIANT(
    last_peeked == current_depth_queue->end(),
    "Should have popped or notify_path_terminated() before peeking");

  --last_peeked;
  return current_depth_queue->back();
}

void breadth_depth_path_storaget::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  INVARIANT(
    depth_list.empty() || current_depth_queue != depth_list.end(),
    "We have paths to explore DFS, but no pointer to which path to start with");

  source_locationt to_pop;

  if(depth_list.empty())
  {
    if(!breadth_list.empty())
      to_pop = breadth_list.back().state.source.pc->source_location;
    breadth_list.push_back(next_instruction);
    breadth_list.push_back(jump_target);
  }
  else
  {
    current_depth_queue->push_back(next_instruction);
    current_depth_queue->push_back(jump_target);
  }

  if(breadth_list.size() > diameter)
  {
    for(const auto &path : breadth_list)
    {
      std::list<patht> tmp;
      tmp.push_back(path);
      depth_list.push_back(tmp);
      context.log.debug()
        << "DFS start point: " << path.state.saved_target->source_location
        << context.log.eom;
    }
    // The path that led to next_instruction and jump_target being pushed is
    // currently the third-last item in breadth_list (the last and second-last
    // items are the two arguments to this method). We've just transferred
    // breadth_list into depth_list, but we need to ensure that when private_pop
    // is called, it actually pops the correct path from depth_list.
    std::list<std::list<patht>>::iterator tmp = depth_list.end();
    std::advance(tmp, -3);
    last_peeked = tmp->begin();
    INVARIANT(
      last_peeked->state.source.pc->source_location == to_pop,
      "Expected last_peeked to point to the precursor of next_instruction "
      "and jump_target");

    // Meanwhile, when we peek, we should go through all the subtrees in a
    // round-robin fashion.
    current_depth_queue = depth_list.begin();

    // From here onward, breadth_list will never be used.
    breadth_list.clear();
  }
}

void breadth_depth_path_storaget::private_pop()
{
  INVARIANT(
    depth_list.empty() || current_depth_queue != depth_list.end(),
    "We have paths to explore DFS, but no pointer to which path to start with");

  if(depth_list.empty())
    breadth_list.pop_front();
  else
  {
    INVARIANT(
      last_peeked != current_depth_queue->end(),
      "Must peek immediately before popping");
    current_depth_queue->erase(last_peeked);
    last_peeked = current_depth_queue->end();
  }
}

std::size_t breadth_depth_path_storaget::size() const
{
  INVARIANT(
    depth_list.empty() || current_depth_queue != depth_list.end(),
    "We have paths to explore DFS, but no pointer to which path to start with");

  if(depth_list.empty())
    return breadth_list.size();

  std::size_t total = 0;
  for(const auto &paths : depth_list)
    total += paths.size();
  return total;
}

void breadth_depth_path_storaget::clear()
{
  breadth_list.clear();
  depth_list.clear();
  current_depth_queue = depth_list.end();
}

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

  if(cmdline.isset("bdfs-diameter"))
  {
    if(!cmdline.isset("paths")
    || options.get_option("exploration-strategy") != "hybrid-bdfs")
    {
      message.error() << "`--bdfs-diameter` can only be passed when passing "
                         "`--paths hybrid-bdfs`."
                      << message.eom;
      exit(CPROVER_EXIT_USAGE_ERROR);
    }
    options.set_option(
      "bdfs-diameter",
      unsafe_string2unsigned(cmdline.get_value("bdfs-diameter")));
  }
}

path_strategy_choosert::path_strategy_choosert()
  : strategies(
      {{"hybrid-bdfs",
        {" hybrid-bdfs                  explore breadth-first until we have\n"
         "                              N saved paths, at which point explore\n"
         "                              depth-first from each of those paths\n"
         "                              in round-robin order. N defaults to 8\n"
         "                              and can be specified with the flag\n"
         "                              --bdfs-diameter N.\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const path_storaget::strategy_contextt &ctx) {
           return util_make_unique<breadth_depth_path_storaget>(ctx);
         }}},
       {"lifo",
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
