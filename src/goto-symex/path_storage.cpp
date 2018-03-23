/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include <cmath>
#include <sstream>

#include <goto-programs/goto_model.h>

#include <util/exit_codes.h>

// _____________________________________________________________________________
// path_lifo_function_penaltyt

void path_lifo_function_penaltyt::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &path : paths)
  {
    unsigned &freq = map[path.state.source.pc->source_location];
    ++freq;
  }
}

path_storaget::patht &path_lifo_function_penaltyt::private_peek()
{
  std::map<const irep_idt, unsigned> local_penalties = penalties;
  paths.sort([&local_penalties](
    const path_storaget::patht &p1, const path_storaget::patht &p2)
    {
      // It is correct for the comparison to be > rather than < because we want
      // the paths with the lowest location counts to go at the end. This is
      // because for LIFO, we're pulling paths from the end of the list rather
      // than the beginning.
      return local_penalties[p1.state.source.pc->source_location.get_function()] >
        local_penalties[p2.state.source.pc->source_location.get_function()];
    });
  last_peeked = paths.end();
  ++penalties[paths.back().state.source.pc->source_location.get_function()];
  --last_peeked;
  return paths.back();
}

void path_lifo_function_penaltyt::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_lifo_function_penaltyt::private_pop()
{
  PRECONDITION(last_peeked != paths.end());
  paths.erase(last_peeked);
  last_peeked = paths.end();
}

std::size_t path_lifo_function_penaltyt::size() const
{
  return paths.size();
}

// _____________________________________________________________________________
// path_lifo_location_penaltyt

void path_lifo_location_penaltyt::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &path : paths)
  {
    unsigned &freq = map[path.state.source.pc->source_location];
    ++freq;
  }
}

path_storaget::patht &path_lifo_location_penaltyt::private_peek()
{
  std::map<const source_locationt, unsigned> local_penalties = penalties;
  paths.sort([&local_penalties](
    const path_storaget::patht &p1, const path_storaget::patht &p2)
    {
      // It is correct for the comparison to be > rather than < because we want
      // the paths with the lowest location counts to go at the end. This is
      // because for LIFO, we're pulling paths from the end of the list rather
      // than the beginning.
      return local_penalties[p1.state.source.pc->source_location] >
        local_penalties[p2.state.source.pc->source_location];
    });
  last_peeked = paths.end();
  --last_peeked;
  ++penalties[paths.back().state.source.pc->source_location];
  return paths.back();
}

void path_lifo_location_penaltyt::push(
  const path_storaget::patht &next_instruction,
  const path_storaget::patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

void path_lifo_location_penaltyt::private_pop()
{
  PRECONDITION(last_peeked != paths.end());
  paths.erase(last_peeked);
  last_peeked = paths.end();
}

std::size_t path_lifo_location_penaltyt::size() const
{
  return paths.size();
}

// _____________________________________________________________________________
// path_lifot

void path_lifot::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &path : paths)
  {
    unsigned &freq = map[path.state.source.pc->source_location];
    ++freq;
  }
}

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

// _____________________________________________________________________________
// path_fifot

void path_fifot::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &path : paths)
  {
    unsigned &freq = map[path.state.source.pc->source_location];
    ++freq;
  }
}

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

// _____________________________________________________________________________
// progressive_path_fifot

void progressive_path_fifot::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &jump : jumps)
  {
    unsigned &freq = map[jump.state.source.pc->source_location];
    ++freq;
  }
  for(const auto &next : nexts)
  {
    unsigned &freq = map[next.state.source.pc->source_location];
    ++freq;
  }
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

// _____________________________________________________________________________
// high_coverage_path_storaget

high_coverage_path_storaget::high_coverage_path_storaget(
  const abstract_goto_modelt &model, messaget &message)
  : path_storaget(model, message),
    transitive_blocks(model),
    paths(),
    last_peeked(paths.end())
{
  forall_goto_functions(f_it, model.get_goto_functions())
    forall_goto_program_instructions(i_it, f_it->second.body)
      if(!i_it->source_location.is_nil())
        all_sloc.insert(i_it->source_location);
}

void high_coverage_path_storaget::push(
  const patht &next_instruction,
  const patht &jump_target)
{
  paths.push_back(next_instruction);
  paths.push_back(jump_target);
}

std::size_t high_coverage_path_storaget::size() const
{
  return paths.size();
}

void high_coverage_path_storaget::private_pop()
{
  PRECONDITION(last_peeked != paths.end());
  paths.erase(last_peeked);
  last_peeked = paths.end();
}

void high_coverage_path_storaget::get_location_map(
  std::map<source_locationt, unsigned> &map)
{
  for(const auto &path : paths)
  {
    unsigned &freq = map[path.state.source.pc->source_location];
    ++freq;
  }
}

path_storaget::patht &high_coverage_path_storaget::private_peek()
{
  unsigned most_visited = 0;
  for(const auto &pair : frequency)
    if(pair.second > most_visited)
      most_visited = pair.second;

  // Each location has a score (higher scores are better) based on how
  // many times we've already executed that location. The score of a
  // path is the sum of the scores of all the locations the path might
  // execute.
  std::map<source_locationt, long> score;
  for(const auto &sloc : all_sloc)
  {
    const auto found = frequency.find(sloc);
    if(found == frequency.end())
      score[sloc] = most_visited;
    else
      score[sloc] = most_visited - found->second;
  }

  paths.sort([this, &score](
    const path_storaget::patht &p1, const path_storaget::patht &p2)
    {
      goto_programt::const_targett t1;
      if(p1.state.has_saved_jump_target)
        t1 = p1.state.source.pc->get_target();
      else
      {
        DATA_INVARIANT(
          p1.state.has_saved_next_instruction,
          "A saved path at " + p1.state.source.pc->source_location.as_string() +
            " has neither a saved_next_instruction nor saved_jump_target");
        t1 = p1.state.source.pc;
        ++t1;
      }

      goto_programt::const_targett t2;
      if(p2.state.has_saved_jump_target)
        t2 = p2.state.source.pc->get_target();
      else
      {
        DATA_INVARIANT(
          p2.state.has_saved_next_instruction,
          "A saved path at " + p2.state.source.pc->source_location.as_string() +
            " has neither a saved_next_instruction nor saved_jump_target");
        t2 = p2.state.source.pc;
        ++t2;
      }

      double path_score[2] = {0};
      unsigned unexplored[2] = {0};
      int cnt = 0;
      for(const auto &branch : {t1->source_location, t2->source_location})
      {
        for(const auto &potential_line : transitive_blocks.line_map[branch])
        {
          path_score[cnt] += score[potential_line];
          if(frequency[potential_line] == 0)
            ++unexplored[cnt];
        }
        ++cnt;
      }

      return path_score[0] < path_score[1];
    });

  last_peeked = paths.begin();
  return paths.front();
}

void high_coverage_path_storaget::notify_executing(
  const goto_programt::instructiont &instruction)
{
  if(!instruction.source_location.is_nil())
    ++frequency[instruction.source_location];
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
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<path_fifot>(new path_fifot(mod, mess));
         }}},
       {"progressive-fifo",
        {" progressive-fifo             prefer to make progress: all goto\n"
         "                              targets are popped in fifo order,\n"
         "                              followed by all next instructions\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<progressive_path_fifot>(
             new progressive_path_fifot(mod, mess));
         }}},
       {"coverage",
        {" coverage                     prefer paths that lead to code that\n"
         "                              we haven't executed as many times\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<high_coverage_path_storaget>(
             new high_coverage_path_storaget(mod, mess));
         }}},
       {"lifo",
        {" lifo                         Depth-first path exploration\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<path_lifot>(new path_lifot(mod, mess));
         }}},
       {"lifo-location-penalty",
        {" lifo-location-penalty        Depth-first path exploration with\n"
         "                              a penalty for locations already\n"
         "                              popped\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<path_lifo_location_penaltyt>(
             new path_lifo_location_penaltyt(mod, mess));
         }}},
       {"lifo-function-penalty",
        {" lifo-function-penalty        Depth-first path exploration with\n"
         "                              a penalty for functions already\n"
         "                              popped\n",
         // NOLINTNEXTLINE(whitespace/braces)
         [](const abstract_goto_modelt &mod, messaget &mess) {
           return std::unique_ptr<path_lifo_function_penaltyt>(
             new path_lifo_function_penaltyt(mod, mess));
         }}}
      })
{
}
