/*******************************************************************\

Module: Path Storage

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "path_storage.h"

#include <cmath>
#include <sstream>

#include <goto-programs/goto_model.h>

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
  std::map<source_locationt, double> score;
  for(const auto &sloc : all_sloc)
  {
    const auto found = frequency.find(sloc);
    if(found == frequency.end())
      score[sloc] = std::pow(1.1, most_visited);
    else
      score[sloc] = std::pow(1.1, most_visited - found->second);
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

  last_peeked = paths.end();
  --last_peeked;
  return paths.back();
}

void high_coverage_path_storaget::notify_executing(
  const goto_programt::instructiont &instruction)
{
  if(!instruction.source_location.is_nil())
    ++frequency[instruction.source_location];
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
         }}}})
{
}
