/*******************************************************************\

Module: Transitive Blocks

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "transitive_blocks.h"

#include "goto_program2code.h"

transitive_blockst::transitive_blockst(const abstract_goto_modelt &model)
  : model(model)
{
  transitive_blockst::funs2linest funs2lines;
  compute_transitive_function_lines(funs2lines);

  for(const auto &pair : model.get_goto_functions().function_map)
    compute_blocks(pair.first, pair.second.body, funs2lines);
}

void transitive_blockst::compute_blocks(
  const irep_idt &fun_name,
  const goto_programt &goto_program,
  const funs2linest &funs2lines)
{
  code_blockt block;
  symbol_tablet st_copy(model.get_symbol_table());
  std::list<irep_idt> local_static, type_names;
  const std::unordered_set<irep_idt, irep_id_hash> typedef_names;
  std::set<std::string> system_headers;
  goto_program2codet g2c(
    fun_name,
    goto_program,
    st_copy,
    block,
    local_static,
    type_names,
    typedef_names,
    system_headers);
  g2c();
  std::set<source_locationt> tmp;
  transitive_of_nested(block, funs2lines, tmp);

  // At this point, line_map maps from a source line that begins a block
  // to all the source locations transitively touched by running the
  // code inside that block. However, once that block finishes, the
  // _next_ blocks in the surrounding scope will also be executed. Thus
  // we should add the transitive locations of all successor blocks to
  // each block. i.e. in the code
  //
  // 19 if(x)
  // 20   y();
  // 21 else
  // 22   z();
  // 23 while(x)
  // 24   w();
  //
  // we want to have the following:
  //
  // line_map[19] = {19} U line_map[20] U line_map[23]
  // line_map[20] =        line_map[20] U line_map[23]
  // line_map[21] = {21} U line_map[22] U line_map[23]
  // line_map[22] =        line_map[22] U line_map[23]
  // line_map[23] = {23} U line_map[24]
  //
  // but we don't yet have line_map[23] unioned onto the lines of the
  // ifelse-block since the while block is a successor of the ifelse rather than
  // a nested block. Fix that here.

  tmp.clear();
  transitive_of_successors(block, tmp);
}

void transitive_blockst::transitive_of_successors(
  const codet &code,
  std::set<source_locationt> &future_lines)
{
  source_locationt my_location;
  if(!location_of(code, my_location))
    return;

  // Ifthenelse is a special case. The siblings are mutually exclusive, so the
  // lines reachable from the else case should not be propagated to the then
  // case. So recurse into each case with a separate copy of the future lines.
  if(code.get_statement() == ID_ifthenelse)
  {
    const code_ifthenelset &itl = to_code_ifthenelse(code);
    std::set<source_locationt> then_futures(future_lines);
    transitive_of_successors(itl.then_case(), then_futures);

    std::set<source_locationt> else_futures(future_lines);
    if(itl.has_else_case())
      transitive_of_successors(itl.else_case(), else_futures);

    future_lines.insert(then_futures.begin(), then_futures.end());
    future_lines.insert(else_futures.begin(), else_futures.end());
  }
  // For every other sort of code, walk through the operands backwards
  // and accumulate future lines as we go along. The closer we get to
  // the beginning of the code block, the more future lines there are.
  else
  {
    for(auto rit = code.operands().rbegin(); rit != code.operands().rend();
        ++rit)
    {
      if(rit->id() == ID_code)
        transitive_of_successors(to_code(*rit), future_lines);
    }
  }

  line_map[my_location].insert(future_lines.begin(), future_lines.end());

  future_lines.insert(my_location);
}

void transitive_blockst::transitive_of_nested(
  const codet &code,
  const funs2linest &funs2lines,
  std::set<source_locationt> &my_locations)
{
  // Try to get a location for this code block. If the block is a while,
  // ifthenelse, etc. then it probably won't have a source location, but one of
  // its booleans or some other nested member probably will.
  source_locationt my_location;
  if(!location_of(code, my_location))
    return;

  if(code.get_statement() == ID_function_call)
  {
    const code_function_callt &call = to_code_function_call(code);
    const irep_idt &call_name = call.function().get("identifier");
    const auto found = funs2lines.find(call_name);
    if(found != funs2lines.end())
      my_locations.insert(
        funs2lines.at(call_name).begin(), funs2lines.at(call_name).end());
  }

  for(const auto &op : code.operands())
  {
    if(op.id() != ID_code)
      continue;
    const codet inner = to_code(op);
    std::set<source_locationt> tmp;
    transitive_of_nested(inner, funs2lines, tmp);
    my_locations.insert(tmp.begin(), tmp.end());
  }
  my_locations.insert(my_location);
  line_map[my_location].insert(my_locations.begin(), my_locations.end());
}

void transitive_blockst::compute_transitive_function_lines(
  transitive_blockst::funs2linest &transitive_function_lines)
{
  std::unordered_map<irep_idt, std::set<source_locationt>, irep_id_hash>
    original_lines;
  forall_goto_functions(f_it, model.get_goto_functions())
  {
    std::set<source_locationt> &line_set = original_lines[f_it->first];
    forall_goto_program_instructions(it, f_it->second.body)
      line_set.insert(it->source_location);
  }
  forall_goto_functions(f_it, model.get_goto_functions())
  {
    std::list<irep_idt> worklist = {f_it->first};
    transitive_function_lines[f_it->first].insert(
      original_lines[f_it->first].begin(), original_lines[f_it->first].end());
    std::unordered_set<irep_idt, irep_id_hash> seen = {f_it->first};
    while(!worklist.empty())
    {
      const irep_idt &fun_name = worklist.front();
      if(fun_name.empty())
        continue;
      const auto explore_it =
        model.get_goto_functions().function_map.find(fun_name);
      INVARIANT(
        explore_it != model.get_goto_functions().function_map.end(),
        "Could not find function '" + std::string(fun_name.c_str()) +
          "' in function map");
      forall_goto_program_instructions(it, explore_it->second.body)
      {
        if(!it->is_function_call())
          continue;
        const code_function_callt &call = to_code_function_call(it->code);
        const irep_idt &call_name = call.function().get("identifier");
        transitive_function_lines[f_it->first].insert(
          original_lines[call_name].begin(), original_lines[call_name].end());
        const auto found = seen.find(call_name);
        if(found == seen.end())
        {
          seen.insert(call_name);
          worklist.push_back(call_name);
          INVARIANT(
            original_lines.find(call_name) != original_lines.end(),
            "Could not find function '" + std::string(call_name.c_str()) +
              "' during traversal of program");
        }
      }
      worklist.pop_front();
    }
  }
}

bool transitive_blockst::location_of(
  const exprt &expr,
  source_locationt &location) const
{
  if(!expr.source_location().is_nil())
  {
    location = expr.source_location();
    return true;
  }
  for(const auto &op : expr.operands())
  {
    if(op.is_nil())
      continue;
    if(!op.source_location().is_nil())
    {
      location = op.source_location();
      return true;
    }
    // DFS.
    if(location_of(op, location))
      return true;
  }
  return false;
}

void transitive_blockst::show_blocks(
  const abstract_goto_modelt &model,
  messaget &message)
{
  for(const auto &pair : model.get_goto_functions().function_map)
  {
    code_blockt block;
    symbol_tablet st_copy(model.get_symbol_table());
    std::list<irep_idt> local_static, type_names;
    const std::unordered_set<irep_idt, irep_id_hash> typedef_names;
    std::set<std::string> system_headers;
    goto_program2codet g2c(
      pair.first,
      pair.second.body,
      st_copy,
      block,
      local_static,
      type_names,
      typedef_names,
      system_headers);
    g2c();
    message.status() << block.pretty() << message.eom;
  }
}

void transitive_blockst::show_transitive_blocks(
  const abstract_goto_modelt &model,
  messaget &message)
{
  transitive_blockst::transitive_linest transitive_lines;
  transitive_blockst blocks(model);
  for(const auto &pair : blocks.line_map)
  {
    if(pair.first.is_nil())
      continue;
    std::list<source_locationt> locs;
    // Consistent output from run to run
    locs.insert(locs.end(), pair.second.begin(), pair.second.end());
    locs.sort();
    for(const auto &loc : locs)
    {
      if(!(loc.is_nil() || loc.get_file() == "<built-in-additions>" ||
           pair.first.get_file() == "<built-in-additions>"))
        message.status() << pair.first << " -> " << loc << message.eom;
    }
  }
}
