/*******************************************************************\

Module: Path Queue

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

/// \file
/// Saved path data structures

#include <algorithm>
#include <iostream>

#include "path_queue.h"

path_queuet *path_queuet::make_queue(std::string type)
{
  if(type=="FIFO")
    return new path_fifot();
  else if(type=="local-advance")
    return new path_local_advancet();
  else
  {
    std::cerr << "Unknown path queue type '" << type << "'.\n";
    abort();
  }
}

path_local_advancet::bpit path_local_advancet::next()
{
  std::vector<irep_idt> fun_order;
  std::map<irep_idt, unsigned> fun_lines;
  for(auto &bp : list)
  {
    irep_idt fun=bp.state.source.pc->source_location.get_function();
    unsigned line=std::stoul(
        bp.state.source.pc->source_location.get_line().c_str());
    auto pair=fun_lines.find(fun);
    if(pair==fun_lines.end())
    {
      std::cerr << "Adding " << fun << " at line " << line << "\n";
      fun_order.push_back(fun);
      fun_lines.emplace(fun, line);
    }
    else if(line>pair->second)
      std::cerr << "Updating " << fun << " with line " << line << "\n";
      pair->second=line;
  }
  irep_idt next_function;
  auto found=std::find(fun_order.begin(), fun_order.end(), last_function);
  if(found==fun_order.end()||found+1==fun_order.end())
  {
    next_function=*fun_order.begin();
    std::cerr << "POP: Wrapping around to " << next_function << ", were on "
      << last_function << " with funs size " << fun_order.size() << "\n";
  }
  else
  {
    next_function=*(found+1);
    std::cerr << "POP: Starting with " << next_function << ", were on "
      << last_function << " with funs size " << fun_order.size() << "\n";
  }
  last_function=next_function;
  auto target_pair=fun_lines.find(next_function);
  irep_idt target_line(std::to_string(target_pair->second));
  bpit target_bp=std::find_if(list.begin(), list.end(),
      [&target_line, &next_function](branch_pointt const& bp)
      {
        return bp.state.source.pc->
                  source_location.get_function()==next_function&&
               bp.state.source.pc->
                  source_location.get_line()==target_line;
      });
  if(target_bp!=list.end())
  {
    std::cerr << "POP: returning target\n";
    return target_bp;
  }
  else
  {
    std::cerr << "POP: returning begin\n";
    return list.begin();
  }
}
