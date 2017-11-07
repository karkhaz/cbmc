/*******************************************************************\

Module: Path Queue

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

/// \file
/// Saved path data structures

#include <iostream>

#include "path_queue.h"

path_queuet *path_queuet::make_queue(std::string type)
{
  if(type=="FIFO")
    return new path_fifot();
  else
  {
    std::cerr << "Unknown path queue type '" << type << "'.\n";
    abort();
  }
}
