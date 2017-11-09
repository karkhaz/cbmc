/// \file path_queue.h
/// \brief Data structures to hold saved symex paths
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_QUEUE_H
#define CPROVER_GOTO_SYMEX_PATH_QUEUE_H

#include "symex_target_equation.h"
#include "goto_symex_state.h"

struct branch_pointt
{
  symex_target_equationt equation;
  goto_symex_statet state;

  explicit branch_pointt(
      const symex_target_equationt &e,
      const goto_symex_statet &s):
    equation(e), state(s, &equation)
  {}

  explicit branch_pointt(const branch_pointt &other):
    equation(other.equation),
    state(other.state, &equation)
  { };
};

class path_queuet
{
public:
  virtual branch_pointt &get()=0;
  virtual void put(branch_pointt &bp)=0;
  virtual void rm_front()=0;
  virtual std::size_t size()=0;
  virtual std::list<branch_pointt> &internal()=0;
  bool empty(){ return size()==0; };
  static path_queuet *make_queue(std::string type);
  virtual ~path_queuet(){};
};

class path_fifot: public path_queuet
{
public:
  path_fifot(){}
  branch_pointt &get(){ return list.front(); }
  void put(branch_pointt &bp){ list.push_back(bp); }
  void rm_front(){ list.pop_front(); }
  std::size_t size(){ return list.size(); }
  std::list<branch_pointt> &internal(){ return list; };
private:
  std::list<branch_pointt> list;
};

#if 0
class path_unique_targett: public path_queuet
{
public:
  unique_targett(){}
  branch_pointt &get(){ return *next(); }
  void put(branch_pointt &bp){ list.push_back(bp); }
  void rm_front(){ list.erase(next()); }
  std::size_t size(){ return list.size(); }
  std::list<branch_pointt> &internal(){ return list; };
private:
  10k
  std::list<branch_pointt> list;
  irep_idt last_function;
  bpit next();
};
#endif

class path_local_advancet: public path_queuet
{
public:
  path_local_advancet():
    last_function("")
  {}
  branch_pointt &get(){ return *next(); }
  void put(branch_pointt &bp){ list.push_back(bp); }
  void rm_front(){ list.erase(next()); }
  std::size_t size(){ return list.size(); }
  std::list<branch_pointt> &internal(){ return list; };
private:
  typedef std::list<branch_pointt>::iterator bpit;
  std::list<branch_pointt> list;
  irep_idt last_function;
  bpit next();
};

#endif // CPROVER_SYMEX_PATH_QUEUE_H
