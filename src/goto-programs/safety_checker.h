/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Safety Checker Interface

#ifndef CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H
#define CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H

// this is just an interface -- it won't actually do any checking!

#include <util/message.h>

#include "goto_trace.h"
#include "goto_functions.h"

class safety_checkert:public messaget
{
public:
  explicit safety_checkert(
    const namespacet &_ns);

  explicit safety_checkert(
    const namespacet &_ns,
    message_handlert &_message_handler);

  enum class resultt { SAFE, UNSAFE, ERROR };

  // check whether all assertions in goto_functions are safe
  // if UNSAFE, then a trace is returned

  virtual resultt operator()(
    const goto_functionst &goto_functions)=0;

  // this is the counterexample
  goto_tracet error_trace;

protected:
  // the namespace
  const namespacet &ns;
};

/// \brief The best of two results
inline safety_checkert::resultt operator||(
    safety_checkert::resultt const &r1,
    safety_checkert::resultt const &r2)
{
  return r1==safety_checkert::resultt::SAFE?safety_checkert::resultt::SAFE:
         r2==safety_checkert::resultt::SAFE?safety_checkert::resultt::SAFE:
         r1==safety_checkert::resultt::UNSAFE?safety_checkert::resultt::UNSAFE:
         r2==safety_checkert::resultt::UNSAFE?safety_checkert::resultt::UNSAFE:
         r1==safety_checkert::resultt::ERROR?safety_checkert::resultt::ERROR:
         r2==safety_checkert::resultt::ERROR?safety_checkert::resultt::ERROR:
         throw("Unknown enum value");
}

/// \brief The worst of two results
inline safety_checkert::resultt operator&&(
    safety_checkert::resultt const &r1,
    safety_checkert::resultt const &r2)
{
  return r1==safety_checkert::resultt::ERROR?safety_checkert::resultt::ERROR:
         r2==safety_checkert::resultt::ERROR?safety_checkert::resultt::ERROR:
         r1==safety_checkert::resultt::UNSAFE?safety_checkert::resultt::UNSAFE:
         r2==safety_checkert::resultt::UNSAFE?safety_checkert::resultt::UNSAFE:
         r1==safety_checkert::resultt::SAFE?safety_checkert::resultt::SAFE:
         r2==safety_checkert::resultt::SAFE?safety_checkert::resultt::SAFE:
         throw("Unknown enum value");
}

/// \brief The worst of two results
inline safety_checkert::resultt &operator&=(
    safety_checkert::resultt &a,
    safety_checkert::resultt const &b)
{
  a=a&&b;
  return a;
}

/// \brief The best of two results
inline safety_checkert::resultt &operator|=(
    safety_checkert::resultt &a,
    safety_checkert::resultt const &b)
{
  a=a||b;
  return a;
}
#endif // CPROVER_GOTO_PROGRAMS_SAFETY_CHECKER_H
