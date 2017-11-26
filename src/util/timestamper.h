/// \file timestamper.h
/// \brief Emit timestamps
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_UTIL_TIMESTAMPER_H
#define CPROVER_UTIL_TIMESTAMPER_H

#include <chrono>
#include <sstream>

#include "invariant.h"

#define OPT_TIMESTAMP "(timestamp):"

#define HELP_TIMESTAMP \
" --timestamp <monotonic|wall> print microsecond-precision timestamps.\n" \
"                              monotonic: timestamps are relative to an\n" \
"                              arbitrary start point, guaranteed to " \
"increase,\n" \
"                              formatted as s.u where 's' increases every\n" \
"                              second and 'u' is a zero-padded six-digit\n" \
"                              microsecond counter.\n" \
"                              wall: timestamps use the format\n" \
"                              %Y-%m-%dT%H:%M:%S.u where 'u' is a six-digit\n" \
"                              zero-padded microsecond counter. Timestamp " \
"may\n" \
"                              decrease on daylight saving time changes\n" \

class timestampert
{
public:
  enum class clockt { NONE, MONOTONIC, WALL_CLOCK };
  timestampert() {}
  virtual ~timestampert() {}
  virtual const std::string stamp(const std::string &message) const
  {
    return message;
  }
  static const timestampert *const make(clockt clock_type);
};


class monotonic_timestampert : public timestampert
{
public:
  virtual const std::string stamp(const std::string &message) const override;
};

class wall_clock_timestampert : public timestampert
{
  virtual const std::string stamp(const std::string &message) const override;
};

#endif
