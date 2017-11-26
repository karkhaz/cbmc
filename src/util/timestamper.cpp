/*******************************************************************\

Module: Timestamps

Author: Kareem Khazem <karkhaz@karkhaz.com>

\*******************************************************************/

#include "timestamper.h"

const timestampert *const timestampert::make(
    timestampert::clockt clock_type)
{
  switch(clock_type)
  {
    case timestampert::clockt::NONE:
      return new timestampert();
    case timestampert::clockt::MONOTONIC:
      return new monotonic_timestampert();
    case timestampert::clockt::WALL_CLOCK:
      return new wall_clock_timestampert();
  }
  UNREACHABLE;
}

const std::string monotonic_timestampert::stamp(
    const std::string &message) const
{
  std::stringstream ss;
  std::chrono::time_point<std::chrono::steady_clock,
                          std::chrono::microseconds> time_stamp =
    std::chrono::time_point_cast<std::chrono::microseconds>(
        std::chrono::steady_clock::now());

  auto cnt = time_stamp.time_since_epoch().count();
  div_t divmod = div(cnt, 1000000);
  char u_seconds_fmt[7];
  std::snprintf(u_seconds_fmt, sizeof(u_seconds_fmt), "%06d", divmod.rem);

  ss << divmod.quot << "." << u_seconds_fmt << " " << message;
  return ss.str();
}

#define TIMESTAMPERT_WALL_FORMAT "%Y-%m-%dT%H:%M:%S."

/// The length of the string "2017-08-22T18:32:53." plus null byte
#define TIMESTAMPERT_WALL_FORMAT_BUFFER_LENGTH 21

const std::string wall_clock_timestampert::stamp(
    const std::string &message) const
{
  std::chrono::time_point<std::chrono::system_clock,
                          std::chrono::microseconds> time_stamp =
    std::chrono::time_point_cast<std::chrono::microseconds>(
        std::chrono::system_clock::now());

  unsigned u_seconds=time_stamp.time_since_epoch().count() % 1000000;
  char u_seconds_fmt[7];
  std::snprintf(u_seconds_fmt, sizeof(u_seconds_fmt), "%06u", u_seconds);

  std::time_t tt=std::chrono::system_clock::to_time_t(time_stamp);
  std::tm *local=std::localtime(&tt);
  char time_buf[TIMESTAMPERT_WALL_FORMAT_BUFFER_LENGTH];
  int chars=std::strftime(time_buf,
                          TIMESTAMPERT_WALL_FORMAT_BUFFER_LENGTH,
                          TIMESTAMPERT_WALL_FORMAT,
                          local);
  INVARIANT(chars == TIMESTAMPERT_WALL_FORMAT_BUFFER_LENGTH - 1,
      "buffer not long enough to hold the string "
      "'2017-08-22T18:32:53.' plus null byte");

  std::stringstream ss;
  ss << time_buf << u_seconds_fmt << " " << message;
  return ss.str();
}
