#!/usr/bin/env python3
#
# Create test.desc files from the test.in files in each directory.
#
# Author: Kareem Khazem <karkhaz@karkhaz.com>
#
# Several regression test directories test the functionality of CBMC's --paths
# option with various path exploration strategies. They ensure that paths are
# pushed onto and popped off of the workqueue in the right order, and that the
# verification result is as expected along each path.
#
# The test.desc files for these tests are cumbersome to write manually, since
# they involve very long multi-line regexes, and so are generated using this
# script. This script reads a test.in file, and interprets all lines that occur
# beneath the string 'Test that the following happens in order:'. The
# interpreted lines are turned into a regular expression, which is inserted
# below all other patterns that the user specifies in the test.in file.
# test.in. All other lines are preserved. The result of this is written to
# test.desc, ready for the test suite to be run over it.


import os
import os.path
import re
import sys


"""
Return an array containing the sections of a .desc file. The array will have up
to four elements: the 3 sections delimited by the two "--"s, and a sequence of
instructions to be converted to a regex delimited by the string 'Test that the
following happens in order:'.
"""
def get_desc_sections(in_file):
    seen_activate = False
    ignore_activate = False
    sections = [[]]
    section = 0
    with open(in_file) as f:
        cnt = 0
        for line in f:
            cnt += 1
            line = line.strip()
            if re.match("^--$", line):
                section += 1
                sections.append([])
            elif re.match("^activate-multi-line-match$", line):
                seen_activate = True
                sections[section].append(line)
            elif re.match("^ignore-multi-line-match$", line):
                ignore_activate = True
            elif re.match("Test that the following happens in order:", line):
                if section != 2:
                    print("%s:%d:0: error: Found the string 'Test that the "
                          "following happens in order' in section %d, should "
                          "be in section 2 (zero-indexed)" %
                          (in_file, cnt, section), file=sys.stderr)
                    exit(1)
                section += 1
                sections.append([])
            else:
                sections[section].append(line)
    if not (seen_activate or ignore_activate):
        print("The file '{file}' does not activate multi-line match. To "
              "disable this warning, add 'activate-multi-line-match' to "
              "the fourth line of that file, or write the string "
              "'ignore-multi-line-match' in the comment section at the "
              "bottom of the file.".format(file=in_file), file=sys.stderr)
    return sections


"""
Return a Perl regular expression that matches a log file that contains the
sequence of events in `command_list`.
"""
def interpret(command_list, in_file, offset):
    ret = ""
    end = False
    ok = True
    for line in command_list:
        offset += 1
        if end:
            print("%s:%d:0: error: Trailing instructions after 'end'"
                  % (in_file, offset), file=sys.stderr)
            exit(1)

        m = re.match(r"^$", line)
        if m:
            continue

        m = re.match(r"^//.*$", line)
        if m:
            continue

        m = re.match(r"^execute line (?P<l>\d+)$", line)
        if m:
            ret += ("BMC at file[^\\n]+line %d function \\w+\\n"
                    % int(m.group("l")))
            continue

        m = re.match(r"^save jump (?P<l>\d+)$", line)
        if m:
            ret += ("Saving jump target 'file[^\\n]+line %d function \\w+'\\n"
                    % int(m.group("l")))
            continue

        m = re.match(r"^save next (?P<l>\d+)$", line)
        if m:
            ret += ("Saving next instruction 'file[^\\n]+line %d function "
                    "\\w+'\\n" % int(m.group("l")))
            continue

        m = re.match(r"^resume next (?P<l>\d+)$", line)
        if m:
            ret += ("Resuming from next instruction 'file[^\\n]+line %d "
                    "function \\w+'\\n" % int(m.group("l")))
            continue

        m = re.match(r"^resume jump (?P<l>\d+)$", line)
        if m:
            ret += ("Resuming from jump target 'file[^\\n]+line %d function "
                    "\\w+'\\n" % int(m.group("l")))
            continue

        m = re.match(r"^unwind$", line)
        if m:
            ret += "Unwinding loop [^\\n]+\\n"
            continue

        m = re.match(r"^path is unsuccessful$", line)
        if m:
            ret += "VERIFICATION FAILED\\n"
            continue

        m = re.match(r"^path is successful$", line)
        if m:
            ret += "VERIFICATION SUCCESSFUL\\n"
            continue

        m = re.match(r"^end$", line)
        if m:
            ret += "[^.]"
            end = True
            continue

        m = re.match(r"^any lines$", line)
        if m:
            # Every other pattern deposits a '\n' at the end of the string.
            # Erase those two characters and add a pattern to match multiple
            # lines instead.
            ret = "%s%s" % (ret[:-2], "(.|\\n)+")
            continue

        print("%s:%d:0: error: Syntax error in path exploration test. "
              "(line: '%s')" % (in_file, offset, line), file=sys.stderr)
        ok = False
    if not ok:
        exit(1)
    return ret


def main():
    for dyr in os.listdir("."):
        if not os.path.isdir(dyr):
            continue
        for fyle in os.listdir(dyr):
            base, ext = os.path.splitext(fyle)
            if ext != ".in":
                continue
            in_file = os.path.join(dyr, fyle)
            sections = get_desc_sections(in_file)
            if len(sections) == 4:
                offset = (len(sections[0]) + len(sections[1]) +
                          len(sections[2]) + 3)
                sections[0].append(interpret(sections[3], in_file, offset))
                sections[3] = [
                    "             WARNING:",
                    "This .desc file is automatically generated",
                    "from the file '{fyle}'.".format(fyle=in_file),
                    "Do not modify this file.",
                    ""
                ]
            sections = ["\n".join(section) for section in sections]
            if len(sections) > 1:
                sections.insert(1, "--")
            if len(sections) > 3:
                sections.insert(3, "--")
            with open(os.path.join(dyr, "%s.desc" % base), "w") as f:
                f.write("\n".join(sections))


if __name__ == "__main__":
    main()
