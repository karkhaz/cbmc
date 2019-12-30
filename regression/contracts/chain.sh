#!/usr/bin/env bash
#
# Build and run tests depending on k:v pairs on third line of *.desc
#
# Author: Kareem Khazem <karkhaz@karkhaz.com>

set -e

# Given a list of 'key:value' pairs, return value at given key.
# $1:     name of key
# $2:     list of semicolon-separated acceptable values, or '*'
# $3..N:  space-separated list of colon-separated k:v pairs
get_value_at_key()
{
    for pair in "${@:3:${#@}}"; do
        key=$(echo "${pair}" | awk -F: '{print $1}')
        if ! [[ "${key}" == "$1" ]]; then
            continue;
        fi

        val=$(echo "${pair}" | awk -F: '{print $2}')
        if [[ "${2}" == '*' ]]; then
            echo "${val}"
            exit 0
        elif ! [[ "${2}" =~ "${val}" ]]; then
            (
              >&2 echo "Found invalid value '${val}' "
              >&2 echo "for key '$1' in one of the .desc "
              >&2 echo "files in directory '$(pwd)'. "
              >&2 echo "Acceptable values are [${2}]."
            )
            exit 1
        fi

        echo "${val}"
        return 0
    done

    (
      >&2 echo "Could not find key '$1' in one of ";
      >&2 echo "the .desc files in directory '$(pwd)'."
    )
    exit 1
}

goto_cc=$1
goto_instrument=$2
cbmc=$3

is_windows=$4
if [[ "${is_windows}" != "true" && "${is_windows}" != "false" ]]; then
    (>&2 echo "\$is_windows should be true or false (got '${is_windows}')")
    exit 1
fi

# This script expects a set of key:value pairs to be written on the
# third line of the test.desc file. test.pl passes those pairs as
# arguments to chain.sh. They are the fifth argument until the
# second-last.
KEY_VALS="${@:5:${#@}-5}"

contracts_mode=$(get_value_at_key contracts "none check apply" ${KEY_VALS})
test_mode=$(get_value_at_key test-mode "symbol cbmc" ${KEY_VALS})
function=$(get_value_at_key function "*" ${KEY_VALS})

src=main.c

OUT_FILE=01_$(basename ${src%.c}).gb

if [[ "${is_windows}" == "true" ]]; then
    "${goto_cc}"              \
        /I..                  \
        /c                    \
        /Fo"${OUT_FILE}"      \
        "${src}"
else
    "${goto_cc}"              \
        -I..                  \
        -c                    \
        -o "${OUT_FILE}"      \
        "${src}"
fi


instrumented="02_instrumented-${contracts_mode}-${test_mode}.gb"

if [[ "${contracts_mode}" == apply ]]; then
    "${goto_instrument}" --replace-all-with-contracts 01_main.gb "${instrumented}"
elif [[ "${contracts_mode}" == check ]]; then
    "${goto_instrument}" --check-contracts 01_main.gb "${instrumented}"
else
  cp 01_main.gb "${instrumented}"
fi


if [[ "${test_mode}" == "symbol" ]]; then
    "${goto_instrument}" --show-symbol-table "${instrumented}"
elif [[ "${test_mode}" == "cbmc" ]]; then
    "${cbmc}"                     \
        --unwinding-assertions    \
        --bounds-check            \
        --pointer-check           \
        --nondet-static           \
        --div-by-zero-check       \
        --float-overflow-check    \
        --nan-check               \
        --pointer-overflow-check  \
        --undefined-shift-check   \
        --signed-overflow-check   \
        --unsigned-overflow-check \
        --function ${function}    \
        "${instrumented}"
fi
