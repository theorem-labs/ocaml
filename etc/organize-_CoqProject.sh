#!/usr/bin/env bash

SCRIPT_DIR="$(cd "$(dirname "$(realpath "${BASH_SOURCE[0]}")")" 2>/dev/null && pwd)"

ROCQ_DIR="$SCRIPT_DIR/../verified-ocaml"

pushd "$ROCQ_DIR" > /dev/null

if [ -z "${SORT}" ]; then
    if which gsort > /dev/null 2>&1; then
        SORT=gsort
    else
        SORT=sort
    fi
fi


orig_args="$(cat _CoqProject | LC_ALL=C "${SORT}" -u)"
args="$orig_args"
bindings="$(printf "%s\n" "$args" | grep -- '-Q\|-R')"
args="$(printf "%s\n" "$args" | grep -v -- '-Q\|-R')"
# regenerate list of Coq files
args="$(git ls-files --recurse-submodules "*.v" | LC_ALL=C "${SORT}" -u)"
args="$(printf "%s\n" "$args" | grep -v '^manual/audit/')"
manual_args="$(printf "%s\n" "$args" | grep '^manual/')"
semi_auto_args="$(printf "%s\n" "$args" | grep '^semi-auto/')"
automatic_args="$(printf "%s\n" "$args" | grep '^automatic/')"
checker_args="$(printf "%s\n" "$args" | grep '^checker/')"
other_args="$(printf "%s\n" "$args" | grep -v '^manual/\|^semi-auto/\|^automatic/\|^checker/')"
manual_bindings="$(printf "%s\n" "$bindings" | grep manual)"
semi_auto_bindings="$(printf "%s\n" "$bindings" | grep semi-auto)"
automatic_bindings="$(printf "%s\n" "$bindings" | grep automatic)"
checker_bindings="$(printf "%s\n" "$bindings" | grep checker)"
other_bindings="$(printf "%s\n" "$bindings" | grep -v 'manual\|semi-auto\|automatic\|checker')"
# not_tests="$(printf "%s\n" "$args" | grep -v '^Tests/')"
# hashed_originals="$(printf "%s\n" "$args" | grep '^Tests/HashedOriginals/')"
# failures="$(printf "%s\n" "$args" | grep '^Tests/CurrentExpectedFailure/')"
# args="$(printf "%s\n" "$args" | grep '^Tests/' | grep -v '^Tests/CurrentExpectedFailure/' | grep -v '^Tests/HashedOriginals/')"
# pre_tests="$(printf "%s\n" "$args" | grep '^Tests/[^/]*$')"
# args="$(printf "%s\n" "$args" | grep -v '^Tests/[^/]*$')"
# non_regression="$(printf "%s\n" "$args" | grep -v 'Regression')"
# regression_unknown="$(printf "%s\n" "$args" | grep 'Regression' | grep 'Unknown')"
# regression_not_unknown="$(printf "%s\n" "$args" | grep 'Regression' | grep -v 'Unknown')"
# failures_non_regression="$(printf "%s\n" "$failures" | grep -v 'Regression')"
# failures_regression_unknown="$(printf "%s\n" "$failures" | grep 'Regression' | grep 'Unknown')"
# failures_regression_not_unknown="$(printf "%s\n" "$failures" | grep 'Regression' | grep -v 'Unknown')"

# new_args="$(printf '%s\n' "$bindings" "$not_tests" "$pre_tests" "$non_regression" "$regression_not_unknown" "$regression_unknown" "$hashed_originals" "$failures_non_regression" "$failures_regression_not_unknown" "$failures_regression_unknown" | grep -v '^$')"
new_args="$(printf '%s\n' "$manual_bindings" "$semi_auto_bindings" "$automatic_bindings" "$checker_bindings" "$other_bindings" "$manual_args" "$semi_auto_args" "$automatic_args" "$checker_args" "$other_args")"
# printf '%s\n' "$new_args"
printf '%s\n' "$new_args" > _CoqProject.new
mv _CoqProject.new _CoqProject
printf '%s\n' "$manual_bindings" "$manual_args" > _CoqProject.manual
printf '%s\n' "$manual_bindings" "$semi_auto_bindings" "$manual_args" "$semi_auto_args" > _CoqProject.semi-auto
printf '%s\n' "$manual_bindings" "$semi_auto_bindings" "$automatic_bindings" "$manual_args" "$semi_auto_args" "$automatic_args" > _CoqProject.automatic
printf '%s\n' "$manual_bindings" "$semi_auto_bindings" "$automatic_bindings" "$checker_bindings" "$manual_args" "$semi_auto_args" "$automatic_args" "$checker_args" > _CoqProject.checker
git add _CoqProject _CoqProject.manual _CoqProject.semi-auto _CoqProject.automatic _CoqProject.checker
popd > /dev/null
