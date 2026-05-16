#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
VO="$ROOT/verified-ocaml"
failed=0

fail() {
  printf 'FAIL: %s\n' "$1" >&2
  failed=1
}

pass() {
  printf 'PASS: %s\n' "$1"
}

strip_coq_comments() {
  # Strip Coq block comments (* ... *) before counting; non-nested fallback.
  perl -0777 -ne '
    my $prev;
    do { $prev = $_; s{\(\*[^(*]*(?:(?:\*[^)]|\([^*]|[^*(])[^(*]*)*\*\)}{}gs; } while ($prev ne $_);
    print;
  ' "$1"
}

count_admits() {
  local total=0
  while IFS= read -r f; do
    local c
    c=$(strip_coq_comments "$ROOT/$f" \
      | grep -E -c '(^|[[:space:]])(Admitted|admit)\.' || true)
    total=$((total + c))
  done < <(git -C "$ROOT" ls-files -- 'verified-ocaml/*.v' 'verified-ocaml/**/*.v' 2>/dev/null)
  printf '%s' "$total"
}

count_checker_admits() {
  local total=0
  while IFS= read -r f; do
    local c
    c=$(strip_coq_comments "$ROOT/$f" \
      | grep -E -c '(^|[[:space:]])(Admitted|admit)\.' || true)
    total=$((total + c))
  done < <(git -C "$ROOT" ls-files -- 'verified-ocaml/checker/*.v' 'verified-ocaml/checker/**/*.v' 2>/dev/null)
  printf '%s' "$total"
}

count_automatic_placeholders() {
  local total=0
  while IFS= read -r f; do
    local c
    c=$(strip_coq_comments "$ROOT/$f" \
      | grep -E -c '^[[:space:]]*(Axiom|Parameter|Conjecture)[[:space:]]+' || true)
    total=$((total + c))
  done < <(git -C "$ROOT" ls-files -- 'verified-ocaml/automatic/*.v' 'verified-ocaml/automatic/**/*.v' 2>/dev/null)
  printf '%s' "$total"
}

run_gate_step() {
  local description="$1"
  shift
  if "$@"; then
    pass "$description"
  else
    fail "$description"
  fi
}

if [[ ! -d "$VO" ]]; then
  fail "verified-ocaml directory exists"
else
  pass "verified-ocaml directory exists"
fi

all_admits="$(count_admits)"
if [[ "$all_admits" == "0" ]]; then
  pass "no Admitted./admit. remains in tracked verified-ocaml .v files"
else
  fail "tracked verified-ocaml .v files still contain $all_admits Admitted./admit. occurrences"
fi

checker_admits="$(count_checker_admits)"
if [[ "$checker_admits" == "0" ]]; then
  pass "checker .v files contain no Admitted./admit."
else
  fail "checker .v files still contain $checker_admits Admitted./admit. occurrences"
fi

automatic_placeholders="$(count_automatic_placeholders)"
if [[ "$automatic_placeholders" == "0" ]]; then
  pass "automatic proof files contain no Axiom/Parameter/Conjecture placeholders"
else
  fail "automatic proof files still contain $automatic_placeholders Axiom/Parameter/Conjecture placeholders"
fi

manual_bad_imports="$(git -C "$ROOT" grep -n -E 'OCamlInterp\.(Automatic|SemiAutomatic|Checker)|From[[:space:]]+OCamlInterp\.(Automatic|SemiAutomatic|Checker)|Require[[:space:]]+Import[[:space:]]+OCamlInterp\.(Automatic|SemiAutomatic|Checker)' -- 'verified-ocaml/manual/*.v' 'verified-ocaml/manual/**/*.v' 2>/dev/null || true)"
if [[ -z "$manual_bad_imports" ]]; then
  pass "manual files do not import automatic/semi-auto/checker namespaces"
else
  printf '%s\n' "$manual_bad_imports" >&2
  fail "manual trust hierarchy imports are clean"
fi

if [[ "$failed" -eq 0 ]]; then
  run_gate_step "Makefile.coq is regenerated" make -C "$VO" Makefile.coq
  run_gate_step "checker targets build" make -C "$VO" -f Makefile.coq \
    checker/Bytecode/DecodeChecker.vo \
    checker/Bytecode/InterpretChecker.vo \
    checker/Bytecode/Main.vo \
    checker/Compile/CompileChecker.vo \
    checker/Compile/PBTChecker.vo \
    checker/Compile/ExtractionChecker.vo \
    checker/LexParse/LexParseChecker.vo \
    checker/Extract.vo
  run_gate_step "bytecode instruction/meta checker targets build" make -C "$VO" -f Makefile.coq \
    checker/Bytecode/InstructChecker.vo \
    checker/Bytecode/MetaSpecChecker.vo
  run_gate_step "extraction completes" make -C "$VO" extract
  run_gate_step "core tests pass" make -C "$VO" test
  run_gate_step "testsuite passes or has documented skips" make -C "$VO" testsuite
fi

if [[ "$failed" -ne 0 ]]; then
  printf 'Completion gate is not satisfied; continue working.\n' >&2
  exit 1
fi

printf 'Completion gate satisfied.\n'
