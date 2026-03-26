# TODO.md -- Project Status Checkpoint (2026-03-26)

## Current State Summary

### Lines of Code

| Directory     | .v files | Description                              |
|---------------|----------|------------------------------------------|
| manual/       | 2,268    | Trusted core (interpreter, specs, IO)    |
| semi-auto/    | 468      | Pretty-printer, source interpreter       |
| automatic/    | 3,244    | Compiler, decoder, proofs (mostly Admitted) |
| Extract.v     | 208      | Extraction directives                    |
| **Total Rocq**| **6,188**|                                          |

| Directory          | .ml files | Description                        |
|--------------------|-----------|------------------------------------|
| manual/test/       | 5,712     | PBT harnesses, runners, common infra |
| interp_extracted.ml| 10,362    | Generated from Rocq (do not edit)  |

Key files by size:
- Interpret.v: 1,027 lines (bytecode step function, trusted core)
- DecodeProof.v: 1,744 lines (decode roundtrip proof, 2 Admitted)
- CompileProof.v: 531 lines (compiler correctness, 44 Admitted)
- Decode.v: 545 lines (bytecode decoder)
- Compile.v: 402 lines (compiler)
- Interpret.v (semi-auto): 360 lines (source interpreter)
- Main.v: 334 lines (pipeline + ~25 C-call handlers in Rocq)
- Encode.v: 321 lines (bytecode encoder)
- test_common.ml: 2,377 lines (~344 C-call stubs for PBT)

### Instruction Set

AST.v defines 100 instruction variants (one-to-one with opcodes.h).

### Module Types and Checkers

| Spec (Module Type)  | Location                        | Checker (Module Check)          | Status     |
|----------------------|---------------------------------|---------------------------------|------------|
| DecoderSpec          | manual/Bytecode/Main.v          | Extract.v (ConcreteDecoder)     | Instantiated |
| DecodeSpec           | manual/Bytecode/DecodeSpec.v    | (no checker module yet)         | Spec only  |
| LexParseSpec         | manual/LexParse/LexParseSpec.v  | Same file (Module Check)        | Checked    |
| CompileSpec          | manual/Compile/CompileSpec.v    | Same file (Module Check)        | Checked    |

### Axioms (Trusted)

9 axioms in manual/theories/Bytecode/IO.v (all IO boundary):
- `byte_string` (type), `read_file`, `byte_string_to_list`, `byte_string_length`
- `print_string_io`, `sys_argv`
- `marshal_from_bytes`, `unmarshal_globals`, `load_primitives`

25 Extract Constant directives in Extract.v:
- 10 for Uint63 (native int ops)
- 9 for IO axiom implementations
- 4 for PrimArray (native array ops)
- 2 for z_flip_sign, z_lsr (bit ops needing native semantics)

---

## Build Health

### Rocq Theories: PASS
All .v files compile cleanly. No errors. Deprecation warnings only in
DecodeProof.v (app_length -> length_app, map_length -> length_map).

### Extraction: PASS
`coqc Extract.v` succeeds. Produces 10,362-line interp_extracted.ml.

### OCaml Build: FAIL (1 file)
`dune build` fails on `manual/test/bytecode-pbt/runner.ml` line 8:
```
let _exit_code = Interp_extracted.main0 () in
```
`main0` is extracted as `int` (not a function), so `() in` is a type error.
**Fix**: change `Interp_extracted.main0 ()` to `Interp_extracted.main0`.

All other test executables (harness.exe, manual_test.exe, compile_test.exe,
ocaml_testsuite_runner.exe, etc.) build successfully.

### `make all`: FAIL (blocked by runner.ml)
### `make test` (modified to skip runner): bytecode PBT FAIL, compile PBT PASS
### `make testsuite`: runs, 59 PASS / 11 FAIL / 7 SKIP on basic dirs
### `make testsuite-all`: some dirs time out (IO-heavy tests)

---

## Test Coverage

### PBT Suites (QCheck)

| Suite                 | QCheck.Test.make | Generators | File                          |
|-----------------------|------------------|------------|-------------------------------|
| Bytecode vs ocamlrun  | 1                | 38         | bytecode-pbt/harness.ml       |
| Parser roundtrip       | 2                | 6          | bytecode-pbt/roundtrip_test.ml|
| Compile vs ocamlrun    | 1                | 1          | bytecode-pbt/compile_test.ml  |
| Source interp vs run   | 1                | 1          | bytecode-pbt/source_interp_test.ml |
| Bytecode equiv (us vs ocamlc) | 1        | 1          | bytecode-pbt/bytecode_equiv_test.ml |
| Compile PBT (compile-pbt) | 1            | 1          | compile-pbt/harness.ml        |
| **Total**             | **7**            | **48**     |                               |

### Manual Tests
4 hand-written bytecode tests in manual_test.ml (arithmetic, function call,
globals, blocks). All PASS.

### OCaml Test Suite Integration

Testsuite symlinked from system-ocaml-compiler: 198 directories total.

**TESTSUITE_BASIC** (8 dirs, `make testsuite`):
- basic, basic-more, basic-modules, basic-private, basic-float,
  basic-io, basic-io-2, basic-manyargs

**TESTSUITE_PHASE1** (42 additional dirs, `make testsuite-all`):
- misc, letrec-compilation, match-exception, array-functions,
  local-functions, 19 lib-* dirs, misc-kb, misc-unsafe, lazy,
  functors, exotic-syntax, let-syntax, extension-constructor,
  generalized-open, letrec-check, match-exception-warnings,
  raise-counts, prim-revapply, prim-bswap, float-unboxing,
  fma, int64-unboxing, basic-multdef

**Results on TESTSUITE_BASIC (77 tests):**
- 59 PASS (77%)
- 11 FAIL
- 7 SKIP

### Failing Tests (basic dirs)

| Test file                    | Failure reason                          | Category        |
|------------------------------|-----------------------------------------|-----------------|
| equality.ml                  | VECTLENGTH: not a block                 | Missing C-call   |
| patmatch.ml                  | Output truncated                        | Interpreter bug? |
| recvalues.ml                 | Test 4: FAILED                          | Recursive values |
| bounds.ml                    | "bad exception" instead of expected msg | Exception handling |
| div_by_zero.ml               | Empty output                            | Exception handling |
| pr2719.ml                    | Truncated output                        | Unknown          |
| recursive_module_init.ml     | Empty output                            | Module init      |
| float_literals.ml            | ccall failed                            | Missing C-call   |
| tfloat_hex.ml                | Slightly different error messages        | Float parsing    |
| wc.ml                        | Empty output (needs file I/O)           | File I/O         |
| io.ml                        | Empty output (needs file I/O)           | File I/O         |

### Known Failing PBT

Bytecode PBT (harness.ml) fails on nested exception handling:
```
try try raise Not_found with Exit -> 1 with Not_found -> 2
```
Our interpreter returns "unhandled exception" instead of 2.

---

## Bugs

### Fixed
- **SETFLOATFIELD operand inversion** (commit acb8483): field index and value
  were swapped in the step function. Fixed.
- **EQ/NEQ: structural vs physical equality** (commit 2a471f5): was using
  structural comparison; now uses `value_phys_eqb` for physical equality.
- **Silent C-call fallback** (commit acb8483): unknown C-calls silently
  returned 0. Now returns `None` to signal failure.

### Known Bugs
- **Nested exception handling**: `try try raise X with Y -> ... with X -> ...`
  fails. The inner PUSHTRAP/POPTRAP sequence does not correctly restore
  trap_sp when the inner handler does not match. Found by PBT.
- **patmatch.ml truncation**: Output is truncated mid-stream on large pattern
  match tests. Likely a fuel/step-limit issue.
- **div_by_zero.ml**: Division_by_zero exception not caught properly.
  Related to exception handling bug above.
- **bounds.ml**: Array bounds exceptions produce "bad exception" instead of
  expected error messages. Likely missing exception constructor matching.
- **recvalues.ml**: Recursive value initialization fails on Test 4.
  May need lazy/forcing semantics for recursive let bindings.
- **recursive_module_init.ml**: No output at all. Recursive modules likely
  need first-class module initialization support.

### Investigated, Not A Bug
- **closinfo=0**: All closures set closinfo to `Val_int 0`. This is
  intentional -- the closinfo field encodes arity/start-of-env offset, but
  our interpreter does not use it (we track arity differently). Confirmed
  by investigation that this does not cause failures.

### Performance Only (Not Correctness)
- **GETPUBMET/GETDYNMET**: Uses linear scan through method table instead of
  binary search. Correct but O(n) instead of O(log n). Only matters for
  programs with large class hierarchies.

---

## Admitted Proofs

### Summary: 47 total Admitted across 3 files

| File                          | Admitted | Notes                                |
|-------------------------------|----------|--------------------------------------|
| automatic/Compile/CompileProof.v | 44    | Per-case compiler correctness lemmas + main theorem |
| automatic/Bytecode/DecodeProof.v | 2     | Two main roundtrip theorems (sub-lemmas proved) |
| automatic/LexParse/LexParseProof.v | 1   | Single roundtrip theorem, completely Admitted |

### Details

**CompileProof.v** (44 Admitted):
- `compiler_correctness`: main theorem (forall prog, compiler_correct prog)
- `step_deterministic`: determinism of the step function (Admitted)
- ~20 per-instruction step lemmas (step_constint, step_addint, etc.)
- ~10 multi-step execution lemmas
- ~10 expression/pattern compilation correctness lemmas
- All Admitted with `Proof. Admitted.` (no partial proofs)

**DecodeProof.v** (2 Admitted):
- `decode_encode_roundtrip`: decode(encode(code)) = code (main theorem)
- `decode_bytecode_spec`: same via different formulation
- Sub-lemmas for read_u32_le inversion and per-opcode encoding are proved

**LexParseProof.v** (1 Admitted):
- `lex_parse_pp_inverse`: lex_parse(pp_program(prog)) = Some prog
- Completely Admitted, no sub-lemmas

---

## Architecture (Trust Model)

```
                        TRUSTED                          UNTRUSTED
                  (must be correct)               (validated by PBT/proofs)
                        |                                   |
    +---------+---------+---------+          +---------+---------+
    |         |         |         |          |         |         |
 AST.v    Encode.v  Interpret.v  IO.v    Decode.v  Compile.v  LexParse.v
 (100      (321     (1027 lines  (52     (545      (402       (10 lines)
 instrs)   lines)   step fn)     lines)  lines)    lines)
    |         |         |         |          |         |         |
    |         |    Machine.v     Main.v      |         |    PrettyPrint.v
    |         |    (116 lines)  (334 lines   |         |    (108 lines)
    |         |                 ~25 C-calls) |         |    [Semi-auto]
    |         |         |         |          |         |         |
    +---------+---------+---------+          +---------+---------+
              |                                        |
         DecodeSpec.v                          DecodeProof.v
         CompileSpec.v                         CompileProof.v
         LexParseSpec.v                        LexParseProof.v
         (Module Types)                        (all Admitted)
              |                                        |
              +-------------> Module Check <-----------+
                          (type-checks proof
                           against spec)

  Data Flow:
  ==========
  1. Reference:  source --ocamlc--> bytes --ocamlrun--> output
  2. Compiled:   source --lex-parse--> AST --compile--> bytecode --interpret-bytecode--> output
  3. Interpreted: source --lex-parse--> AST --interpret--> output

  Correctness theorem: paths 2 and 3 agree (all 47 proofs Admitted)
  PBT cross-validates: paths 1 and 2 agree (7 QCheck suites, ~48 generators)
```

---

## Roadmap Priorities

### P0: Fix Build
- [ ] Fix runner.ml type error (`main0` is int, not a function)

### P1: Fix Known Bugs
- [ ] Fix nested exception handling (PUSHTRAP/POPTRAP trap_sp restoration)
  - This is the only PBT failure. Fixing it would make bytecode PBT 0-fail.
- [ ] Fix Division_by_zero exception handling (div_by_zero.ml, bounds.ml)
- [ ] Investigate patmatch.ml output truncation (fuel limit?)

### P2: Expand Test Coverage
- [ ] Get testsuite-all to run without timeouts (IO tests are slow)
- [ ] Reduce FAIL count from 11 to <5 on basic dirs
- [ ] Add more C-call handlers in Main.v for lib-* test dirs
  - test_common.ml has 344 stubs; Main.v has ~25 Rocq handlers
  - Priority stubs: caml_array_*, caml_equal, caml_hash, caml_lazy_*

### P3: Proof Progress
- [ ] LexParseProof.v: prove lex_parse_pp_inverse (currently 0% done)
- [ ] DecodeProof.v: prove remaining 2 main theorems (sub-lemmas done)
- [ ] CompileProof.v: prove per-instruction lemmas, then main theorem

### P4: Roadmap Steps 5-9
- [ ] Step 5: Expand PBT for ocamlc vs compile equivalence
- [ ] Step 6: Rocq self-verification (extract Rocq source files)
- [ ] Step 7: Bootstrapping proofs
- [ ] Step 8: Verify ocamlc
- [ ] Step 9: Dockerfile and graders

---

## Git Status

- Branch: main (2 commits ahead of origin/main)
- Uncommitted: modified test_common.ml (not staged)
- Untracked: stubs.o, manyargsprim.o, audit snippets

Recent commits:
```
d20f3cf Add Tier 1 test directories, fix testsuite symlink and runner
2a471f5 Fix EQ/NEQ: use physical equality instead of structural comparison
f405aba Make audit line numbers dynamic; fix extract_snippets.py paths
3a93f95 Expand OCaml testsuite: 25 new dirs, testing.ml discovery, .mli support
eafd23c Add C-call stubs: float math, Obj, GC, Sys primitives
b64ad6a Remove LaTeX build artifacts, update gitignore
d1e304d Split audit into external and internal versions
acb8483 Fix SETFLOATFIELD operand inversion and silent C-call fallback
3bbc22c Add interp.c vs Interpret.v audit infrastructure
e1a443f Stop tracking extracted OCaml file; regenerate via make extract
834615b Update extracted OCaml to match current Rocq theories
3a5295f Merge local bytecode interpreter improvements into remote directory layout
7708121 Port local bytecode interpreter improvements to remote directory layout
dd953fc new stuff
7f96b33 directory restructuring
```
