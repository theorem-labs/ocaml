# Progress Report: OCaml Formal Verification Project

## Project Goal
Formally verify an OCaml compiler in Rocq (Coq). The correctness theorem is:
`forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Architecture Overview

### Trust Levels
- **Trusted**: Code that must be correct for the verification to be meaningful
- **SemiTrusted**: OCaml AST definitions and pretty-printer
- **Untrusted**: Code validated by PBT or proofs - can be complex
- **Checker**: Thin modules that verify Untrusted code satisfies Trusted interfaces

### Components (from content.txt)
1. `interpret-bytecode` [Trusted] - Rocq bytecode interpreter
2. `lex-parse` [Untrusted] + `pretty-printer` [SemiTrusted] - OCaml source <-> AST
3. `compile` [Untrusted] + `interpret` [Untrusted] - compiler + source interpreter
4. Compiler correctness theorem [SemiTrusted spec + Untrusted proof] - theorem statement + infrastructure
5. Bytecode equivalence PBT [Trusted-ish] - our compiler vs ocamlc

## What's Done

### Part 1: Trusted Bytecode Interpreter (interpret-bytecode)
**Status: Complete and validated**

PBT results: **2000/2000 pass, 0 fail, 0 skip across 10 seeds (200 tests each)**

### Part 1.1: PBT Harness (interpret-bytecode vs ocamlrun)
**Status: Complete and validated, migrated to QCheck**

37 test generators covering: arithmetic, recursion, higher-order functions,
partial application, tuples, variants, strings, refs, exceptions, lists,
closures over mutable refs, compare, String.length, String.get, nested match,
mutual recursion (even/odd), bitwise operations, while loops

### Part 2: Lexer/Parser + Pretty-Printer Round-Trip
**Status: Complete and validated, migrated to QCheck**

PBT results: **12000/12000 pass, 0 fail across 10 seeds at depth 4**

### Part 3: Source Interpreter + Compiler
**Status: Complete and validated, migrated to QCheck**

Source interpreter (`theories/Untrusted/SourceInterp.v`) [Untrusted]:
- Fuel-based evaluation of Syntax.v AST
- Environment model with closures and recursive closures
- Pattern matching with tuple/constructor support
- Built-in functions: print_int, print_newline, fst, snd

Source interpreter PBT: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

Compiler (`theories/Untrusted/Compile.v`) [Untrusted]:
- Free variable analysis for closure capture
- Absolute branch target computation via `base` parameter
- CLOSURE with environment variable capture (ENVACC)
- CLOSUREREC with self-reference (OFFSETCLOSURE 0)
- Inline builtins: fst -> GETFIELD 0, snd -> GETFIELD 1
- C-call builtins: print_int, print_newline, print_string
- Right-to-left tuple evaluation for correct MAKEBLOCK field ordering
- Pattern matching with proper dispatch:
  - Pat_int: equality test (ACC, PUSH, CONSTINT, EQ) + BRANCHIFNOT
  - Pat_bool: equality test against 0/1 + BRANCHIFNOT
  - Pat_var: unconditional with variable binding
  - Pat_wild / Pat_unit: unconditional catch-all
  - Cases chained with BRANCH to end for each body
- Top-level Decl_letrec uses CLOSUREREC (not delegated to Decl_let)

Compiler PBT (`test/harness/compile_test.ml`):
- 32 generators
- **5000/5000 pass, 0 fail, 0 skip across 10 seeds (500 tests each)**

### Part 4: Correctness Theorem Infrastructure
**Status: Infrastructure complete, theorem Admitted**

Correctness spec (`theories/SemiTrusted/CorrectnessSpec.v`) [SemiTrusted]:
- Module Type declaring `compiler_correct` and `compiler_correctness`
- Parameters for `compile_program` and `interpret` (provided by Untrusted)

Correctness proofs (`theories/Untrusted/CorrectnessProofs.v`) [Untrusted]:
- `ccall_to_events`: maps C-call primitives to output events
- `run_collecting`: fuel-based bytecode execution with event collection
- `bytecode_behavior`: entry point for compiled code execution
- `compiler_correct`: correctness statement (independent fuel parameters)
- `compiler_correctness`: main theorem (Admitted)
- `step_deterministic` lemma proved

Checker (`theories/Checker/Correctness.v`):
- `Module Check <: CorrectnessSpec` — verifies Untrusted proofs match spec

### Part 5: Bytecode Equivalence PBT (our compiler vs ocamlc)
**Status: Complete and validated, migrated to QCheck**

PBT results: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

### Loader in Rocq (from TODO)
**Status: Complete**

- `theories/Trusted/Loader.v`: bytecode decoder ported from OCaml to Rocq
  - Section table parsing, two-pass decode with branch target resolution
  - All 153 opcodes handled
- `theories/Untrusted/Encode.v`: bytecode encoder (inverse of Loader)
  - Two-pass encoding with offset maps, always uses general opcode forms
- `theories/Untrusted/LoaderCorrectnessProofs.v`: roundtrip proof
  - Well-formedness predicate, sub-lemmas proved
  - Main theorem `decode_encode_inverse` Admitted
- `theories/Trusted/LoaderCorrectnessSpec.v`: Module Type for roundtrip
- `theories/Checker/LoaderCorrectness.v`: `Module Check <: LoaderCorrectnessSpec`

### Extract Constant IO Wrapper (from TODO)
**Status: Complete**

- `theories/Trusted/IO.v`: opaque axioms with Extract Constant for file I/O,
  Marshal, command-line args (following fiat-crypto pattern)
- `theories/Trusted/Main.v`: standalone entry point with pure Rocq C-call
  handler (~30 primitives), globals decoding, interpreter run loop

### QCheck Migration (from TODO)
**Status: Complete**

All 5 PBT suites migrated from hand-rolled Random.State to QCheck generators.
Uses `qcheck-core` and `qcheck-core.runner`.

### OCaml Test Suite (from TODO)
**Status: Infrastructure complete, partially passing**

- `test/ocaml-testsuite` symlinked to system-ocaml-compiler test suite
- `test/harness/ocaml_testsuite_runner.ml`: runs .ml files through ocamlc + our interpreter
- Results on `basic/`: 10/39 pass, 24 fail (mostly GETFIELD errors), 5 skip
- `make testsuite` and `make testsuite-all` Makefile targets

## What's Working

1. Full build pipeline: `make all` builds Rocq theories, extracts to OCaml, runs 5 PBT suites
2. All 5 PBT suites achieve 0 fail, 0 skip
3. Bytecode interpreter handles all tested patterns including mutual recursion
4. Parser round-trips all generated ASTs through the pretty-printer
5. Source interpreter agrees with ocamlrun on all tested programs
6. Compiler produces correct bytecode for functions, recursion, tuples, match, multi-arg
7. Our compiler and ocamlc produce equivalent output on all tested programs
8. Correctness infrastructure ready for proof work
9. Trusted code kept maximally simple; no dead code in Rocq files
10. Checker pattern enforces Untrusted code satisfies Trusted interfaces
11. Standalone Main.v entry point with Extract Constant I/O wrapper

## What's Not Working / Not Yet Done

1. **Correctness proof** - theorem is Admitted, pending proof
2. **Constructor match** - compiler handles int/bool/var/wild patterns but not constructor dispatch
3. **Effects/OO/Floats** - not planned for initial scope
4. **Parser doesn't handle full OCaml** - only the AST subset in Syntax.v
5. **Builtins as values** - fst/snd/print_int can only be used in direct application
6. **Loader roundtrip proof** - main theorem Admitted, sub-lemmas proved
7. **OCaml test suite** - 24/39 failing on basic/ (mostly GETFIELD interpreter limitation)

## Remaining Work (from content.txt)

- Part 4: Prove compiler_correctness theorem
- Part 6: Extend PBT to Rocq source files as they come into scope
- Part 7: Formal verification of OCaml extraction (self-verification)
- Part 8: Formal verification of ocamlc
- Part 9: Dockerfile and graders

## File Layout

```
theories/
  Trusted/
    Bytecode.v              Instruction set (107 variants)
    Value.v                 Value representation
    Machine.v               Machine state + heap
    Interp.v                Step function + run loop (~800 LoC)
    Loader.v                Bytecode decoder (list Z -> list instruction)
    Observable.v            Observable behavior type
    IO.v                    Extract Constant axioms for file I/O
    Main.v                  Standalone entry point + C-call handler
    LoaderCorrectnessSpec.v Module Type for encode/decode roundtrip
  SemiTrusted/
    Syntax.v                OCaml AST
    PrettyPrint.v           AST -> OCaml source
    CorrectnessSpec.v       Module Type for compiler correctness
  Untrusted/
    SourceInterp.v          Source-level interpreter
    Compile.v               Compiler (functions, recursion, match, tuples)
    Encode.v                Bytecode encoder (list instruction -> list Z)
    LoaderCorrectnessProofs.v  Roundtrip proof (Admitted)
    CorrectnessProofs.v     Compiler correctness proof (Admitted)
  Checker/
    LoaderCorrectness.v     Module Check <: LoaderCorrectnessSpec
    Correctness.v           Module Check <: CorrectnessSpec
  Extract.v                 Extraction directives

test/harness/
  interp_extracted.ml       Extracted OCaml from Rocq (generated, do not edit)
  test_common.ml            Shared test utilities (temp dirs, handlers, runners)
  loader.ml                 [Trusted] Bytecode file loader
  harness.ml                Bytecode PBT harness (QCheck, Part 1.1)
  lexer.ml                  [Untrusted] OCaml tokenizer
  parser.ml                 [Untrusted] OCaml parser
  roundtrip_test.ml         Parser round-trip PBT (QCheck, Part 2)
  source_interp_test.ml     Source interpreter PBT (QCheck, Part 3)
  compile_test.ml           Compiler PBT (QCheck, Part 3)
  bytecode_equiv_test.ml    Bytecode equivalence PBT (QCheck, Part 5)
  ocaml_testsuite_runner.ml OCaml test suite runner (Part 7 prep)
  trace.ml                  Execution tracer
  manual_test.ml            Manual bytecode tests
test/ocaml-testsuite        Symlink to system-ocaml-compiler test suite
```
