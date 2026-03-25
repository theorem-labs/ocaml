# Progress Report: OCaml Formal Verification Project

## Project Goal
Formally verify an OCaml compiler in Rocq. The correctness theorem is:
`forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Architecture Overview

### Trust Levels
- **Trusted**: Code that must be correct for the verification to be meaningful
- **Untrusted**: Code validated by PBT or proofs — can be complex
- **Checker**: Thin modules that verify proofs satisfy interface specs

### Automation Levels
- **[Manual]**: Human-authored
- **[Auto]**: LLM-generated
- **[Semi-auto]**: LLM-generated with human-defined constraints (e.g., length penalties)

### Components
1. `interpret-bytecode` [Trusted] [Manual] — Rocq bytecode interpreter
2. `lex-parse` [Untrusted] [Auto] + `pretty-printer` [Trusted] [Semi-auto] — OCaml source <-> AST
3. `compile` [Untrusted] [Auto] + `interpret` [Untrusted] [Auto] — compiler + source interpreter
4. Compiler correctness theorem [Trusted spec] [Manual] + [Untrusted proof] [Auto] — theorem statement + infrastructure. [Semi-auto] interpret length penalty
5. Bytecode equivalence PBT [Trusted-ish] [Auto] — our compiler vs ocamlc

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

Source interpreter (`theories/Interpret/SourceInterp.v`):
- Fuel-based evaluation of Syntax.v AST
- Environment model with closures and recursive closures
- Pattern matching with tuple/constructor support
- Built-in functions: print_int, print_newline, fst, snd

Source interpreter PBT: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

Compiler (`theories/Compile/Compile.v`):
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

Compiler PBT (`test/compile-pbt/compile_test.ml`):
- 32 generators
- **5000/5000 pass, 0 fail, 0 skip across 10 seeds (500 tests each)**

### Part 4: Correctness Theorem Infrastructure
**Status: Infrastructure complete, theorem Admitted**

Correctness spec (`theories/Correctness/CorrectnessSpec.v`):
- Module Type declaring `compiler_correct` and `compiler_correctness`
- Parameters for `compile_program` and `interpret` (provided by proof module)

Correctness proofs (`theories/Correctness/CorrectnessProofs.v`):
- `ccall_to_events`: maps C-call primitives to output events
- `run_collecting`: fuel-based bytecode execution with event collection
- `bytecode_behavior`: entry point for compiled code execution
- `compiler_correct`: correctness statement (independent fuel parameters)
- `compiler_correctness`: main theorem (Admitted)
- `step_deterministic` lemma proved

Checker (`theories/Checker/CorrectnessChecker.v`):
- `Module Check <: CorrectnessSpec` — verifies proofs match spec

### Part 5: Bytecode Equivalence PBT (our compiler vs ocamlc)
**Status: Complete and validated, migrated to QCheck**

PBT results: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

### Loader in Rocq
**Status: Complete**

- `theories/InterpBytecode/Loader.v`: bytecode decoder ported from OCaml to Rocq
  - Section table parsing, two-pass decode with branch target resolution
  - All 153 opcodes handled
- `theories/InterpBytecode/Encode.v`: bytecode encoder (inverse of Loader)
  - Two-pass encoding with offset maps, always uses general opcode forms
- `theories/InterpBytecode/LoaderCorrectnessProofs.v`: roundtrip proof
  - Well-formedness predicate, sub-lemmas proved
  - Main theorem `decode_encode_inverse` Admitted
- `theories/InterpBytecode/LoaderCorrectnessSpec.v`: Module Type for roundtrip
- `theories/Checker/LoaderCorrectnessChecker.v`: `Module Check <: LoaderCorrectnessSpec`

### Extract Constant IO Wrapper
**Status: Complete**

- `theories/InterpBytecode/IO.v`: opaque axioms with Extract Constant for file I/O,
  Marshal, command-line args (following fiat-crypto pattern)
- `theories/InterpBytecode/Main.v`: standalone entry point with pure Rocq C-call
  handler (~30 primitives), globals decoding, interpreter run loop

### QCheck Migration
**Status: Complete**

All 5 PBT suites migrated from hand-rolled Random.State to QCheck generators.
Uses `qcheck-core` and `qcheck-core.runner`.

### OCaml Test Suite
**Status: Infrastructure complete, partially passing**

- `test/ocaml-testsuite` symlinked to system-ocaml test suite
- `test/interpret-bytecode-pbt/ocaml_testsuite_runner.ml`: runs .ml files through ocamlc + our interpreter
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
9. Checker pattern enforces proofs satisfy interface specs
10. Standalone Main.v entry point with Extract Constant I/O wrapper

## What's Not Working / Not Yet Done

1. **Correctness proof** — theorem is Admitted, pending proof
2. **Constructor match** — compiler handles int/bool/var/wild patterns but not constructor dispatch
3. **Effects/OO/Floats** — not planned for initial scope
4. **Parser doesn't handle full OCaml** — only the AST subset in Syntax.v
5. **Builtins as values** — fst/snd/print_int can only be used in direct application
6. **Loader roundtrip proof** — main theorem Admitted, sub-lemmas proved
7. **OCaml test suite** — 24/39 failing on basic/ (mostly GETFIELD interpreter limitation)

## Remaining Work

- Part 4: [Auto] Prove compiler_correctness theorem. [Semi-auto] Penalty for `interpret` length
- Part 6: [Auto] Extend PBT to Rocq source files as they come into scope
- Part 7: [Auto] Formal verification of OCaml extraction (self-verification)
- Part 8: [Auto] Formal verification of ocamlc
- Part 9: [Manual] Dockerfile and graders

## File Layout

```
theories/
  Utils/
    AST.v                       Bytecode instruction set (~107 variants)
    Value.v                     Value representation
    Observable.v                Observable behavior type
    Syntax.v                    OCaml source AST subset
  InterpBytecode/
    Machine.v                   Machine state + heap model
    Interp.v                    Step function + run loop (~800 LoC)
    Encode.v                    Bytecode encoder (instruction list -> byte list)
    Loader.v                    Bytecode decoder (bytes -> instruction list)
    WellFormed.v                Decidable well-formedness predicate
    LoaderCorrectnessSpec.v     Module Type for encode/decode roundtrip
    LoaderCorrectnessProofs.v   Roundtrip proof (Admitted)
    IO.v                        Extract Constant axioms for file I/O
    Main.v                      Standalone entry point with IO + Loader + Interp
  Compile/
    Compile.v                   Compiler (closures, recursion, match, tuples)
    LexParse/
      PrettyPrint.v             AST -> OCaml source string
  Interpret/
    SourceInterp.v              Fuel-based source interpreter
  Correctness/
    CorrectnessSpec.v           Module Type for compiler correctness
    CorrectnessProofs.v         Compiler correctness proof (Admitted)
  Checker/
    CorrectnessChecker.v        Module Check <: CorrectnessSpec
    LoaderCorrectnessChecker.v  Module Check <: LoaderCorrectnessSpec
  Extract.v                     Extraction directives

test/
  common/
    interp_extracted.ml         Extracted OCaml from Rocq (generated, do not edit)
    test_common.ml              Shared test utilities
    loader.ml                   Bytecode file loader
  interpret-bytecode-pbt/
    harness.ml                  Bytecode PBT (QCheck, Part 1.1)
    manual_test.ml              Hand-written bytecode tests
    ocaml_testsuite_runner.ml   OCaml test suite runner
    trace.ml                    Execution tracer
  compile-pbt/
    lexer.ml                    OCaml tokenizer
    parser.ml                   OCaml parser
    roundtrip_test.ml           Parser round-trip PBT (QCheck, Part 2)
    compile_test.ml             Compiler PBT (QCheck, Part 3)
    bytecode_equiv_test.ml      Bytecode equivalence PBT (QCheck, Part 5)
  interpret-pbt/
    source_interp_test.ml       Source interpreter PBT (QCheck, Part 3)
  ocaml-testsuite               Symlink to system-ocaml test suite
```
