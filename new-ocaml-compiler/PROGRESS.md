# Progress Report: OCaml Formal Verification Project

## Project Goal
Formally verify an OCaml compiler in Rocq (Coq). The core correctness theorem:
`forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Architecture Overview

### Trust Levels
- **Trusted**: Code that must be correct for the verification to be meaningful. Kept maximally simple.
- **Untrusted**: Code validated by PBT or proofs - can be complex.

### Components (from content.txt)
1. `interpret-bytecode` [Trusted] - Rocq bytecode interpreter
2. `lex-parse` [Untrusted] + `pretty-printer` [Trusted] - OCaml source <-> AST
3. `compile` [Untrusted] + `interpret` [Untrusted] - compiler + source interpreter
4. Compiler correctness theorem [Trusted] - theorem statement + infrastructure
5. Bytecode equivalence PBT [Trusted-ish] - our compiler vs ocamlc

## Part Status

### Part 1: Trusted Bytecode Interpreter + PBT Harness
**Status: COMPLETE**

37 QCheck test generators covering: arithmetic, recursion, higher-order functions,
partial application, tuples, variants, strings, refs, exceptions, lists,
closures over mutable refs, compare, String.length, String.get, nested match,
mutual recursion (even/odd), bitwise operations, while loops

### Part 2: Lexer/Parser + Pretty-Printer Round-Trip
**Status: COMPLETE**

QCheck round-trip PBT: generates random ASTs, pretty-prints, parses back, checks equality.

### Part 3: Source Interpreter + Compiler
**Status: COMPLETE**

- Source interpreter PBT (20 QCheck generators): vs ocamlrun
- Compiler PBT (32 QCheck generators): compile + bytecode interp vs ocamlrun

### Part 4: Correctness Theorem Infrastructure
**Status: COMPLETE (infrastructure). Theorem Admitted.**

`compiler_correct`: if source interpreter terminates normally with trace t,
there exists enough bytecode fuel such that the compiled code also terminates
normally and produces the same trace. Stronger than trace-only agreement.

Also provides weaker `traces_agree` variant with proved implication lemma.

### Part 5: Bytecode Equivalence PBT (our compiler vs ocamlc)
**Status: COMPLETE**

32 QCheck generators. For each test:
- Path A: AST -> compile_program -> our bytecode interpreter -> output
- Path B: AST -> OCaml source -> ocamlc -> load bytecode -> our interpreter -> output
- Asserts Path A output == Path B output

## What's Working

1. `make all` builds Rocq theories, extracts to OCaml, runs all 5 QCheck PBT suites
2. All 5 suites pass with 0 failures
3. Bytecode interpreter handles all tested patterns including mutual recursion
4. Correctness infrastructure ready for proof work

## Known Limitations

1. **Correctness proof** - `compiler_correct` is Admitted
2. **Op_and/Op_or** - compiles to ANDINT/ORINT (not short-circuit)
3. **Constructor match** - compiler handles int/bool/var/wild but not constructor dispatch
4. **print_string** - declared as builtin but not implemented in source interpreter or ccall_to_events
5. **Builtins as values** - fst/snd/print_int only in direct application position

## Remaining Work

- Part 4: Prove `compiler_correct`
- Part 6: PBT on Rocq source files
- Part 7: Self-verification (OCaml extraction)
- Part 8: Verify ocamlc
- Part 9: Dockerfile and graders

## File Layout

```
new-ocaml-compiler/
  theories/
    Bytecode.v         [Trusted] Instruction set (107 variants)
    Value.v            [Trusted] Value representation
    Machine.v          [Trusted] Machine state + heap
    Interp.v           [Trusted] Step function + run loop (~800 LoC)
    Syntax.v           [Trusted] OCaml AST
    Observable.v       [Trusted] Observable behavior type
    Correctness.v      [Trusted] compiler_correct theorem + infrastructure
    PrettyPrint.v      [Trusted] AST -> OCaml source (fully parenthesized)
    SourceInterp.v     [Untrusted] Source-level interpreter
    Compile.v          [Untrusted] Compiler
    Encode.v           Bytecode encoding
    Loader.v           Bytecode loader (Rocq)
    LoaderCorrectness.v  Loader correctness proof infrastructure
    IO.v               I/O model
    Main.v             Main entry point
    Extract.v          Extraction directives

  test/harness/
    interp_extracted.ml         Extracted OCaml from Rocq
    test_common.ml              Shared utilities
    loader.ml                   [Trusted] Bytecode file loader (OCaml)
    harness.ml                  [Trusted] Bytecode PBT (Part 1.1, 37 generators)
    lexer.ml                    [Untrusted] OCaml tokenizer
    parser.ml                   [Untrusted] OCaml parser
    roundtrip_test.ml           [Trusted] Parser round-trip PBT (Part 2)
    source_interp_test.ml       [Trusted] Source interpreter PBT (Part 3, 20 generators)
    compile_test.ml             [Trusted] Compiler PBT (Part 3, 32 generators)
    bytecode_equiv_test.ml      [Trusted-ish] Bytecode equiv PBT (Part 5, 32 generators)
    ocaml_testsuite_runner.ml   OCaml test suite runner
    trace.ml                    Execution tracer
    manual_test.ml              Manual bytecode tests
```
