# Progress Report: OCaml Formal Verification Project

## Project Goal
Formally verify an OCaml compiler in Rocq (Coq). The correctness theorem is:
`forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Architecture Overview

### Trust Levels
- **Trusted**: Code that must be correct for the verification to be meaningful
- **Untrusted**: Code validated by PBT or proofs - can be complex

### Components (from content.txt)
1. `interpret-bytecode` [Trusted] - Rocq bytecode interpreter
2. `lex-parse` [Untrusted] + `pretty-printer` [Trusted] - OCaml source <-> AST
3. `compile` [Untrusted] + `interpret` [Untrusted] - compiler + source interpreter
4. Compiler correctness theorem [Trusted] - theorem statement + infrastructure
5. Bytecode equivalence PBT [Trusted-ish] - our compiler vs ocamlc

## What's Done

### Part 1: Trusted Bytecode Interpreter (interpret-bytecode)
**Status: Complete and validated**

PBT results: **2000/2000 pass, 0 fail, 0 skip across 10 seeds (200 tests each)**

### Part 1.1: PBT Harness (interpret-bytecode vs ocamlrun)
**Status: Complete and validated**

37 test generators covering: arithmetic, recursion, higher-order functions,
partial application, tuples, variants, strings, refs, exceptions, lists,
closures over mutable refs, compare, String.length, String.get, nested match,
mutual recursion (even/odd), bitwise operations, while loops

### Part 2: Lexer/Parser + Pretty-Printer Round-Trip
**Status: Complete and validated**

PBT results: **12000/12000 pass, 0 fail across 10 seeds at depth 4**

### Part 3: Source Interpreter + Compiler
**Status: Complete and validated**

Source interpreter (`theories/SourceInterp.v`) [Untrusted]:
- Fuel-based evaluation of Syntax.v AST
- Environment model with closures and recursive closures
- Pattern matching with tuple/constructor support
- Built-in functions: print_int, print_newline, fst, snd

Source interpreter PBT: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

Compiler (`theories/Compile.v`) [Untrusted]:
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
- 32 generators: literals, arithmetic, if, let, negation, nested arithmetic,
  simple functions, factorial, fibonacci, tuples+fst/snd, multi-arg functions,
  integer match (3/5-case), match with variable binding, match on computed value,
  nested if-in-match, match-in-if, function-returning-match, let-in-match,
  deeply nested let, recursive function with match, top-level Decl_letrec,
  non-commutative tuple access, division/modulo, nested function calls,
  higher-order function returning closure, multiple prints, comparison operators,
  variable shadowing, partial application via currying
- **5000/5000 pass, 0 fail, 0 skip across 10 seeds (500 tests each)**

### Part 4: Correctness Theorem Infrastructure
**Status: Infrastructure complete, theorem Admitted**

Correctness infrastructure (`theories/Correctness.v`) [Trusted]:
- `ccall_to_events`: maps C-call primitives to output events
- Uses `z_to_events` from SourceInterp.v (single source of truth)
- `run_collecting`: fuel-based bytecode execution with event collection
- `bytecode_behavior`: entry point for compiled code execution
- `traces_agree`: correctness statement (source trace = bytecode trace for
  terminating programs, with independent fuel parameters)
- `compiler_correctness`: main theorem (Admitted)
- `step_deterministic` lemma proved

### Part 5: Bytecode Equivalence PBT (our compiler vs ocamlc)
**Status: Complete and validated**

Test (`test/harness/bytecode_equiv_test.ml`) [Trusted-ish]:
- Generates ASTs from 14 generator families
- Path A: AST -> compile_program -> our bytecode interpreter -> output
- Path B: AST -> OCaml source -> ocamlc -> load bytecode -> our interpreter -> output
- Asserts Path A output == Path B output
- Proves: for tested programs, compile_program and ocamlc produce
  behaviorally equivalent bytecode when run on our interpreter

PBT results: **1000/1000 pass, 0 fail, 0 skip across 10 seeds**

## What's Working

1. Full build pipeline: `make all` builds 11 Rocq files, extracts to OCaml, runs 5 PBT suites
2. All 5 PBT suites achieve 0 fail, 0 skip across 10 seeds
3. Bytecode interpreter handles all tested patterns including mutual recursion
4. Parser round-trips all generated ASTs through the pretty-printer
5. Source interpreter agrees with ocamlrun on all tested programs
6. Compiler produces correct bytecode for functions, recursion, tuples, match, multi-arg
7. Our compiler and ocamlc produce equivalent output on all tested programs
8. Correctness infrastructure ready for proof work
9. Trusted code kept maximally simple; no dead code in Rocq files

## What's Not Working / Not Yet Done

1. **Correctness proof** - theorem is Admitted, pending proof
2. **Constructor match** - compiler handles int/bool/var/wild patterns but not constructor dispatch
3. **Effects/OO/Floats** - not planned for initial scope
4. **Parser doesn't handle full OCaml** - only the AST subset in Syntax.v
5. **Builtins as values** - fst/snd/print_int can only be used in direct application

## Remaining Work (from content.txt)

- Part 4: Prove compiler_correctness theorem
- Part 6: Extend PBT to Rocq source files as they come into scope
- Part 7: Formal verification of OCaml extraction (self-verification)
- Part 8: Formal verification of ocamlc
- Part 9: Dockerfile and graders

## File Layout

```
theories/
  Bytecode.v      [Trusted] Instruction set (107 variants)
  Value.v         [Trusted] Value representation
  Machine.v       [Trusted] Machine state + heap
  Interp.v        [Trusted] Step function + run loop (~800 LoC)
  Syntax.v        [Trusted] OCaml AST
  Observable.v    [Trusted] Observable behavior type
  Correctness.v   [Trusted] Compiler correctness theorem + infrastructure
  PrettyPrint.v   [Trusted] AST -> OCaml source
  SourceInterp.v  [Untrusted] Source-level interpreter
  Compile.v       [Untrusted] Compiler (functions, recursion, match, tuples)
  Extract.v       Extraction directives

test/harness/
  interp_extracted.ml       Extracted OCaml from Rocq
  test_common.ml            Shared test utilities (temp dirs, handlers, runners)
  loader.ml                 [Trusted] Bytecode file loader
  harness.ml                [Trusted] Bytecode PBT harness (Part 1.1)
  lexer.ml                  [Untrusted] OCaml tokenizer
  parser.ml                 [Untrusted] OCaml parser
  roundtrip_test.ml         [Trusted] Parser round-trip PBT (Part 2)
  source_interp_test.ml     [Trusted] Source interpreter PBT (Part 3)
  compile_test.ml           [Trusted] Compiler PBT (Part 3, 32 generators)
  bytecode_equiv_test.ml    [Trusted-ish] Bytecode equivalence PBT (Part 5)
  trace.ml                  Execution tracer
  manual_test.ml            Manual bytecode tests
```
