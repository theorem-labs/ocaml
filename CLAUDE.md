# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formally verified OCaml compiler in Rocq (Coq). The correctness theorem:
`forall source, interpret(source) = (interpret-bytecode . compile)(source)`

Code is split into **trusted** (must be correct for verification to be meaningful) and **untrusted** (validated by PBT or proofs). Trusted code is kept maximally simple.

## Build Commands

```bash
make all        # Build Rocq theories, extract to OCaml, run all tests
make build      # Build Rocq theories with dune
make extract    # Extract Rocq to OCaml (copies to test/harness/interp_extracted.ml)
make test       # Run all 5 PBT suites + manual tests
make clean      # Clean build artifacts
```

### Running individual test suites

```bash
dune exec test/harness/manual_test.exe                       # Manual bytecode tests
dune exec test/harness/harness.exe -- 200 42                 # Bytecode PBT (count seed)
dune exec test/harness/roundtrip_test.exe -- 500 42 4        # Parser round-trip PBT (count seed depth)
dune exec test/harness/source_interp_test.exe -- 100 42      # Source interpreter PBT
dune exec test/harness/compile_test.exe -- 200 42            # Compiler PBT
dune exec test/harness/bytecode_equiv_test.exe -- 100 42     # Bytecode equivalence PBT
```

## Architecture

### Rocq theories (`theories/`)

The pipeline: **OCaml source -> AST (`Syntax.v`) -> bytecode (`Compile.v`) -> execution (`Interp.v`)**

- `Bytecode.v` [Trusted] — Instruction set (107 variants)
- `Value.v` [Trusted] — Value representation
- `Machine.v` [Trusted] — Machine state + heap model
- `Interp.v` [Trusted] — Step function + run loop (~800 LoC)
- `Syntax.v` [Trusted] — OCaml AST subset
- `Observable.v` [Trusted] — Observable behavior type
- `PrettyPrint.v` [Trusted] — AST -> OCaml source string
- `Correctness.v` [Trusted] — Compiler correctness theorem (currently Admitted)
- `SourceInterp.v` [Untrusted] — Fuel-based source-level interpreter
- `Compile.v` [Untrusted] — Compiler: AST -> bytecode (closures, recursion, match, tuples)
- `Extract.v` — Extraction directives (generates `interp_extracted.ml`)

### Test harness (`test/harness/`)

- `interp_extracted.ml` — **Generated file**: extracted OCaml from Rocq, do not edit manually
- `test_common.ml` — Shared utilities (temp dirs, handlers, runners)
- `loader.ml` [Trusted] — Bytecode file loader (parses ocamlc output)
- `lexer.ml` / `parser.ml` [Untrusted] — OCaml tokenizer and parser for the AST subset

PBT suites validate each layer: bytecode interp vs ocamlrun, parser round-trip, source interp vs ocamlrun, compiler correctness, and our compiler vs ocamlc equivalence.

### Extraction flow

Rocq theories are built with dune, then `coqc` extracts `Interp.v` (and its dependencies) to `interp_extracted.ml`. This extracted file is compiled as a regular OCaml module alongside the test harness. The extraction step uses `-R _build/default/theories OCamlInterp` to find compiled `.vo` files.

## Key Design Decisions

- The bytecode interpreter (`Interp.v`) is the core trusted component — it must faithfully model OCaml's bytecode semantics
- PBT compares our Rocq-extracted interpreter against `ocamlrun` (the real OCaml runtime) to validate correctness
- The compiler and source interpreter are untrusted — they can be complex because PBT and eventually proofs validate them
- `Correctness.v` defines the theorem infrastructure but the proof itself is not yet done (Admitted)
- The project uses dune with the coq plugin (`(using coq 0.8)`) for building theories

## Dependencies

- Rocq/Coq (for building theories and extraction)
- OCaml + dune 3.16
- `ocamlc` and `ocamlrun` (for PBT reference comparison)
