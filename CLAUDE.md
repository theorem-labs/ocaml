# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formally verified OCaml compiler in Rocq (Coq). The end goal is a verified OCaml compiler that can bootstrap itself and eventually verify `ocamlc`. See the Roadmap section for the full plan.

The core correctness theorem: `forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Repository Structure

- `new-ocaml-compiler/` — The main project (Rocq theories + OCaml test harness)
- `system-ocaml-compiler/` — Git submodule: OCaml 4.14 source (`github.com/ocaml/ocaml`), used as reference implementation and test suite source
- `camlboot/` — Git submodule: OCaml bootstrap experiment (`github.com/Ekdohibs/camlboot`), reference for bootstrapping goals

## Build Commands

All build commands run from `new-ocaml-compiler/`:

```bash
make all            # Build Rocq theories, extract to OCaml, run all tests
make build          # Build Rocq theories with dune
make extract        # Extract Rocq to OCaml (copies to test/harness/interp_extracted.ml)
make test           # Run all 5 PBT suites + manual tests
make testsuite      # Run OCaml test suite (basic/) through our interpreter
make testsuite-all  # Run OCaml test suite (all basic-* dirs)
make clean          # Clean build artifacts
```

### Running individual test suites

All PBT suites use QCheck. Run from `new-ocaml-compiler/`:

```bash
dune exec test/harness/manual_test.exe                  # Manual bytecode tests
dune exec test/harness/harness.exe                      # Bytecode PBT (interpret-bytecode vs ocamlrun)
dune exec test/harness/roundtrip_test.exe               # Parser round-trip PBT
dune exec test/harness/source_interp_test.exe           # Source interpreter PBT
dune exec test/harness/compile_test.exe                 # Compiler PBT
dune exec test/harness/bytecode_equiv_test.exe          # Bytecode equivalence PBT (our compiler vs ocamlc)
```

## Architecture

### Rocq theories (`new-ocaml-compiler/theories/`)

The pipeline: **OCaml source -> AST (`Syntax.v`) -> bytecode (`Compile.v`) -> execution (`Interp.v`)**

Organized by trust level:

**`Trusted/Bytecode/`** — Core bytecode layer (must be correct):
- `AST.v` — Instruction set (~107 variants, one-to-one with `opcodes.h`)
- `Value.v` — Value representation
- `Machine.v` — Machine state + heap model
- `Interp.v` — Step function + run loop (~800 LoC)
- `Encode.v` — Bytecode encoder (instruction list -> byte list)
- `WellFormed.v` — Decidable well-formedness predicate for bytecode
- `LoaderCorrectnessSpec.v` — Module Type spec for encode/decode roundtrip

**`Trusted/`** — Other trusted components:
- `Observable.v` — Observable behavior type (output events + termination)
- `IO.v` — Opaque axioms with Extract Constant for file I/O, Marshal, command-line args

**`SemiTrusted/`** — AST definitions and specs:
- `Syntax.v` — OCaml AST subset (expressions, declarations, patterns, types)
- `PrettyPrint.v` — AST -> OCaml source string
- `CorrectnessSpec.v` — Module Type declaring the compiler correctness theorem

**`Untrusted/`** — Validated by PBT, eventually by proofs:
- `Compile.v` — Compiler: AST -> bytecode (closures, recursion, match, tuples)
- `SourceInterp.v` — Fuel-based source-level interpreter
- `Loader.v` — Bytecode decoder (bytes -> instruction list)
- `CorrectnessProofs.v` — Compiler correctness proof (Admitted)
- `LoaderCorrectnessProofs.v` — Encode/decode roundtrip proof (Admitted)

**`Checker/`** — Thin modules verifying Untrusted satisfies Trusted specs:
- `Correctness.v` — `Module Check <: CorrectnessSpec`
- `LoaderCorrectness.v` — `Module Check <: LoaderCorrectnessSpec`

**Top-level theories:**
- `Extract.v` — Extraction directives (generates `interp_extracted.ml`)
- `Main.v` — Standalone entry point with IO + Loader + Interp

### Test harness (`new-ocaml-compiler/test/harness/`)

- `interp_extracted.ml` — **Generated file**: extracted OCaml from Rocq, do not edit manually
- `test_common.ml` — Shared utilities (temp dirs, handlers, runners)
- `loader.ml` [Trusted] — Bytecode file loader (parses ocamlc `.cmo` output)
- `lexer.ml` / `parser.ml` [Untrusted] — OCaml tokenizer and parser for the AST subset
- `harness.ml` — Bytecode PBT: interpret-bytecode vs ocamlrun (37 generators)
- `roundtrip_test.ml` — Parser round-trip PBT
- `source_interp_test.ml` — Source interpreter PBT
- `compile_test.ml` — Compiler PBT (32 generators)
- `bytecode_equiv_test.ml` — Bytecode equivalence PBT: our compiler vs ocamlc
- `ocaml_testsuite_runner.ml` — Runs OCaml's own test suite through our interpreter
- `trace.ml` — Execution tracer
- `manual_test.ml` — Manual bytecode tests

### Extraction flow

Rocq theories are built with dune, then `coqc` extracts to `interp_extracted.ml`. This extracted file is compiled as a regular OCaml module alongside the test harness. The extraction step uses `-R _build/default/theories OCamlInterp` to find compiled `.vo` files.

## Named Components

| Name | Type | Description |
|------|------|-------------|
| `ocamlc` | System program | OCaml source to bytecode (reference compiler) |
| `ocamlrun` | System program | OCaml bytecode to syscalls (reference runtime) |
| `compile` | Rocq code | OCaml source to bytecode (our compiler) |
| `interpret-bytecode` | Rocq code | OCaml bytecode to interaction tree of syscalls |
| `interpret` | Rocq code | OCaml source to interaction tree of syscalls |
| `lex-parse` | OCaml code | OCaml source to AST |
| `extract` | Rocq -> OCaml | Rocq source to OCaml source (Coq extraction) |
| `process` | Syscalls -> fn | Converts syscall interaction trees to executable functions |

## Trust Model

Four trust levels:
- **Trusted**: Must be correct for verification to hold. Kept maximally simple. Includes `interpret-bytecode`, bytecode encoder, observable behavior type, IO axioms.
- **SemiTrusted**: AST definitions, pretty-printer, correctness theorem spec.
- **Untrusted**: Validated by PBT and eventually formal proofs. Includes `compile`, `lex-parse`, `interpret`, source interpreter, loader, correctness proofs.
- **Checker**: Thin modules that verify Untrusted code satisfies Trusted/SemiTrusted interface specs.

Additionally, **Trusted-ish** refers to ongoing PBT/proof obligations that grow as scope expands (cross-validation of `ocamlc` vs `compile`, bootstrapping proofs, Rocq self-verification).

## Roadmap

1. **[Trusted] Bytecode interpreter** -- AST + pretty-printer + interpreter for OCaml bytecode (~150 instructions, ~1500 LoC). PBT harness verifies `ocamlrun` and `interpret-bytecode` agree.
2. **[Untrusted] Lexer/parser** -- `lex-parse` processes OCaml source into AST. **[Trusted]** `pretty-printer` goes in reverse direction.
3. **[Untrusted] Compiler + source interpreter** -- `compile` (using `lex-parse`) and `interpret`.
4. **[Trusted] Correctness theorem** -- `forall source, interpret(source) = (interpret-bytecode . compile)(source)`. Proof evolves with `compile`/`interpret`. RL penalty for `interpret` length, amplified if no distinguishing program is found between previous `interpret` and `ocamlrun . ocamlc`.
5. **[Trusted-ish] PBT: `ocamlc` vs `compile`** -- Verify identical/equivalent bytecode on infinite families of syntax trees.
6. **[Trusted-ish] Rocq self-verification** -- As each Rocq source file comes into scope, add it to the PBT suite for `ocamlc` vs `compile`.
7. **[Trusted-ish] OCaml compiler in OCaml (bootstrapping)** -- As OCaml extraction comes into scope, prove:
   - `compile` = `process . interpret . extract(compile src)`
   - `interpret-bytecode` = `process . interpret . extract(interpret-bytecode src)`
   - `interpret` = `process . interpret . extract(interpret src)`
8. **[Trusted-ish] Verify `ocamlc`** -- As `ocamlc` source comes into scope, prove `compile` = `process . interpret(ocamlc src)`.
9. **Hardening** -- Dockerfile and graders for all tasks, hardened against exploits that modify testing infrastructure.

## Key Design Decisions

- The bytecode interpreter (`Interp.v`) is the core trusted component — it must faithfully model OCaml's bytecode semantics
- PBT compares our Rocq-extracted interpreter against `ocamlrun` (the real OCaml runtime) to validate correctness
- The compiler and source interpreter are untrusted — they can be complex because PBT and eventually proofs validate them
- Checker modules enforce that Untrusted proofs satisfy Trusted/SemiTrusted interface specs (`Module Check <: Spec`)
- The project uses dune with the coq plugin (`(using coq 0.8)`) for building theories

## Dependencies

- Rocq/Coq (for building theories and extraction)
- OCaml + dune 3.16
- `ocamlc` and `ocamlrun` (for PBT reference comparison)
- `qcheck-core` (for property-based testing)
