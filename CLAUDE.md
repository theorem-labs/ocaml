# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formally verified OCaml compiler in Rocq (Coq). The end goal is a verified OCaml compiler that can bootstrap itself and eventually verify `ocamlc`. See the Roadmap section for the full plan.

The core correctness theorem: `forall source, interpret(source) = (interpret-bytecode . compile)(source)`

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

## Named Components

| Name | Type | Description |
|------|------|-------------|
| `ocamlc` | System program | OCaml source to bytecode (reference compiler) |
| `ocamlrun` | System program | OCaml bytecode to syscalls (reference runtime) |
| `compile` | Rocq code | OCaml source to bytecode (our compiler) |
| `interpret-bytecode` | Rocq code | OCaml bytecode to interaction tree of syscalls |
| `interpret` | Rocq code | OCaml source to interaction tree of syscalls |
| `lex-parse` | Rocq code | OCaml source to AST |
| `extract` | Rocq -> OCaml | Rocq source to OCaml source (Coq extraction) |
| `process` | Syscalls -> fn | Converts syscall interaction trees to executable functions |

## Trust Model

Three trust levels:
- **Trusted**: Must be correct for verification to hold. Kept maximally simple. Includes `interpret-bytecode`, `pretty-printer`, and the correctness theorem statement.
- **Untrusted**: Validated by PBT and eventually formal proofs. Includes `compile`, `lex-parse`, `interpret`, `SourceInterp.v`.
- **Trusted-ish**: Ongoing PBT/proof obligations that grow as scope expands. Includes cross-validation of `ocamlc` vs `compile`, bootstrapping proofs, and Rocq self-verification steps.

## Roadmap

1. **[Trusted] Bytecode interpreter** -- AST + pretty-printer + interpreter for OCaml bytecode (~150 instructions, ~1500 LoC). PBT harness verifies `ocamlrun` and `interpret-bytecode` agree. Based on semantics in https://cadmium.x9c.fr/distrib/caml-instructions.pdf.
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

Dates on roadmap items refer to when infrastructure/trusted parts are finished, not the task itself.

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
