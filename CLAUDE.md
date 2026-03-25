# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formally verified OCaml compiler in Rocq (Coq). The end goal is a verified OCaml compiler that can bootstrap itself and eventually verify `ocamlc`. See the Roadmap section for the full plan.

The core correctness theorem: `forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Repository Structure

- `verified-ocaml/` — The main project, organized by automation level:
  - `manual/` — Human-authored Rocq theories (trusted core)
  - `semi-auto/` — LLM-generated Rocq theories with human-defined constraints
  - `automatic/` — LLM-generated Rocq theories and PBT test harness
  - `Extract.v` — Extraction directives (top-level, imports from all three)
- `system-ocaml/` — Git submodule: OCaml 4.14 source (`github.com/ocaml/ocaml`), reference implementation and test suite source
- `camlboot/` — Git submodule: OCaml bootstrap experiment (`github.com/Ekdohibs/camlboot`), reference for bootstrapping goals

## Build Commands

All build commands run from `verified-ocaml/`:

```bash
make all            # Build Rocq theories, extract to OCaml, run all tests
make build          # Build Rocq theories with dune
make extract        # Extract Rocq to OCaml (copies to manual/test/common/interp_extracted.ml)
make test           # Run all 5 PBT suites + manual tests
make testsuite      # Run OCaml test suite (basic/) through our interpreter
make testsuite-all  # Run OCaml test suite (all basic-* dirs)
make clean          # Clean build artifacts
```

### Running individual test suites

All PBT suites use QCheck. Run from `verified-ocaml/`:

```bash
dune exec manual/test/bytecode-pbt/manual_test.exe         # Manual bytecode tests
dune exec manual/test/bytecode-pbt/harness.exe             # Bytecode PBT (interpret-bytecode vs ocamlrun)
dune exec manual/test/compile-pbt/roundtrip_test.exe                 # Parser round-trip PBT
dune exec manual/test/interpret-pbt/source_interp_test.exe           # Source interpreter PBT
dune exec manual/test/compile-pbt/compile_test.exe                   # Compiler PBT
dune exec manual/test/compile-pbt/bytecode_equiv_test.exe            # Bytecode equivalence PBT (our compiler vs ocamlc)
```

## Architecture

Theories are organized by automation level: **Manual** (human-authored), **SemiAutomatic** (LLM-generated with human-defined constraints), and **Automatic** (LLM-generated). Within each, sub-folders group by component.

### `manual/` — Human-authored Rocq theories (trusted core)

- **`Utils/`** — Shared type definitions (no bytecode dependency):
  - `Value.v` — Value representation (used by interpreter, compiler, source interpreter)
  - `Observable.v` — Observable behavior type (output events + termination)
  - `Syntax.v` — OCaml source AST subset (expressions, declarations, patterns, types)

- **`Bytecode/`** — Bytecode interpreter pipeline (trusted core):
  - `AST.v` — Bytecode instruction set (~107 variants, one-to-one with `opcodes.h`)
  - `Machine.v` — ZINC machine state + heap model
  - `Interpret.v` — Step function + run loop (~800 LoC)
  - `Encode.v` — Bytecode encoder (AST -> bytes)
  - `DecodeSpec.v` — Module Type spec for encode/decode roundtrip
  - `IO.v` — Opaque axioms for OS interaction (disk-to-bytes, syscalls-to-real-world)
  - `Main.v` — Pipeline: disk -> decode -> interpret -> output (parameterized over decoder via `DecoderSpec` Module Type)

- **`Correctness/`** — Step 4: Compiler correctness theorem definition:
  - `CorrectnessSpec.v` — Module Type declaring the theorem signature

- **`Checker/`** — Thin modules verifying proofs satisfy specs:
  - `CorrectnessChecker.v` — `Module Check <: CorrectnessSpec`
  - `DecodeCorrectnessChecker.v` — `Module Check <: DecodeSpec`

- **`theories/`** — Specs with integrated checkers:
  - `LexParseSpec.v` — Module Type for lex-parse/pretty-print roundtrip + `Module Check <: LexParseSpec`

### `semi-auto/` — LLM-generated Rocq theories with human-defined constraints

- **`LexParse/`** — Step 2: Pretty-printer (length penalty):
  - `PrettyPrint.v` — AST -> OCaml source string (trusted direction)

- **`Interpret/`** — Step 3: Source-level interpreter (length penalty):
  - `SourceInterp.v` — Fuel-based source interpreter

### `automatic/` — LLM-generated code and tests

**`theories/`** — Rocq theories:

- **`Compile/`** — Step 3: Compiler (AST -> bytecode):
  - `Compile.v` — Compiler: closures, recursion, match, tuples

- **`Correctness/`** — Step 4: Compiler correctness proof:
  - `CorrectnessProofs.v` — Proof infrastructure (main theorem Admitted)

- **`Bytecode/`** — Untrusted decoder and proofs:
  - `Decode.v` — Bytecode decoder (bytes -> AST, reverse of Encode.v)
  - `Main.v` — Instantiates the trusted pipeline with the concrete decoder
  - `DecodeProof.v` — Proof that Decode.v satisfies DecodeSpec.v (Admitted)

**`LexParse/`** — Untrusted parser and proofs:
- `LexParse.v` — OCaml source string to AST parser (reverse of PrettyPrint.v)
- `LexParseProof.v` — Proof that LexParse.v and PrettyPrint.v roundtrip (Admitted)

**`test/`** — PBT test harness:

- **`common/`** — Shared test infrastructure:
  - `interp_extracted.ml` — **Generated file**: extracted OCaml from Rocq, do not edit
  - `test_common.ml` — Shared utilities (temp dirs, process runners, C-call handlers)
  - `loader.ml` — Bytecode file loader (parses ocamlc `.cmo` output)

- **`bytecode-pbt/`** — Step 1.1: Bytecode interpreter PBT:
  - `harness.ml` — Bytecode PBT: interpret-bytecode vs ocamlrun (37 generators)
  - `manual_test.ml` — Hand-written bytecode tests
  - `ocaml_testsuite_runner.ml` — Runs OCaml's own test suite through our interpreter
  - `trace.ml` — Execution tracer

- **`compile-pbt/`** — Steps 2, 3, 5: Compiler and parser PBT:
  - `lexer.ml` / `parser.ml` — OCaml tokenizer and parser for the AST subset
  - `roundtrip_test.ml` — Parser round-trip PBT (step 2)
  - `compile_test.ml` — Compiler PBT: compile + interpret-bytecode vs ocamlrun (step 3, 32 generators)
  - `bytecode_equiv_test.ml` — Bytecode equivalence PBT: our compiler vs ocamlc (step 5)

- **`interpret-pbt/`** — Step 3: Source interpreter PBT:
  - `source_interp_test.ml` — Source interpreter vs ocamlrun

### Extraction flow

Rocq theories are built with dune, then `coqc` extracts to `manual/test/common/interp_extracted.ml`. This extracted file is compiled as a library (`pbt_common`) alongside `test_common.ml` and `loader.ml`, shared by all PBT test executables.

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

## Data Flow

The system has three parallel paths from source to output:

1. **Reference path**: `source --ocamlc--> bytes --ocamlrun--> output` (the real OCaml toolchain)
2. **Our compiled path**: `source --lex-parse--> AST --compile--> bytecode AST --interpret-bytecode--> output`
3. **Our interpreted path**: `source --lex-parse--> AST --interpret--> output`

The correctness theorem ties paths 2 and 3: they must agree on all programs. PBT cross-validates paths 1 and 2 (our output matches `ocamlrun`).

Pretty-printers go in the reverse direction (AST -> source string, bytecode AST -> bytes). They are trusted because they are simple injections. Parsers/decoders are untrusted because they are complex inversions, validated by roundtrip proofs: `parse(pretty-print(x)) = x`.

## Trust Model

- **Trusted**: Must be correct for verification to hold. Kept maximally simple. Includes `interpret-bytecode`, bytecode encoder, observable behavior type, IO axioms.
- **Untrusted**: Validated by PBT and eventually formal proofs. Includes `compile`, `lex-parse`, `interpret`, source interpreter, loader, correctness proofs.
- **Checker**: Thin modules that verify proofs satisfy interface specs.
- **Trusted-ish**: Ongoing PBT/proof obligations that grow as scope expands (cross-validation of `ocamlc` vs `compile`, bootstrapping proofs, Rocq self-verification).

## Roadmap

Each step is tagged with a trust level (**[Trusted]**, **[Untrusted]**, **[Trusted-ish]**) and an automation level: **[Manual]** = human-authored, **[Auto]** = LLM-generated, **[Semi-auto]** = LLM-generated with human-defined constraints.

1. **[Trusted] [Manual] Bytecode interpreter** (`manual/theories/Bytecode/`) -- AST + pretty-printer + interpreter for OCaml bytecode. **[Auto]** PBT harness verifies `ocamlrun` and `interpret-bytecode` agree.
2. **[Untrusted] [Auto] Lexer/parser** (`manual/test/compile-pbt/`) -- `lex-parse` processes OCaml source into AST. **[Trusted] [Semi-auto]** `pretty-printer` goes in reverse direction (`semi-auto/theories/Compile/LexParse/`).
3. **[Untrusted] [Auto] Compiler + source interpreter** (`automatic/theories/Compile/`, `semi-auto/theories/Interpret/`) -- `compile` (using `lex-parse`) and `interpret`.
4. **[Trusted] [Manual] Correctness theorem** (`manual/theories/Correctness/`) -- `forall source, interpret(source) = (interpret-bytecode . compile)(source)`. **[Auto]** Proof evolves with `compile`/`interpret` (`automatic/theories/Correctness/`). **[Semi-auto]** Penalty for `interpret` length, amplified if LLM cannot find a program where the previous `interpret` and `ocamlrun`∘`ocamlc` disagree on behavior.
5. **[Trusted-ish] [Auto] PBT: `ocamlc` vs `compile`** (`manual/test/compile-pbt/`) -- Verify identical/equivalent bytecode on **[Manual]** infinite families of syntax trees.
6. **[Trusted-ish] [Auto] Rocq self-verification** -- As each Rocq source file comes into scope, **[Manual]** add it to the PBT suite for `ocamlc` vs `compile`.
7. **[Trusted-ish] [Auto] OCaml compiler in OCaml (bootstrapping)** -- As OCaml extraction comes into scope, **[Manual]** prove:
   - `compile` = `process . interpret . extract(compile src)`
   - `interpret-bytecode` = `process . interpret . extract(interpret-bytecode src)`
   - `interpret` = `process . interpret . extract(interpret src)`
8. **[Trusted-ish] [Auto] Verify `ocamlc`** -- As `ocamlc` source comes into scope, **[Manual]** prove `compile` = `process . interpret(ocamlc src)`.
9. **[Manual] Hardening** -- Dockerfile and graders for all tasks, hardened against exploits that modify testing infrastructure.

## Key Design Decisions

- The bytecode interpreter (`Interp.v`) is the core trusted component — it must faithfully model OCaml's bytecode semantics
- PBT compares our Rocq-extracted interpreter against `ocamlrun` (the real OCaml runtime) to validate correctness
- The compiler and source interpreter are untrusted — they can be complex because PBT and eventually proofs validate them
- Checker modules enforce that proofs satisfy interface specs (`Module Check <: Spec`)
- The project uses dune with the coq plugin (`(using coq 0.8)`) for building theories

## Dependencies

- Rocq/Coq (for building theories and extraction)
- OCaml + dune 3.16
- `ocamlc` and `ocamlrun` (for PBT reference comparison)
- `qcheck-core` (for property-based testing)
