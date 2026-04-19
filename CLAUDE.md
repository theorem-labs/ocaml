# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Formally verified OCaml compiler in Rocq (Coq). The end goal is a verified OCaml compiler that can bootstrap itself and eventually verify `ocamlc`. See the Roadmap section for the full plan.

The core correctness theorem: `forall source, interpret(source) = (interpret-bytecode . compile)(source)`

## Repository Structure

- `verified-ocaml/` — The main project, organized by automation/trust level:
  - `manual/` — Human-authored Rocq theories (trusted core)
  - `semi-auto/` — LLM-generated Rocq theories with human-defined constraints
  - `automatic/` — LLM-generated Rocq theories
  - `checker/` — Thin `Module Check <: Spec` ascriptions that verify proofs satisfy interface specs; also hosts the PBT test harness (`checker/common/`, `checker/<Component>/test/`) and `checker/Extract.v` (extraction directives, imports from manual/semi-auto/automatic)
- `system-ocaml/` — Git submodule: OCaml 4.14 source (`github.com/ocaml/ocaml`), reference implementation and test suite source
- `camlboot/` — Git submodule: OCaml bootstrap experiment (`github.com/Ekdohibs/camlboot`), reference for bootstrapping goals

## Build Commands

All build commands run from `verified-ocaml/`:

```bash
make all            # Build Rocq theories, extract to OCaml, run all tests
make build          # Build Rocq theories with dune
make extract        # Extract Rocq to OCaml (copies to checker/common/interp_extracted.ml)
make test           # Run all PBT suites
make testsuite      # Run OCaml test suite (basic/) through our interpreter
make testsuite-all  # Run OCaml test suite (all basic-* dirs)
make clean          # Clean build artifacts
```

### Verifying Rocq compilation (without dune)

A full `dune build` / `make build` here can take long enough to time out a
tool-call. To check whether `.v` files compile, use the
`coq_makefile`-generated makefiles driven from `_CoqProject`, **always
with an explicit `.vo` target list**:

```bash
make Makefile.coq                          # regenerate Makefile.coq from _CoqProject
make -f Makefile.coq path/to/File.vo ...   # build a specific subset
```

Do **not** invoke `make -f Makefile.coq` with no target — that rebuilds
every `.v` listed in `_CoqProject` (hundreds of files, including ~10k-line
`instruct_handlers.v` and 151 per-handler proofs) and will time out the
tool call. Same rule applies to the per-tier variants.

Per-tier cumulative variants exist (generated from `_CoqProject.<tier>`):
`Makefile.coq.manual`, `Makefile.coq.semi-auto`, `Makefile.coq.automatic`,
`Makefile.coq.checker`. Each tier's makefile knows about its tier and the
tiers it depends on; pick the narrowest tier whose loadpath covers the
targets you want to build.

`_CoqProject` is kept in sync with `git ls-files "*.v"` via
`etc/organize-_CoqProject.sh`; re-run that script after adding or moving
`.v` files so the makefiles pick them up.

Prefer `make -f Makefile.coq <.vo targets>` over `dune build` when all you
need is a compilation check on a subset of theories.

### Running individual test suites

All PBT suites use QCheck. Run from `verified-ocaml/`:

```bash
dune exec checker/Bytecode/test/pbt.exe                    # Bytecode PBT (interpret-bytecode vs ocamlrun)
dune exec checker/Bytecode/test/ocaml_testsuite_runner.exe # Runs OCaml's own test suite through our interpreter
dune exec checker/Bytecode/test/pipeline_runner.exe        # Disk -> decode -> interpret -> output pipeline
dune exec checker/Compile/test/pbt.exe                     # Compiler PBT (compile + interpret-bytecode vs ocamlrun)
dune exec checker/Compile/test/equiv_test.exe              # Bytecode equivalence PBT (our compiler vs ocamlc)
dune exec checker/LexParse/test/pbt.exe                    # Parser round-trip PBT
dune exec checker/Interpret/test/source_interp_test.exe    # Source interpreter PBT
dune exec checker/Interpret/test/correctness_test.exe      # Cross-validates interpret vs compile+interpret-bytecode
dune exec checker/Interpret/test/advanced_test.exe         # Hand-crafted complex program tests
dune exec checker/Interpret/test/rocq_source_test.exe      # Tests using Rocq-style function patterns
```

## Architecture

Theories are organized by automation level: **Manual** (human-authored), **SemiAutomatic** (LLM-generated with human-defined constraints), and **Automatic** (LLM-generated). Within each, sub-folders group by component.

### `manual/` — Human-authored Rocq theories (trusted core)

Files sit flat in each component subfolder (no `theories/` layer).

- **`Utils/`** — Shared type definitions (no bytecode dependency):
  - `Value.v` — Value representation (used by interpreter, compiler, source interpreter)
  - `Observable.v` — Observable behavior type (output events + termination)
  - `Syntax.v` — OCaml source AST subset (expressions, declarations, patterns, types)
  - `WellFormed.v` — Well-formedness predicates

- **`Bytecode/`** — Bytecode interpreter pipeline (trusted core):
  - `AST.v` — Bytecode instruction set (~107 variants, one-to-one with `opcodes.h`)
  - `Machine.v` — ZINC machine state + heap model
  - `Interpret.v` — Step function + run loop (~800 LoC)
  - `Encode.v` — Bytecode encoder (AST -> bytes)
  - `DecodeSpec.v` — Module Type spec for encode/decode roundtrip
  - `IO.v` — Opaque axioms for OS interaction (disk-to-bytes, syscalls-to-real-world)

- **`Compile/`** — Compiler specification:
  - `CompileSpec.v` — Module Type for the compiler

- **`LexParse/`** — Lex/parse specification:
  - `LexParseSpec.v` — Module Type for lex-parse/pretty-print roundtrip

- **`ExtractSetup.v`** — Extraction configuration shared across the build.

### `semi-auto/` — LLM-generated Rocq theories with human-defined constraints

- **`LexParse/`** — Step 2: Pretty-printer (length penalty):
  - `PrettyPrint.v` — AST -> OCaml source string (trusted direction)

- **`Interpret/`** — Step 3: Source-level interpreter (length penalty):
  - `SourceInterp.v` — Fuel-based source interpreter

### `automatic/` — LLM-generated Rocq theories

Files sit flat in each component subfolder (no `theories/` layer).

- **`Bytecode/`** — Untrusted decoder and proofs:
  - `Decode.v` — Bytecode decoder (bytes -> AST, reverse of Encode.v)
  - `DecodeProof.v` — Proof that Decode.v satisfies DecodeSpec.v (Admitted)

- **`Compile/`** — Compiler and its proof:
  - `Compile.v` — Compiler: closures, recursion, match, tuples
  - `CompileProof.v` — Proof that Compile.v satisfies CompileSpec.v (Admitted)

- **`LexParse/`** — Untrusted parser and proofs:
  - `LexParse.v` — OCaml source string to AST parser (reverse of PrettyPrint.v)
  - `LexParseProof.v` — Proof that LexParse.v and PrettyPrint.v roundtrip (Admitted)

### `checker/` — Thin ascriptions and PBT harness

- **`<Component>/<Component>Checker.v`** — `Module Check <: <Component>Spec` (e.g. `Bytecode/DecodeChecker.v`, `Compile/CompileChecker.v`, `LexParse/LexParseChecker.v`).
- **`Bytecode/Main.v`** — Pipeline: disk -> decode -> interpret -> output, parameterized over decoder via `DecoderSpec`.
- **`Extract.v`** — Top-level extraction directives; imports from manual/semi-auto/automatic.
- **`common/`** — Shared test infrastructure:
  - `interp_extracted.ml` — **Generated file**: extracted OCaml from Rocq, do not edit
  - `test_common.ml` — Shared utilities (temp dirs, process runners, C-call handlers)
  - `code_arr.ml`, `uint63.ml` — Runtime support for the extracted code
- **`<Component>/test/`** — Per-component PBT harnesses (e.g. `checker/Bytecode/test/pbt.ml`, `checker/Compile/test/...`).

### Extraction flow

Rocq theories are built with dune, then `coqc` extracts to `checker/common/interp_extracted.ml`. This extracted file is compiled as a library alongside `test_common.ml`, shared by all PBT test executables under `checker/<Component>/test/`.

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

**`manual/` must never depend on `automatic/`, `semi-auto/`, or `checker/`.** This is a hard, one-directional dependency rule — violating it collapses the trust hierarchy. `manual/` may only import from `manual/` and external libraries. If a manual file is reaching for a definition outside manual/, the answer is either (a) move the definition into manual/, (b) restructure so the manual file doesn't need it, or (c) parameterize manual over the missing piece via a Module Type.

**Never complicate `manual/` to make proofs in `automatic/` easier.** `manual/` is the trusted core and must stay minimal; it is not a place to park shims, duplicated definitions, or back-compat re-exports that exist solely to spare downstream proof scripts from being updated. If a refactor in `manual/` forces a large mechanical update in `automatic/`, do the update — sed / scripted rewrites are cheap and reviewable; bloat in the trusted base is not. When an umbrella/re-export module is genuinely useful for downstream ergonomics, put it in `automatic/` (or `checker/`) and have it `Include` the functor or re-export the split manual submodules from there.

## Roadmap

Each step is tagged with a trust level (**[Trusted]**, **[Untrusted]**, **[Trusted-ish]**) and an automation level: **[Manual]** = human-authored, **[Auto]** = LLM-generated, **[Semi-auto]** = LLM-generated with human-defined constraints.

1. **[Trusted] [Manual] Bytecode interpreter** (`manual/Bytecode/`) -- AST + pretty-printer + interpreter for OCaml bytecode. **[Auto]** PBT harness (`checker/Bytecode/test/`) verifies `ocamlrun` and `interpret-bytecode` agree.
2. **[Untrusted] [Auto] Lexer/parser** (`automatic/LexParse/`) -- `lex-parse` processes OCaml source into AST. **[Trusted] [Semi-auto]** `pretty-printer` goes in reverse direction (`semi-auto/LexParse/PrettyPrint.v`).
3. **[Untrusted] [Auto] Compiler + source interpreter** (`automatic/Compile/`, `semi-auto/Interpret/`) -- `compile` (using `lex-parse`) and `interpret`.
4. **[Trusted] [Manual] Correctness theorem** (`manual/Correctness/`, planned) -- `forall source, interpret(source) = (interpret-bytecode . compile)(source)`. **[Auto]** Proof evolves with `compile`/`interpret` (`automatic/Correctness/`, planned). **[Semi-auto]** Penalty for `interpret` length, amplified if LLM cannot find a program where the previous `interpret` and `ocamlrun`∘`ocamlc` disagree on behavior.
5. **[Trusted-ish] [Auto] PBT: `ocamlc` vs `compile`** (`checker/Compile/test/`) -- Verify identical/equivalent bytecode on **[Manual]** infinite families of syntax trees.
6. **[Trusted-ish] [Auto] Rocq self-verification** -- As each Rocq source file comes into scope, **[Manual]** add it to the PBT suite for `ocamlc` vs `compile`.
7. **[Trusted-ish] [Auto] OCaml compiler in OCaml (bootstrapping)** -- As OCaml extraction comes into scope, **[Manual]** prove:
   - `compile` = `process . interpret . extract(compile src)`
   - `interpret-bytecode` = `process . interpret . extract(interpret-bytecode src)`
   - `interpret` = `process . interpret . extract(interpret src)`
8. **[Trusted-ish] [Auto] Verify `ocamlc`** -- As `ocamlc` source comes into scope, **[Manual]** prove `compile` = `process . interpret(ocamlc src)`.
9. **[Manual] Hardening** -- Dockerfile and graders for all tasks, hardened against exploits that modify testing infrastructure.

## Key Design Decisions

- The bytecode interpreter (`manual/Bytecode/Interpret.v`) is the core trusted component — it must faithfully model OCaml's bytecode semantics
- PBT compares our Rocq-extracted interpreter against `ocamlrun` (the real OCaml runtime) to validate correctness
- The compiler and source interpreter are untrusted — they can be complex because PBT and eventually proofs validate them
- Checker modules enforce that proofs satisfy interface specs (`Module Check <: Spec`)
- The project uses dune with the coq plugin (`(using coq 0.8)`) for building theories

## Dependencies

- Rocq/Coq (for building theories and extraction)
- OCaml + dune 3.16
- `ocamlc` and `ocamlrun` (for PBT reference comparison)
- `qcheck-core` (for property-based testing)
