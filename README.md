# Verified OCaml Compiler

A formally verified OCaml compiler written in [Rocq](https://rocq-prover.org/) (formerly Coq).

**Core correctness theorem:**
```
forall source, interpret(source) = (interpret-bytecode ∘ compile)(source)
```

The source interpreter and the compiled+bytecode path must agree on all programs. Property-based tests cross-validate both paths against the real OCaml toolchain (`ocamlrun`).

## What's in here

| Directory | Contents |
|-----------|----------|
| `verified-ocaml/` | Main Rocq project |
| `system-ocaml/` | OCaml 4.14 source (reference implementation + test suite) |
| `camlboot/` | OCaml bootstrap experiment (bootstrapping reference) |

### Three automation tiers

- **`manual/`** — Human-authored, trusted. Bytecode interpreter, AST, observable behavior type, IO axioms, correctness theorem signature.
- **`semi-auto/`** — LLM-generated with human-defined constraints. Pretty-printer (AST → source), source interpreter.
- **`automatic/`** — LLM-generated. Compiler (AST → bytecode), lexer/parser, correctness proofs, PBT test harness.

## Data flow

```
source ──ocamlc──▶ bytes ──ocamlrun──▶ output   (reference)
source ──lex-parse──▶ AST ──compile──▶ bytecode AST ──interpret-bytecode──▶ output   (our compiled path)
source ──lex-parse──▶ AST ──interpret──▶ output   (our interpreted path)
```

The theorem ties the compiled and interpreted paths. PBT cross-validates our compiled path against `ocamlrun`.

## Trust model

- **Trusted**: `interpret-bytecode`, bytecode encoder, `Observable.v`, IO axioms. Kept maximally simple.
- **Untrusted**: `compile`, `lex-parse`, `interpret`, correctness proofs. Validated by PBT and eventually formal proofs.
- **Checker modules**: `Module Check <: Spec` enforces proofs satisfy interface specs.

## Build

All commands run from `verified-ocaml/`:

```bash
make all          # Build theories, extract to OCaml, run all tests
make build        # Build Rocq theories with dune
make extract      # Extract Rocq → OCaml
make test         # Run all 5 PBT suites + manual tests
make testsuite    # Run OCaml test suite through our interpreter
```

### Individual test suites

```bash
dune exec manual/test/bytecode-pbt/harness.exe            # Bytecode PBT (interpret-bytecode vs ocamlrun)
dune exec manual/test/compile-pbt/harness.exe             # Compiler PBT (compile + interpret-bytecode vs ocamlrun)
dune exec manual/test/compile-pbt/roundtrip_test.exe      # Parser round-trip PBT
dune exec manual/test/compile-pbt/source_interp_test.exe  # Source interpreter PBT
dune exec manual/test/compile-pbt/bytecode_equiv_test.exe # Our compiler vs ocamlc bytecode equivalence
```

## Dependencies

- Rocq/Coq
- OCaml + dune 3.16
- `ocamlc` and `ocamlrun` (PBT reference)
- `qcheck-core`

## Roadmap

1. **[Done] Bytecode interpreter** — Trusted ZINC machine in Rocq, PBT vs `ocamlrun`
2. **[Done] Lexer/parser** — `lex-parse` + trusted pretty-printer, roundtrip proof
3. **[In progress] Compiler + source interpreter** — `compile` and `interpret`, correctness proof
4. **[Planned] Correctness theorem** — Close the admitted proof
5. **[Planned] PBT: `ocamlc` vs `compile`** — Bytecode equivalence on infinite program families
6. **[Planned] Rocq self-verification** — Compiler processes its own Rocq source
7. **[Planned] Bootstrapping** — Prove `compile = process ∘ interpret ∘ extract(compile src)`
8. **[Planned] Verify `ocamlc`** — Prove our compiler matches the real one

## License

MIT — Copyright (c) 2026 Theorem
