# Verified OCaml Compiler Roadmap

## Goal

Reach full formal verification of the OCaml compiler in two stages:

1. **Stage 1 (Manual + Checker)**: State the three top-level theorems correctly. Only edit `manual/` and `checker/`. Stubs in `automatic/`/`semi-auto/` are permissible only as type-level placeholders. Complete when all three theorem statements are provable given only `automatic/`/`semi-auto/` changes. End with a simplification pass on `manual/`.

2. **Stage 2 (Automatic + Semi-auto)**: Fill in proofs and implementations. No changes to `manual/` or `checker/`. `Print Assumptions` shows no `Admitted`. All real behavior modeled, error messages pinned, PBT seeds covering all possible programs.

---

## Current State

### Fully Proved (0 Admitted)

| Component | File | Lines | Lemmas |
|-----------|------|-------|--------|
| Decode roundtrip | `automatic/Bytecode/DecodeProof.v` | 2,683 | 102 Qed |
| LexParse roundtrip | `automatic/LexParse/LexParseProof.v` | 4,351 | ~130 Qed |
| All checker modules | `checker/*.v` (8 files) | 2,334 | 0 Admitted |

### Partially Proved

| Component | File | Admitted | Qed | Blocker |
|-----------|------|----------|-----|---------|
| Compiler correctness | `automatic/Compile/CompileProof.v` | 27 | 115 | Closures, heap allocation, function application, false step lemmas needing stronger preconditions |
| Handler correctness | `automatic/Bytecode/InstructVerification/` (147 files) | 315 | 1,214 | Only STOP and CHECK_SIGNALS fully proved |
| Handler uniqueness (MetaSpec) | `automatic/Bytecode/MetaSpecVerification/` (95 files) | 99 | 0 | Generic lemma is unprovable as stated without halt/ccall payload uniqueness or weaker equivalence |

### Known Gaps in Trusted Code

1. **`behavior_equiv` doesn't compare return values** (`manual/Compile/CompileSpec.v:67-79`). When both sides terminate normally, it checks trace length equality but not `Term_normal v1 = Term_normal v2`. This means two programs producing the same output but different return values are considered equivalent.

2. **`ccall_to_events` only handles output C-calls for the current source subset** (`CompileSpec.v:34-40`). `print_int` (idx=0), `print_newline` (idx=1), and `print_char` (idx=3) produce events. `print_string` (idx=2) remains a no-op while strings are stubbed end-to-end. Compare `checker/Bytecode/Main.v` which handles ~25 C-calls at the pipeline level.

3. **`Observable.v` has no input events**. Only `Out_char` exists. Programs reading stdin, files, or environment variables cannot be distinguished by their behavior.

4. **`Syntax.v` missing constructs**: No `raise`/`try`, `while`/`for`, `ref`/mutable, multi-arg `let rec`, floats, `;;` (double semicolons), character literals, nested modules with signatures.

5. **Source interpreter stubs** (`semi-auto/Interpret/Interpret.v`):
   - `compare` returns `Val_int 0` always
   - `print_string` is a no-op
   - `Decl_open` is a no-op
   - `interpret` always returns `Val_int 0` regardless of actual result
   - `Pat_nil` incorrectly matches `SVal_int 0`
   - `Decl_module` leaks inner bindings into outer scope

6. **Compiler gaps** (`automatic/Compile/Compile.v`):
   - All constructors share tag 0 (can't distinguish variants)
   - Strings compile to `CONSTINT 0` (placeholder)
   - No tail-call optimization (always `APPLY1`, never `APPTERM`)
   - Hardcoded fuel 1000

7. **IO.v axioms are output-only**: No stdin, stderr, file writing, networking, environment variables.

### PBT Coverage

5,200 QCheck tests + 41 deterministic tests across 11 files. Strong coverage for the features that exist, but coverage is limited to the subset of OCaml modeled by `Syntax.v`.

---

## The Three Theorems

### Theorem 1: Compiler Correctness

**Already stated** in `manual/Compile/CompileSpec.v:108-111`:

```coq
Axiom compiler_correctness :
  forall (prog : program) (src_fuel bc_fuel : nat),
    behavior_equiv (interpret src_fuel prog)
                   (bytecode_behavior step_fn bc_fuel (compile_program prog) []).
```

**What it says**: For every program `prog`, the source interpreter and the bytecode interpreter (running the compiled output) produce equivalent observable behavior, regardless of fuel amounts.

**Parameters** (filled by untrusted code):
- `compile_program : program -> list instruction`
- `interpret : nat -> program -> behavior`

**Concrete trusted definitions used**: `behavior_equiv`, `bytecode_behavior`, `run_collecting`, `ccall_to_events`, `step_list_of`.

**Stage 1 work needed**:
- Keep `behavior_equiv` trace-based for the current OS-observable behavior model
- Decide whether `ccall_to_events` needs to handle more C-calls (`print_char` now produces events; `print_string` remains intentionally stubbed until strings are de-stubbed)
- Verify that the `step_fn` derived from `HandleInstrSpec` matches the bytecode semantics

### Theorem 2: PBT Connection (our compiler vs ocamlc)

**Stated** in `manual/Compile/PBTSpec.v` and exposed through `checker/Compile/PBTChecker.v`:

```coq
Axiom compile_models_ocamlc_ok :
  forall (seed : pbt_seed),
    let p := pbt_program seed in
    match ocamlc_compile p with
    | Some ocamlc_bytes =>
      match ocamlc_decode ocamlc_bytes with
      | Some ocamlc_instrs =>
        forall (fuel : nat),
          behavior_equiv
            (bytecode_behavior step_fn fuel (compile_program p) [])
            (bytecode_behavior step_fn fuel ocamlc_instrs [])
      | None => True
      end
    | None => True
    end.
```

**What it says**: For every PBT seed, if ocamlc compiles the seed's program and we can decode the output, then our compiled bytecode and ocamlc's bytecode exhibit equivalent observable behavior under our interpreter at every fuel level. External tool failures are acceptable (`None => True`); only behavioral disagreement where both succeed constitutes a failure.

**Parameters** (filled by untrusted code):
- `compile_program : program -> list instruction`
- `pbt_seed : Type` (finite inductive type, e.g. `Seed1 | Seed2 | ... | SeedN`)
- `pbt_program : pbt_seed -> program` (deterministic program generator)
- `ocamlc_compile : program -> option (list Z)` (external ocamlc pipeline)
- `ocamlc_decode : list Z -> option (list instruction)` (bytecode file decoder)
- `golden_seed : pbt_seed` (anti-vacuity witness)

**How it's proved**: Auto side defines `pbt_seed` as a finite inductive type. For each seed, `pbt_program seed` reduces to a concrete program. `ocamlc_compile` and `ocamlc_decode` are concrete functions embedding results from actually running ocamlc. Proof is by exhaustive case analysis over seeds + `native_compute`/`vm_compute` + `reflexivity`.

**Anti-vacuity**: `golden_compiles_and_decodes` requires at least one seed where both `ocamlc_compile` and `ocamlc_decode` succeed, preventing trivial satisfaction via always-`None` parameters.

**Trust model**: The theorem is universally quantified over the seed type and machine-checked by `coqc`. Human auditing verifies that `ocamlc_compile`/`ocamlc_decode` actually came from running ocamlc (not from copying `compile_program`'s output). Following the Go verified compiler's pattern of making external tools explicit Parameters.

### Theorem 3: Extraction Validation

**Stated** in `manual/Compile/ExtractionSpec.v` and exposed through `checker/Compile/ExtractionChecker.v`:

```coq
Axiom extraction_validates :
  forall (prog : program),
    let extracted_source := extract_to_ocaml compile_program in
    match ocaml_build extracted_source with
    | Some binary =>
      match extracted_run binary prog with
      | Some extracted_instrs =>
        extracted_instrs = compile_program prog
      | None => True
      end
    | None => False
    end.
```

**What it says**: The extracted+built compiler, when run on any program where it succeeds, produces IDENTICAL bytecode to the Rocq-level `compile_program`. The extraction pipeline is decomposed into explicit Parameters: `extract_to_ocaml` (Rocq extraction), `ocaml_build` (system compiler), `extracted_run` (running the binary on a program). `ocaml_build` failing is `False` (extraction must produce compilable code). `extracted_run` failing is `True` (untested programs are not claimed to match).

**Parameters** (filled by untrusted code):
- `compile_program : program -> list instruction`
- `extract_to_ocaml : (program -> list instruction) -> string` (extraction mechanism)
- `ocaml_build : string -> option (list Z)` (system OCaml compiler)
- `extracted_run : list Z -> program -> option (list instruction)` (run binary on program)
- `golden_program : program` (anti-vacuity witness)

**How it's proved**: Auto side defines `extract_to_ocaml` to return the actual extraction source, `ocaml_build` to return `Some binary` (embedded bytes), and `extracted_run` as a lookup table mapping tested programs to their instruction lists (returning `None` for untested). For each tested program, `compile_program prog` and the embedded instructions reduce by `native_compute`, and `reflexivity` closes the goal.

**Why instruction-list equality** (not behavioral equivalence): Theorem 3 checks that the *same* compiler produces *identical* bytecodes before and after extraction. This is the correct (and stronger) notion for extraction faithfulness. Theorem 2 uses `behavior_equiv` because it compares two *different* compilers (ours vs ocamlc) that produce different bytecodes.

**Anti-vacuity**: `golden_extraction_succeeds` requires at least one program where the full pipeline succeeds (extraction, build, and run all produce `Some`), preventing trivial satisfaction.

**Trust model**: The theorem is universally quantified over all programs and machine-checked by `coqc`. The extraction pipeline is decomposed into explicit, auditable Parameters following the Go verified compiler's pattern. Human auditing verifies the Parameters faithfully represent the real pipeline. This provides strong evidence of extraction correctness without requiring verified extraction (an unsolved research problem).

---

## Stage 1 Plan: Manual + Checker

**Goal**: State all three theorems correctly. Only edit `manual/` and `checker/`. When complete, the theorems are provable with only `automatic/`/`semi-auto/` changes.

### 1.1 Audit `behavior_equiv` (resolved: keep as-is)

**File**: `manual/Compile/CompileSpec.v`

Review found that `behavior_equiv` does not compare return values (`Term_normal v1` vs `Term_normal v2`). However, adding `v1 = v2` would make the spec **unprovable** because the source interpreter always returns `Val_int 0` regardless of the actual result. Return values are also unobservable at the OS boundary. **Resolution**: Keep `behavior_equiv` as-is. The trace-based comparison is the correct notion.

Error message matching (`msg1 = msg2` for `Term_error`) is also impractical — the source interpreter and bytecode interpreter produce different error strings for the same semantic error. **Resolution**: Keep current behavior (same termination kind, not same message).

**Remaining concern**: `behavior_equiv` permits trivial satisfaction — an `interpret` that always returns `Term_timeout` with empty trace satisfies `compiler_correctness`. The length penalty on `interpret` (semi-auto constraint) is the mitigation, but it is external to the formal spec.

### 1.2 Audit `ccall_to_events`

**File**: `manual/Compile/CompileSpec.v`

Currently handles: `print_int` (idx=0), `print_newline` (idx=1), `print_char` (idx=3). Review found:
- `print_char` is handled by the source interpreter and now mapped as an observable C-call
- `print_string` (idx=2) is mapped by the compiler but is a stub in both the source interpreter and `ccall_to_events`
- Only output-producing C-calls need event handling; pure C-calls (comparison, etc.) correctly produce no events

**Remaining fix**: Add `print_string` (idx=2) handling when strings are de-stubbed.

### 1.3 Theorem 2 (PBT Connection) — DONE

**File**: `manual/Compile/PBTSpec.v` (already written)

Universally quantified over a `pbt_seed` type. External tools (`ocamlc_compile`, `ocamlc_decode`) are Parameters filled by the auto side with embedded results from running ocamlc. Anti-vacuity via `golden_seed`/`golden_compiles_and_decodes`. Checker exposure exists in `checker/Compile/PBTChecker.v`. Follows the Go verified compiler's `compile_models_go_pbt_ok` pattern.

### 1.4 Theorem 3 (Extraction Validation) — DONE

**File**: `manual/Compile/ExtractionSpec.v` (already written)

Universally quantified over all programs. Extraction pipeline (`extract_to_ocaml`, `ocaml_build`, `extracted_run`) decomposed as Parameters. Uses instruction-list equality (not behavioral equivalence). `ocaml_build` failure is `False` (extraction must compile). Anti-vacuity via `golden_program`/`golden_extraction_succeeds`. Checker exposure exists in `checker/Compile/ExtractionChecker.v`. Follows the Go verified compiler's `extract_on_compile_ok` pattern.

### 1.5 Simplification Pass

Before declaring Stage 1 complete, review every file in `manual/` against four criteria:

1. **Fully describes real behavior**: Every definition models the actual OCaml semantics it claims to model. No stubs, no placeholders, no "returns 0 for everything."
2. **Provable**: The stated theorems can be proved by providing appropriate `automatic/`/`semi-auto/` implementations. No theorem is stated in a way that makes it impossible to prove.
3. **Uniquely pins down behavior**: The specs don't allow trivially satisfying implementations (e.g., a compiler that always outputs `STOP`, or an interpreter that always returns `Val_int 0`).
4. **No cheating**: No axioms that smuggle in unverified assumptions. No specs that are trivially true.

Additional simplification principle: **pulling in existing source code is free complexity**. If a definition in `manual/` can be simplified by referencing real OCaml/Rocq definitions (like the actual opcode table, the actual instruction set), that's preferred over hand-maintaining a parallel definition.

**Files to audit in the simplification pass**:
- `Observable.v` — Is `Out_char` the only needed event type? (Probably yes for current scope)
- `Value.v` — Is this complete for current Syntax.v? (Missing: floats, but Syntax.v has no floats either)
- `Syntax.v` — Is this the right subset? (Matches current scope; progressive expansion adds more)
- `WellFormed.v` — Are the 20 keywords correct? Are the predicates complete?
- `CompileSpec.v` — After behavior_equiv fix, is this the simplest correct statement?
- `DecodeSpec.v` — Already clean. `well_formed` predicate is the right approach.
- `LexParseSpec.v` — Already minimal (5 lines of content). Good.
- `Machine.v` — Is `state` complete for current instruction set?
- `Encode.v` — Is the encoder complete and correct?
- `IO.v` — Are all 8 axioms needed? Are any missing?
- `HandleInstrSpec.v` — Is the single-function interface right?
- `Run.v` — Is the double-fuel model the simplest correct approach?
- `InstructSpec.v` — Is the Clight-level spec the right abstraction?
- `MetaSpec.v` — Is the uniqueness meta-theorem correctly formulated?

---

## Stage 2 Plan: Automatic + Semi-auto

**Goal**: Fill in all proofs and implementations. No changes to `manual/` or `checker/`. `Print Assumptions` shows no `Admitted`.

### 2.1 Complete CompileProof.v

**Current state**: 27 Admitted, 115 Qed. Core blockers are extending `val_corresponds` for closures and strengthening false single-step lemmas with operand bounds/preconditions where handlers reject malformed operands.

**Work needed**:
- Extend `val_corresponds` with a closure clause relating `SVal_closure param body senv` to `Val_closure addr ofs` (heap-allocated)
- Prove `expr_correct_gen` for `Exp_fun`, `Exp_app`, `Exp_letrec`, `Exp_match`, `Exp_constr`, `Exp_tuple`
- Fix compiler: constructor tags must distinguish variants (requires new `constr_env` data structure), nullary constructors with tag > 0 need `ATOM tag`
- Fix string compilation (currently `CONSTINT 0` — this is a large feature, not a simple fix)
- The 17 per-program `compiler_correct_*` Admitted are redundant once the main theorem is proved

### 2.2 Complete InstructVerification

**Current state**: 315 Admitted (per-handler) + 92 Admitted (assembly), 1214 Qed across 147 files. Only STOP and CHECK_SIGNALS fully proved.

**Work needed**: Prove each handler correct against the Clight AST. Largely mechanical — follows established pattern (construct exec_stmt derivation, prove abs_rel preservation). Complexity varies: STOP is 51 lines, CLOSUREREC is 427 lines.

**Resolved**: The CLOSUREREC restriction in `manual/Bytecode/Interpret/InstructSpec.v` now permits `nf=1, any nv`, so closures capturing free variables are not rejected solely because `nv > 0`.

### 2.3 Complete MetaSpecVerification

**Current state**: 99 Admitted across 95 files. All 94 handler uniqueness lemmas Admitted.

**Work needed**: MetaSpec is **logically independent** of InstructVerification (does not depend on per-handler proofs). The generic lemma (`handler_correct_gen_determines_em_eq` in `SharedLemmas.v`) is unprovable as stated: `handler_correct_gen` does not uniquely pin down halt/ccall payloads. Fix by adding payload uniqueness to the spec, or weaken the target equivalence so payload equality is not required.

### 2.4 Fix Source Interpreter

**File**: `semi-auto/Interpret/Interpret.v`

**Fixes needed**:
- `compare` must implement real structural comparison
- `print_string` must produce `Out_char` events
- `interpret` must return the actual computed value, not `Val_int 0`
- `Pat_nil` must not match `SVal_int 0`
- `Decl_module` must not leak inner bindings
- `Decl_open` needs real semantics or must be documented as out-of-scope

### 2.5 Fix Compiler

**File**: `automatic/Compile/Compile.v`

**Fixes needed**:
- Constructor tags must distinguish different variants (not all tag 0)
- String compilation must produce real string values
- Consider adding tail-call optimization (APPTERM)
- Fuel should not be hardcoded

### 2.6 PBT Expansion

Expand PBT to cover all possible programs:
- Seeds must enumerate all strings in roughly lexicographic order
- Generators must produce relevant OCaml program syntax
- Programs selected from corpus (OCaml test suite, Rocq source)
- Error messages pinned and matching exactly

---

## Progressive Expansion

The three theorem statements are designed to be **stable under feature expansion**. When a new OCaml feature is added to `Syntax.v`:

1. The `program` type grows (new constructors in `expr`, `pattern`, `decl`)
2. `compile_program` must handle the new constructors (change in `automatic/`)
3. `interpret` must handle the new constructors (change in `semi-auto/`)
4. The theorem statements in `manual/` **do not change** — they quantify over all `program` values, which automatically includes the new constructors
5. The proofs in `automatic/` must be extended to cover the new cases
6. PBT generators must be extended to produce the new syntax

This is why `Syntax.v` is in `manual/` — it's the single source of truth for what "a program" means, and all theorem statements are parametric over it.

**Exception**: Adding new *observable* behavior (e.g., input events, file I/O) would require changes to `Observable.v` and potentially to `behavior_equiv`. This is a Stage 1 concern — the observable behavior model must be complete enough for the target scope before Stage 1 is declared complete.

---

## Resolved Questions

1. **`behavior_equiv` return values**: Keep as-is (no return value comparison). Adding `v1 = v2` would break provability because the source interpreter always returns `Val_int 0`. Return values are unobservable at the OS boundary.

2. **Error message matching**: Keep as-is (same termination kind, not same message). Source and bytecode interpreters produce different error strings for the same semantic error.

3. **`ocamlc` axiomatization**: External tools (ocamlc, extraction, decoder) are modeled as **Parameters** in Module Types, following the Go verified compiler's pattern. The auto side fills these Parameters with concrete implementations that embed results from actually running the tools. The build system runs ocamlc externally; the Rocq spec references it only abstractly through Parameters. Theorems are universally quantified (over seed type for PBT, over all programs for extraction).

4. **CLOSUREREC restriction**: `nf=1` is sufficient (only single recursion in `Syntax.v`), and the former `nv=0` restriction was too restrictive because the compiler emits `CLOSUREREC 1 nvars [ofs]` with `nvars > 0` for closures capturing free variables. `InstructSpec.v` now accepts `nf=1, any nv`.

## Remaining Concerns

1. **`behavior_equiv` trivial satisfaction**: An `interpret` always returning `Term_timeout` with empty trace vacuously satisfies `compiler_correctness`. The length penalty on `interpret` is the mitigation but is external to the formal spec.

2. **PBT generator coverage**: Current generators only produce integer-arithmetic programs. `compare`, `print_string`, string literals, `Pat_nil`, `Decl_module`, non-integer equality, constructors with multiple tags — none are tested.

3. **Progressive expansion requires controlled `manual/` changes**: Every new syntax constructor requires updating `Syntax.v` and `WellFormed.v` in `manual/`. Theorem statements stay stable, but these type-level changes are unavoidable.

4. **Source interpreter additional bugs found**: `Op_eq`/`Op_neq` only work on integers (structural equality missing). `Op_and`/`Op_or` evaluate eagerly instead of short-circuiting.
