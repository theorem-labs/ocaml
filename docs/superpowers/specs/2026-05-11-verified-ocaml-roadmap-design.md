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
| LexParse roundtrip | `automatic/LexParse/LexParseProof.v` | 4,351 | 135 Qed |
| Handler uniqueness (MetaSpec) | `automatic/Bytecode/MetaSpecVerification/` (95 files) | 0 Admitted | 126 Qed |
| All checker modules | `checker/` (10 `.v` files) | 2,354 | 0 Admitted |

### Partially Proved

| Component | File | Admitted | Qed | Blocker |
|-----------|------|----------|-----|---------|
| Compiler correctness | `automatic/Compile/CompileProof.v` | 1 real admit (2 text occurrences; 1 is in a comment) | 199 | Final theorem remains over-broad for current source/compiler semantics; false unbounded step admits are removed, unbound variables now compile to a bytecode error, deterministic constructor tag hashing and record field reordering are in place, source-level max bindings are removed, and concrete int/seq/neg/add/sub/mul/if/let/print/unbound-var examples are proved with explicit in-range/out-of-range/error cases |
| Handler correctness | `automatic/Bytecode/InstructVerification/` plus `automatic/Bytecode/InstructVerificationProof.v` | Gate is 317 admits total; IVP has 85 remaining | 1,256+ | 11 handler files are fully closed (`ATOM0`, `CHECK_SIGNALS`, `CONST0`, `CONST1`, `CONST2`, `CONST3`, `C_CALL`, `PUSHACC`, `RAISE_NOTRACE`, `RERAISE`, `STOP`). `InstructVerificationProof.v` has 10 canonical wrappers wired: newer `CONSTINT`, `PUSHCONSTINT`, `PUSHENVACC`, `PUSHACC` plus pre-existing `STOP`, `CHECK_SIGNALS`, `C_CALL`, `GETBYTESCHAR`, `RERAISE`, `RAISE_NOTRACE`. Remaining admits are structurally blocked by `pre_of` not implying exact operand types, `handler_correct` requiring an exact `Step` post-state, and `R_ex` preservation across heap mutation for the `MAKEBLOCK` family |
| PBT connection auto obligations | `automatic/Compile/PBTProof.v` | 0 `Admitted`, 0 local `Axiom`/`Parameter` placeholders | 3 | Checker interface exists with a minimal concrete golden-seed witness table; still needs generated ocamlc/decode evidence expansion |
| Extraction validation auto obligations | `automatic/Compile/ExtractionProof.v` | 0 `Admitted`, 0 local `Axiom`/`Parameter` placeholders | 2 | Checker interface exists with concrete witness definitions; still needs generated extraction/build/run evidence expansion |

### Known Gaps in Trusted Code

1. **`behavior_equiv` doesn't compare return values** (`manual/Compile/CompileSpec.v:67-79`). When both sides terminate normally, it checks trace length equality but not `Term_normal v1 = Term_normal v2`. This means two programs producing the same output but different return values are considered equivalent.

2. **`ccall_to_events` only handles output C-calls for the current compiled subset** (`CompileSpec.v:34-40`). `print_int` (idx=0), `print_newline` (idx=1), and `print_char` (idx=3) produce events. String concatenation runtime behavior is now fixed for `print_string ("hello" ^ "world")`, but broader `print_string` proof/spec coverage remains incomplete. Compare `checker/Bytecode/Main.v` which handles ~25 C-calls at the pipeline level.

3. **`Observable.v` has no input events**. Only `Out_char` exists. Programs reading stdin, files, or environment variables cannot be distinguished by their behavior.

4. **`Syntax.v` missing constructs**: No `raise`/`try`, `while`/`for`, `ref`/mutable, multi-arg `let rec`, floats, `;;` (double semicolons), character literals, nested modules with signatures.

5. **Source interpreter remaining caveats** (`semi-auto/Interpret/Interpret.v`):
    - `compare` returns `Val_int 0` always
    - `Op_and`/`Op_or` are strict to match current compiler `ANDINT`/`ORINT`
    - `Op_eq`/`Op_neq` remain int-only to match current bytecode physical equality proof
    - Source-level max bindings have been removed
    - `Decl_open` supports qualified aliases only
    - `Exp_int n` rejects values outside `[Int.min_signed, Int.max_signed]` to match bytecode `CONSTINT`; `Pat_int n` is still not `CONSTINT`-range-checked in source pattern matching, while compiled pattern tests emit `CONSTINT n`

6. **Compiler gaps** (`automatic/Compile/Compile.v`):
    - Constructor tags are now computed by deterministic `constr_tag` hashing, but this is still a local hash-based policy rather than a typed constructor environment; collisions and source/type compatibility remain open.
    - Strings now compile to `ATOM String_tag` / `MAKEBLOCK{1,2,3}` / `MAKEBLOCK String_tag n`, matching `svalue_to_value` for string values. The string-concat NUL byte issue is resolved: `let () = print_string ("hello" ^ "world"); print_newline ()` produces `helloworld\n`, matching `ocamlrun`. Remaining string work is proof coverage and broader runtime representation.
   - No tail-call optimization (always `APPLY1`, never `APPTERM`)
   - Top-level compiler fuel is now AST-derived via `compile_fuel`; remaining work is proof coverage, not replacing a hardcoded `1000`.

7. **IO.v axioms are output-only**: No stdin, stderr, file writing, networking, environment variables.

8. **Concrete MetaSpec uniqueness is conditional** (`manual/Bytecode/Interpret/MetaSpec.v`). The proven uniqueness theorem now explicitly requires totality, functionality, and `pre_of`-holds hypotheses for `abs_rel_with_ard`; proving those concrete hypotheses, or strengthening the relation until they hold, is separate work.

### PBT Coverage

4,641 current passing tests across compile, source, correctness, advanced, Rocq, and LexParse suites. Strong coverage for the features that exist, but coverage is limited to the subset of OCaml modeled by `Syntax.v`.

Latest hand-run PBT pass against the regenerated extraction (after deterministic constructor tag hashing, record field reordering, source-level max binding removal, string-concat fix, and `PBTProof.v`/`ExtractionProof.v` placeholder removal):

- `checker/Compile/test/pbt.exe`: 1300/1300 compile-vs-`ocamlc` pass.
- `checker/Interpret/test/source_interp_test.exe`: 500/500 source-vs-`ocamlc` pass.
- `checker/Interpret/test/correctness_test.exe`: 1500/1500 interpret-vs-`compile+interpret-bytecode` pass.
- `checker/Interpret/test/advanced_test.exe`: 14/14 hand-crafted programs pass.
- `checker/Interpret/test/rocq_source_test.exe`: 27/27 Rocq-style programs pass.
- `checker/LexParse/test/pbt.exe` declaration suite: 300/300 pass.
- `checker/LexParse/test/pbt.exe` expression suite: 1000/1000 pass.
- Runtime correctness regression: `let () = print_string ("hello" ^ "world"); print_newline ()` produces `helloworld\n`, matching `ocamlrun`.

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
- Decide whether `ccall_to_events` needs to handle more C-calls (`print_char` now produces events; string-concat through `print_string` has a passing runtime regression, but general `print_string` observable handling still needs proof/spec coverage)
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
- `print_string` (idx=2) now has a passing string-concat runtime regression, but broader `ccall_to_events`/proof coverage remains incomplete
- Only output-producing C-calls need event handling; pure C-calls (comparison, etc.) correctly produce no events

**Remaining fix**: Finish and prove general `print_string` (idx=2) observable handling beyond the current string-concat regression.

### 1.3 Theorem 2 (PBT Connection) — SPEC/CHECKER WIRED; MINIMAL AUTO WITNESS

**File**: `manual/Compile/PBTSpec.v` (already written)

Universally quantified over a `pbt_seed` type. External tools (`ocamlc_compile`, `ocamlc_decode`) are Parameters in the manual spec and are filled by the auto side with concrete definitions. Anti-vacuity via `golden_seed`/`golden_compiles_and_decodes`. Checker exposure exists in `checker/Compile/PBTChecker.v`; `automatic/Compile/PBTProof.v` is now axiom-free for this interface, using a minimal golden-seed witness table. Remaining work is replacing the minimal table with generated ocamlc/decode evidence. Follows the Go verified compiler's `compile_models_go_pbt_ok` pattern.

### 1.4 Theorem 3 (Extraction Validation) — SPEC/CHECKER WIRED; MINIMAL AUTO WITNESS

**File**: `manual/Compile/ExtractionSpec.v` (already written)

Universally quantified over all programs. Extraction pipeline (`extract_to_ocaml`, `ocaml_build`, `extracted_run`) decomposed as Parameters in the manual spec and filled by automatic concrete definitions. Uses instruction-list equality (not behavioral equivalence). `ocaml_build` failure is `False` (extraction must compile). Anti-vacuity via `golden_program`/`golden_extraction_succeeds`. Checker exposure exists in `checker/Compile/ExtractionChecker.v`; `automatic/Compile/ExtractionProof.v` is now axiom-free for this interface, using concrete witness definitions. Remaining work is replacing the minimal witnesses with generated extraction/build/run evidence. Follows the Go verified compiler's `extract_on_compile_ok` pattern.

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

**Current state**: 1 real `Admitted` (2 text occurrences, one in a comment), 199 Qed, and 0 local automatic placeholders. Recent progress proved `compiler_correct_empty`, `compiler_correct_type_decl`, `compiler_correct_expr_unit`, `compiler_correct_expr_bool`, `compiler_correct_expr_int`, `compiler_correct_seq_ints`, `compiler_correct_not_bool`, `compiler_correct_neg_int`, `compiler_correct_add_ints`, `compiler_correct_sub_ints`, `compiler_correct_mul_ints`, `compiler_correct_if_bool_ints`, `compiler_correct_let_int_var`, `compiler_correct_let_then_add`, `compiler_correct_print_int`, `compiler_correct_let_add`, `compiler_correct_if_int_cmp`, `compiler_correct_unbound_var`, plus bounded CONSTINT, ACC, ENVACC, POP, GETFIELD, CLOSURE, and CLOSUREREC helper lemmas. Source `Exp_int` now returns the same malformed-`CONSTINT` error for out-of-range literals as bytecode, and missing variables now compile to an out-of-range `CONSTINT` so source and bytecode both error. The former `code_pc_well_formed` axiom is gone. Deterministic constructor tag hashing, record field reordering, and source-level max binding removal are in place. The proved seq/add/neg/sub/mul/if-bool/let-var/let-then-add/print-int/let-add/if-int-comparison/unbound-var cases explicitly cover representable, out-of-range, and selected error operands. `Pat_int` remains unresolved: source matching compares integer patterns directly without the `CONSTINT` range policy, but compiled pattern tests use `CONSTINT n`. Core blockers are proving or narrowing the final theorem across remaining source/compiler semantic gaps, especially closures, heap allocation, function application, pattern-match failure paths, broader string printing/runtime behavior, constructor tag policy, modules, record fields, dynamic type errors, and evaluation order.

**Work needed**:
- Extend `val_corresponds` with a closure clause relating `SVal_closure param body senv` to `Val_closure addr ofs` (heap-allocated)
- Prove `expr_correct_gen` for `Exp_fun`, `Exp_app`, `Exp_letrec`, `Exp_match`, `Exp_constr`, `Exp_tuple`
- Finish integer representability and failure behavior for patterns: `Exp_int`-only seq/add/neg/sub/mul/if-bool/let-var/let-then-add/print-int/let-add/if-int-comparison cases now handle both in-range and out-of-range selected literals, but `Pat_int n` still lacks a `CONSTINT`-range policy. A local patch attempted literal/bool/nil final-pattern failure paths via malformed `CONSTINT`, but audit found it is likely in an unreachable branch; other final non-irrefutable patterns can still compile to normal body execution.
- Fix compiler constructor semantics: replace the current local hash-based `constr_tag` policy with a typed constructor environment, handle collisions deliberately, and prove nullary constructor `ATOM tag` behavior.
- Finish broader string semantics beyond literal allocation and the fixed string-concat regression; proof/test coverage for general `print_string` runtime behavior remains incomplete.
- No concrete per-program `compiler_correct_*` admits remain; empty programs, type declarations, unit expressions, bool/int expressions, integer sequence/addition/subtraction/multiplication/negation, boolean `not`, boolean-conditioned integer `if` expressions, integer-comparison-conditioned `if` expressions, simple integer let/var expressions, two-declaration let/add expressions, `print_int; print_newline` expressions, and expression-level let/add expressions are now proved directly

### 2.2 Complete InstructVerification

**Current state**: the overall gate reports `317` admits and `0` placeholders. `InstructVerificationProof.v` has `85` admits remaining and `10` canonical wrappers wired: newer `CONSTINT`, `PUSHCONSTINT`, `PUSHENVACC`, `PUSHACC` plus pre-existing `STOP`, `CHECK_SIGNALS`, `C_CALL`, `GETBYTESCHAR`, `RERAISE`, and `RAISE_NOTRACE`. 11 handler files are fully closed (`admit=0`): `ATOM0`, `CHECK_SIGNALS`, `CONST0`, `CONST1`, `CONST2`, `CONST3`, `C_CALL`, `PUSHACC`, `RAISE_NOTRACE`, `RERAISE`, and `STOP`. `PUSHACC` is fully closed and wired after the case-split breakthrough, with `handle_PUSHACC` tightened to match `instr_wfb` (`1..7` only).

**Work needed**: Prove each handler correct against the Clight AST and fix the structural spec blockers. Generic `pre_of i` does not imply specific operand types (`Vlong` vs `Vptr`), `handler_correct`'s `Step` branch requires identifying the exact abstract post-state while `pre_of` only guarantees some `R_ex` post-state, and `R_ex` preservation across heap mutation remains unresolved for the `MAKEBLOCK` family.

**Resolved**: The CLOSUREREC restriction in `manual/Bytecode/Interpret/InstructSpec.v` now permits `nf=1, any nv`, so closures capturing free variables are not rejected solely because `nv > 0`.

### 2.3 Complete MetaSpecVerification

**Current state**: 0 Admitted and 126 Qed across 95 files. The generic uniqueness lemma and all 94 per-handler uniqueness lemmas are proved.

**Resolved**: MetaSpec is **logically independent** of InstructVerification (does not depend on per-handler proofs). `handler_correct_gen` now uses state-indexed option payload specs for halt/ccall, so `handler_correct_gen_determines_em_eq` can prove exact payload equality. The concrete/fine-grained uniqueness specs now carry the same totality, functionality, and `pre_of`-holds hypotheses as the generic theorem, and every per-instruction lemma delegates to the shared proof.

**Remaining obligation**: Prove or refine the concrete `handler_unique_hyps` assumptions for any future consumer that needs unconditional uniqueness over `abs_rel_with_ard`.

### 2.x Expand PBT/Extraction Witness Evidence

- `automatic/Compile/PBTProof.v` and `automatic/Compile/ExtractionProof.v` no longer contain local `Axiom`/`Parameter` placeholders.
- Replace the current minimal PBT witness table with checked-in generated ocamlc/decode evidence.
- Replace the current minimal extraction witnesses with checked-in extraction/build/run evidence.

### 2.4 Fix Source Interpreter

**File**: `semi-auto/Interpret/Interpret.v`

**Remaining fixes needed**:
- `compare` must implement real structural comparison
- Restore short-circuit `Op_and`/`Op_or` once the compiler emits branch code instead of strict `ANDINT`/`ORINT`
- Widen structural equality once the compiler emits structural equality instead of bytecode `EQ`/`NEQ`
- Decide how to handle out-of-range `Pat_int n` literals: either reject them in source pattern matching like `Exp_int`/`CONSTINT`, restrict them via well-formedness to the `CONSTINT` range, or change compilation so pattern tests do not emit malformed `CONSTINT n`

### 2.5 Fix Compiler

**File**: `automatic/Compile/Compile.v`

**Fixes needed**:
- Constructor tags must come from a typed constructor environment instead of the current deterministic local hash policy.
- String literals now produce `String_tag` blocks, and the string-concat NUL byte issue is fixed; remaining string work is broader observable `print_string` behavior and end-to-end runtime/proof coverage.
- Consider adding tail-call optimization (APPTERM)
- Prove the AST-derived `compile_fuel` bound is sufficient everywhere.
- Fix source/compiler evaluation-order mismatches for effectful subexpressions.
- Finish module semantics/proofs for qualified aliases and accepted dotted-name representation; inner `STOP` stripping and compiler-side `Decl_open` are implemented.
- Finish record field ambiguity semantics; record fields are now reordered deterministically and missing field lookup uses a sentinel instead of defaulting to index `0`.
- Align builtin coverage with the source stdlib; direct builtin special-casing is now shadowing-aware.

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

2. **PBT generator coverage**: Current generators remain narrow despite the passing string-concat regression. Broader `compare`, `print_string`, string literal, `Pat_nil`, `Decl_module`, non-integer equality, and multi-tag constructor coverage is still needed.

3. **Progressive expansion requires controlled `manual/` changes**: Every new syntax constructor requires updating `Syntax.v` and `WellFormed.v` in `manual/`. Theorem statements stay stable, but these type-level changes are unavoidable.

4. **Source interpreter additional bugs found**: `Op_eq`/`Op_neq` only work on integers (structural equality missing). `Op_and`/`Op_or` evaluate eagerly instead of short-circuiting.
