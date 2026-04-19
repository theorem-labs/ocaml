# Plan: Uniqueness Meta-Specification for Handler Correctness

## Goal

Produce a single machine-checked meta-theorem, parameterized over
instructions, stating:

> For every instruction `i`, any two `handler : Z -> state -> step_result`
> that satisfy the `handler_correct` obligation for `i` agree on every
> state up to the contents of error message strings.

Call this relation **error-message equivalence** (`em_eq`). Two
`step_result`s are `em_eq` iff they are:
- both `Step s'` with the same `s'`,
- both `Halt v` with the same `v`,
- both `CCall_request n args s'` with the same `(n, args, s')`, or
- both `Error _` (message contents ignored).

Once the meta-theorem holds, `handle_*` in `Interpret.v` can in principle
be replaced by *any* function satisfying the specs — the observable
semantics is fixed. This is the missing justification for shrinking
`Interpret.v` by deferring implementations to specifications.

## Non-goals

- Not (yet) actually replacing `handle_*` with specs — this plan delivers
  the *justification*. Replacement is a separate step.
- Not changing what any individual handler does today; only moving code.
- Not touching PBT extraction — `handle_instr` stays executable.

## Where the plan lives in the tree

- New subdirectory: `manual/Bytecode/Interpret/`
  - `MetaSpec.v` — Module Type (interface) with the uniqueness theorem.
  - `MetaSpecChecker.v` — `Module Check <: MetaSpec` ascribing the
    theorem against proofs (or `Admitted` placeholders, see "Phasing").
- Edits to existing file: `manual/Bytecode/Interpret.v` — factor the big
  `match` in `step` into a free-standing `handle_instr`.
- Edits to existing file: `manual/Bytecode/InstructSpec.v` — introduce the
  `HandlerSpecBundle` record and `spec_of : instruction -> HandlerSpecBundle`
  dispatch function, so that the meta-spec can quantify over *one* thing
  instead of 151.

Generator-local md plans (this file, `EXTRACT_SIMPLIFICATION_PLAN.md`,
`INTERPRET_FUNCTOR_PLAN.md`) live in `manual/Bytecode/generator/`. The
per-handler verification plans (`PLAN.md` / `PROGRESS.md`) live in
`automatic/Bytecode/InstructVerification/`.

## Core definitions

### 1. Error-message equivalence

```coq
Inductive em_eq : step_result -> step_result -> Prop :=
  | em_Step  s  : em_eq (Step s)  (Step s)
  | em_Halt  v  : em_eq (Halt v)  (Halt v)
  | em_CCall n args s' : em_eq (CCall_request n args s') (CCall_request n args s')
  | em_Error msg msg' : em_eq (Error msg) (Error msg').
```

Reflexive by construction; symmetric and transitive by inversion.
(Consider: define as a function `em_eqb` and derive the `Prop` from
equality on the non-message projections — simpler reasoning.)

### 2. Handler spec bundle

```coq
Record HandlerSpecBundle := {
  hs_handler  : Z -> state -> step_result;
  hs_clight   : function;
  hs_step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop;
  hs_P_error  : string -> state -> Prop;
  hs_P_halt   : value -> Prop;
  hs_P_ccall  : nat -> list value -> state -> Prop;
}.

Definition handler_correct_bundle (b : HandlerSpecBundle) : Prop :=
  handler_correct b.(hs_handler) b.(hs_clight) b.(hs_step_pre)
                  b.(hs_P_error) b.(hs_P_halt) b.(hs_P_ccall).
```

### 3. Per-instruction spec dispatch

```coq
Definition spec_of (i : instruction) (pc' : Z) : HandlerSpecBundle :=
  match i with
  | ACC n                  => {| hs_handler  := handle_ACC n pc'; ... |}
  | PUSH                   => {| hs_handler  := handle_PUSH pc'; ... |}
  ...
  | STOP                   => {| hs_handler  := fun _ s => handle_STOP s; ... |}
  end.
```

This captures in one match what `InstructSpec.v` currently spreads across
151 `Parameter` declarations. The 151 existing parameters are equivalent
to `forall i, handler_correct_bundle (spec_of i pc')`. The existing
`InstructVerification.v` module becomes one universally-quantified
theorem.

### 4. The meta-theorem

```coq
Definition handler_matches (h : Z -> state -> step_result)
                           (b : HandlerSpecBundle) : Prop :=
  handler_correct h b.(hs_clight) b.(hs_step_pre)
                  b.(hs_P_error) b.(hs_P_halt) b.(hs_P_ccall).

Parameter handler_unique_mod_errors :
  forall i pc' h1 h2,
    handler_matches h1 (spec_of i pc') ->
    handler_matches h2 (spec_of i pc') ->
    forall s, em_eq (h1 pc' s) (h2 pc' s).
```

One statement, quantifies over every instruction.

## Refactor: split `step` into dispatch + handlers

Current `step` in `Interpret.v` (lines 1004-1110) is a single big match
that fetches and dispatches. After refactor:

```coq
Definition handle_instr (i : instruction) (pc' : Z) (s : state) : step_result :=
  match i with
  | ACC n   => handle_ACC n pc' s
  | PUSH    => handle_PUSH pc' s
  ...
  end.

Definition step (code : array instruction) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | None   => Error "pc out of bounds"
  | Some i => handle_instr i (s.(pc) + 1) s
  end.
```

Shape goals:
- `handle_instr` is the sole caller of every `handle_*`.
- `step` becomes three lines.
- `spec_of` (in `InstructSpec.v`) and `handle_instr` (in `Interpret.v`)
  have isomorphic match structures. A sanity lemma
  `handle_instr i pc' s = (spec_of i pc').(hs_handler) pc' s` is true by
  definition after the refactor.

## Why the meta-theorem doesn't hold today

The current `handler_correct` lets two handlers diverge in at least
three ways on a single input state `s`:

1. **`step_pre`-false states.** The Step branch reads
   `step_pre → ∃ le' m', exec_stmt ... ∧ abs_rel`. If `step_pre` is
   false for `(e, m, s, ard)`, the implication is vacuous and the
   handler may return `Step s'` for any `s'`.

2. **States with no `abs_rel` witness.** If no `(e, le, m, ard)`
   represents `s`, the entire `forall e le m ...` premise is vacuous.

3. **Over-permissive `P_error`.** Where `P_error msg s = True` (or
   a trivially-satisfiable disjunction), the handler can return
   `Error msg'` for any `msg'` *or* return `Step s'` freely
   on step_pre-false states. The current `P_error = fun _ _ => True`
   in 15 handlers (see `automatic/Bytecode/InstructVerification/PLAN.md`
   Issue 2) is the stark case.

4. **`abs_rel` might be relational.** Two distinct abstract states
   `s1 ≠ s2` might both be in `abs_rel` with the same concrete
   post-state. If so, the Step post-state isn't uniquely determined
   even under (1)-(3).

So `handler_unique_mod_errors` is false as stated against the *current*
Parameter declarations. Making it a theorem requires strengthening along
each axis.

## Strengthening obligations (what the Checker actually checks)

For each instruction, `MetaSpecChecker.v` must discharge:

**Obligation A — step_pre totality.**
```coq
forall i pc' s, <step-outcome s i pc'> <->
  exists e le m ard,
    abs_rel_with_ard e le m s ard /\ (spec_of i pc').(hs_step_pre) e m s ard.
```
Here `<step-outcome ...>` characterizes purely abstractly when the
handler *should* return `Step`. This couples the abstract and concrete
sides and is the meat of the work.

**Obligation B — `abs_rel` functional on post-states.**
```coq
Lemma abs_rel_functional :
  forall e le m s1 s2,
    abs_rel e le m s1 -> abs_rel e le m s2 -> s1 = s2.
```
Shared across all handlers; goes in `Machine.v` or a new
`manual/Bytecode/MachineInvariants.v`. Likely requires additional
fields in `state` to be observables of memory (PC / SP / accu already
are; heap / env require care).

**Obligation C — `P_error` is the exact error indicator.**
```coq
forall i pc' s,
  (exists msg, (spec_of i pc').(hs_P_error) msg s) <->
  <no-step-outcome s i pc' /\ no-halt /\ no-ccall>.
```
The 15 `fun _ _ => True` predicates flagged in
`automatic/Bytecode/InstructVerification/PLAN.md` violate the forward
direction; the `BLTINT` pattern (`msg = "..." /\ match accu with Val_int _
=> False | _ => True`) satisfies both directions. The fix set in that
`PLAN.md` Step 7 is a prerequisite.

**Obligation D — outcome kinds are mutually exclusive.**
```coq
forall i pc' s,
  at_most_one_of [step, halt, error, ccall] (spec_of i pc') s.
```
Usually holds because `P_halt` / `P_ccall` are `fun _ => False` for
almost every handler. A shared tactic can discharge 130+ of these.

With A-D in place, `handler_unique_mod_errors` follows by:

```
suppose handler_matches h1 (spec_of i pc') and similarly for h2.
case analysis on (h1 pc' s):
| Step s1' =>
    by (A), step_pre holds, abs_rel witness exists.
    by handler_correct, Clight body executes; abs_rel holds on post.
    by (B), s1' is unique.
    by (D), h2 pc' s is also Step; same derivation gives h2 pc' s = Step s1'.
| Halt v => (D) forces h2 pc' s = Halt v; em_Halt.
| CCall_request n args s' => (D) forces h2 pc' s = CCall_request n args s';
    P_ccall pins (n, args, s').
| Error msg =>
    by (C), step/halt/ccall don't hold, so h2 pc' s is Error _;
    em_Error (messages free).
```

Proof is ~40 lines once the four obligations are in place.

## Phasing

### Phase 1 — refactor only (no new theorems)
1. Introduce `handle_instr` in `Interpret.v`; rewrite `step` to use it.
   Pure refactor; `make -f Makefile.coq.checker` stays green.
2. Introduce `HandlerSpecBundle` and `spec_of` in
   `manual/Bytecode/InstructSpec.v`. Add a lemma
   `handler_correct_bundle_of_parameters :
   forall i pc', handler_correct_bundle (spec_of i pc')`, proven by
   `match i; apply correct_<OP>`. This is ~200 lines of boilerplate,
   mechanical.
3. Create `manual/Bytecode/Interpret/MetaSpec.v` with the
   `em_eq`, `handler_matches`, and `handler_unique_mod_errors`
   declarations. No proofs yet.
4. Create `manual/Bytecode/Interpret/MetaSpecChecker.v` with
   `Module Check <: MetaSpec.` and `Admitted.` on
   `handler_unique_mod_errors`. Whole-tree build stays green; the
   interface is in place.

### Phase 2 — shared obligations
5. Prove `abs_rel_functional` (Obligation B). Shared; one lemma.
6. Prove `outcome_exclusive` (Obligation D) with one reusable tactic.
7. These together reduce the Meta-Theorem to Obligations A+C only.

### Phase 3 — per-handler obligations
8. For each instruction `i`, prove:
   - `step_pre_total_<OP>` (Obligation A specialized to `i`).
   - `P_error_characterizes_<OP>` (Obligation C specialized to `i`).
   Co-located with the existing
   `automatic/Bytecode/InstructVerification/<OP>_correct.v` proof, or in a
   sibling `<OP>_meta.v` if keeping files separate. ~15 lines per handler
   after the error-predicate fixes in
   `automatic/Bytecode/InstructVerification/PLAN.md` land.
9. Discharge `handler_unique_mod_errors` by assembling A+B+C+D per
   instruction; one central proof using the per-handler lemmas.

### Phase 4 — optional follow-on
10. With the meta-theorem in place, *demonstrate* replacement by
    introducing `handle_instr_abstract : Z -> state -> step_result`
    declared as a Parameter satisfying `handler_matches`, and proving
    observational equivalence with the concrete `handle_instr` via
    `handler_unique_mod_errors`. This is the payoff — Interpret.v can
    shrink by swapping implementations for specifications while
    preserving correctness-theorem-level semantics (modulo error
    messages, which PBT doesn't compare against anyway).

## Dependencies & ordering

- Phase 1 is independent; land first.
- Phase 2 depends on Phase 1 #2 (the bundle).
- Phase 3 depends on Phase 2 *and* on the error-predicate strengthening
  already queued in `automatic/Bytecode/InstructVerification/PLAN.md`
  Step 7. Do that one first.
- Phase 4 is strictly optional and orthogonal to the rest of the
  verification effort.

## Files touched

| File | Phase | Action |
|------|-------|--------|
| `manual/Bytecode/Interpret.v` | 1 | Factor `step` → `handle_instr` + 3-line `step` |
| `manual/Bytecode/InstructSpec.v` | 1 | Add `HandlerSpecBundle`, `spec_of`, bundle-collecting lemma |
| `manual/Bytecode/Interpret/MetaSpec.v` | 1 | New — Module Type with `em_eq`, `handler_matches`, meta-theorem |
| `checker/Bytecode/MetaSpecChecker.v` | 1 | New — `Module Check <: MetaSpec` with Admitted meta-theorem |
| `manual/Bytecode/Machine.v` (or new `MachineInvariants.v`) | 2 | Prove `abs_rel_functional` |
| `manual/Bytecode/InstructSpec.v` | 2 | Prove `outcome_exclusive` shared tactic-lemma |
| 151 × per-handler obligation proofs under `automatic/Bytecode/InstructVerification/` | 3 | `step_pre_total_<OP>` + `P_error_characterizes_<OP>` |
| `checker/Bytecode/MetaSpecChecker.v` | 3 | Replace Admitted with `Qed.`; assemble obligations |
| `_CoqProject*` (regenerate via `etc/organize-_CoqProject.sh`) | 1, 3 | Register new files |

## Verification

- After each phase: from `verified-ocaml/`, run the `coq_makefile` flow
  (see CLAUDE.md "Verifying Rocq compilation") with an explicit `.vo`
  target list — never a bare `make -f Makefile.coq.checker` (which
  rebuilds every file in the tier and times out). For each phase name
  only the files that phase touches, e.g.
  `make -f Makefile.coq.checker manual/Bytecode/InstructSpec.vo manual/Bytecode/Interpret/MetaSpec.vo checker/Bytecode/MetaSpecChecker.vo`.
  No newly Admitted or new Axioms beyond the known `Admitted` in
  `checker/Bytecode/MetaSpecChecker.v` during Phase 1-2.
- After Phase 3: `Print Assumptions handler_unique_mod_errors.` lists
  zero axioms beyond `abs_rel_functional`'s dependencies (which should
  themselves be axiom-free).
- After Phase 4: `Print Assumptions <final-wrapper>.` confirms that the
  spec-driven `step` has the same `em_eq` behavior as the
  implementation-driven one.

## Open questions to resolve before starting

1. Does `abs_rel` today actually admit a functional proof, or do we
   need new state invariants (e.g. `heap_block_well_formed` from
   `automatic/Bytecode/InstructVerification/PROGRESS.md` Phase 6A)? If
   the latter, those invariants are a prerequisite for Phase 2.
2. Should `spec_of` be a Definition (match on `instruction`) or a
   typeclass dispatch? Definition is simpler and sufficient; typeclass
   adds inference overhead without proof benefit.
3. How much of the `step_pre_total_<OP>` obligation can be absorbed
   into a shared precondition builder (`accu_check`, `code_at`, etc.)
   already in `InstructSpec.v`? The compositional structure there
   suggests ~30% of Obligation A can be discharged once at the
   combinator level, not per-handler.
