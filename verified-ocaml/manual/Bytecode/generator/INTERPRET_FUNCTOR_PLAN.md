# Plan: Functorize `Interpret.v` over `handle_instr`

## Goal

Shrink `manual/Bytecode/Interpret.v` by pulling the per-instruction
dispatch (currently the ~100-line `match instr with ... end` inside
`step`) into a `handle_instr` abstraction, and restructure so that:

- `manual/Bytecode/Interpret/HandleInstrSpec.v` exposes a Module Type
  declaring only the `handle_instr` signature.
- `manual/Bytecode/Interpret/Run.v` is a functor `Make (H :
  HandleInstrSpec)` producing `step`, `run_micro`, `handle_bcmicro`,
  `run`, `run_pure`, and any other functions built on top of `step`.
- The *concrete* `handle_instr` implementation — including every
  per-opcode `handle_<OP>` — moves to `automatic/Bytecode/HandleInstr.v`.
  That is the working definition LLMs / PBT / the META_SPEC workstream
  are written against.
- `checker/Bytecode/InterpretChecker.v` ascribes
  `HandleInstr <: HandleInstrSpec` and instantiates the `Run` functor.
- Extraction (`Extract.v`) and outside-Rocq PBT machinery that consumes
  extracted OCaml both live under `checker/` — they rely on the
  instantiated functor, not the abstract spec.

The net effect: `manual/Bytecode/Interpret.v` (currently ~1200 LoC) is
replaced by three small files whose combined source is a fraction of
that, and the trusted core contains only the signature + the
composition layer, not 151 `handle_<OP>` definitions.

## Non-goals

- Not changing any handler semantics.
- Not proving anything new. Uniqueness / equivalence theorems are the
  subject of `META_SPEC_PLAN.md` and are orthogonal.
- Not re-proving the 151 per-handler `correct_<OP>` lemmas. They get
  repackaged into a single `correct_handle_instr` theorem via
  dispatchers, but the proof work is pointwise the existing lemmas.

## Why this matters

`manual/` is the trusted core. The big `handle_instr` dispatch is
mechanical (one arm per opcode), while the per-opcode handlers are
where the real semantic decisions live. Pushing both out of `manual/`
and exposing only the combined signature means:

1. The trusted core gets smaller.
2. Replacing `handle_instr` (e.g. with a spec-driven definition per the
   META_SPEC plan, or with a parametric-handler refactor) touches one
   file in `automatic/`, not `manual/`.
3. The code/proof separation matches the stated trust model in
   `CLAUDE.md`: specs in `manual/`, implementations in `automatic/`.

## Target file layout

```
manual/Bytecode/
  Interpret/
    HandleInstrSpec.v       -- NEW. Module Type HandleInstrSpec.
    Run.v                   -- NEW. Module Functor Make (H : HandleInstrSpec).
    Types.v                 -- NEW. step_result, bcmicro, run_result, MRet/MErr/MFuel/MVis, etc.
  Interpret.v               -- REMOVED (content moved elsewhere).

automatic/Bytecode/
  HandleInstr.v             -- NEW. All handle_<OP> + top-level handle_instr.
                               NO Module ascription here — raw impl only.

manual/Bytecode/
  InstructSpec.v            -- EDIT. Add dispatchers (f_instr, step_pre_instr,
                               P_error_instr, P_halt_instr, P_ccall_instr) and
                               a single `correct_handle_instr` theorem.

checker/Bytecode/
  InterpretChecker.v        -- NEW. Module HandleInstrCheck <: HandleInstrSpec
                               ascribing the automatic impl, then
                               Module Interp := Run.Make HandleInstrCheck.
  Main.v                    -- EDIT. Use InterpretChecker.Interp instead of raw step.
  test/                     -- UNCHANGED. PBT continues to consume the extracted .ml.
checker/
  Extract.v                 -- EDIT. Extract from the instantiated functor.
  common/                   -- UNCHANGED. code_arr, test_common, interp_extracted land here.
```

## Step-by-step plan

### Step 1 — Carve out the data types

Create `manual/Bytecode/Interpret/Types.v` containing the definitions
the spec needs but the functor does not take as parameters:

- `step_result` (`Step | Halt | Error | CCall_request`)
- `bcmicro`, `MRet`/`MErr`/`MFuel`/`MVis`
- `run_result` (`Finished | Out_of_fuel | Run_error`)
- Any purely structural helpers (`do_raise` is a candidate to stay at
  the dispatch layer — see Step 2).

These types have no dependency on per-handler behavior, so they
legitimately belong in the trusted core and are shared by both the spec
and the impl.

### Step 2 — Define the Module Type

`manual/Bytecode/Interpret/HandleInstrSpec.v`:

```coq
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Types.

Module Type HandleInstrSpec.
  Parameter handle_instr :
    instruction -> Z -> Machine.state -> step_result.
End HandleInstrSpec.
```

Keep it minimal. The Module Type is the interface `Run.v` needs and
nothing more. Additional obligations (uniqueness modulo errors,
totality, error-message characterization) belong in a sibling Module
Type in the META_SPEC plan, not here.

### Step 3 — Write the functor

`manual/Bytecode/Interpret/Run.v`:

```coq
Module Make (H : HandleInstrSpec).
  Definition step (code : array instruction) (s : state) : step_result :=
    match fetch_instr code s.(pc) with
    | None   => Error "pc out of bounds"
    | Some i => H.handle_instr i (s.(pc) + 1) s
    end.

  Fixpoint run_micro (fuel : nat) (code : array instruction) (s : state) : bcmicro := ...
  Fixpoint handle_bcmicro (fuel : nat) (t : bcmicro) (h : ...) : run_result := ...
  Definition run (fuel : nat) (code : array instruction) (s : state) (h : ...) : run_result := ...
  Definition run_pure (fuel : nat) (code : array instruction) (s : state) : run_result := ...

  (* Any other functions currently in Interpret.v that depend on step
     but are abstract over handle_instr go here. *)
End Make.
```

Everything that currently sits *below* `step` in `Interpret.v` moves
inside `Make`. Nothing inside the functor mentions a specific opcode.

### Step 4 — Move the implementation to `automatic/`

`automatic/Bytecode/HandleInstr.v`:

```coq
From OCamlInterp.Manual.Bytecode.Interpret Require Import Types.
(* No import of HandleInstrSpec here — ascription is done in checker/. *)

(* All 151 per-opcode handlers. *)
Definition handle_ACC (n : nat) (pc' : Z) (s : state) : step_result := ...
Definition handle_PUSH (pc' : Z) (s : state) : step_result := ...
...

(* The big dispatcher. *)
Definition handle_instr (i : instruction) (pc' : Z) (s : state) : step_result :=
  match i with
  | ACC n   => handle_ACC n pc' s
  | PUSH    => handle_PUSH pc' s
  ...
  end.
```

This is where the content of the current `manual/Bytecode/Interpret.v`
(excluding the small pieces moved in Steps 1-2) lands. The file is
large (~1000 LoC) but lives in `automatic/`, where size is expected.

Note: we deliberately do *not* write `Module HandleInstr <:
HandleInstrSpec` here. The automatic file is the raw implementation;
the Module Type ascription — the act of *checking* that the impl
matches the spec — is a trust-boundary operation and belongs in
`checker/`. This matches the `Module Check <: Spec` pattern used for
`DecodeChecker`, `CompileChecker`, and `LexParseChecker` in
`CLAUDE.md`. The ascription happens in Step 6.

### Step 5 — Collapse the 151 specs into `correct_handle_instr`

The current `InstructSpec.v` has 151 `correct_<OP>` theorems, each of
the shape:

```coq
Theorem correct_ACC :
  handler_correct handle_ACC f_ACC step_pre_ACC P_error_ACC P_halt_ACC P_ccall_ACC.
```

Once `handle_instr : instruction -> Z -> state -> step_result` exists
as the central impl in `automatic/Bytecode/HandleInstr.v`, the spec
side should be a single universally quantified theorem rather than 151
separate ones. Introduce dispatchers inside `InstructSpec.v`:

```coq
Definition f_instr (i : instruction) : function :=
  match i with
  | ACC _  => f_ACC
  | PUSH   => f_PUSH
  | ...
  end.

Definition step_pre_instr (i : instruction)
  : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  match i with
  | ACC _  => step_pre_ACC
  | PUSH   => step_pre_PUSH
  | ...
  end.

Definition P_error_instr (i : instruction) : string -> state -> Prop :=
  match i with ... end.

Definition P_halt_instr (i : instruction) : value -> Prop :=
  match i with ... end.

Definition P_ccall_instr (i : instruction)
  : nat -> list value -> state -> Prop :=
  match i with ... end.
```

The five dispatchers let the combined spec stay one line:

```coq
Definition correct_handle_instr : Prop :=
  forall i,
    handler_correct
      (handle_instr i) (f_instr i)
      (step_pre_instr i) (P_error_instr i)
      (P_halt_instr i) (P_ccall_instr i).

Theorem handle_instr_correct : correct_handle_instr.
Proof.
  intros i; destruct i;
    first [ exact correct_ACC
          | exact correct_PUSH
          | ... ].
Qed.
```

The point of the dispatchers: `handle_instr`'s spec *statement* is
short and universally quantified; all the per-opcode clutter moves
into the dispatch tables, which are mechanical. If the ordering of the
five `match` arms exactly matches `handle_instr`'s own match, the proof
is a single `destruct i; exact correct_<OP>` (the ordering matters only
for readability — `first [ exact correct_ACC | exact correct_PUSH | ... ]`
works regardless).

Where do the five dispatchers live? They belong next to
`correct_handle_instr`, i.e. `InstructSpec.v` itself, because they
reference every per-opcode `step_pre_<OP>` and `P_error_<OP>` which
already live in that file. No file moves; `InstructSpec.v` grows by
~250 lines of five parallel 50-arm `match`es, and shrinks by the 151
individual theorem statements once they are inlined into the big proof
(they stay as lemmas — only the export surface contracts).

Parametric handlers (e.g. `CLOSURE`, `CLOSUREREC`, `OFFSETCLOSURE*`
per `EXTRACT_SIMPLIFICATION_PLAN.md`) interact cleanly: the dispatcher
`f_instr` just routes `CLOSURE n tgt` to `f_CLOSURE` carrying `n, tgt`
as parameters, and the proof arm invokes the existing parametric
`correct_CLOSURE`.

This step is independent of the functor work: the dispatchers and
combined theorem could land before the functor rewrite or after. The
natural order is *after* Step 4 so that `handle_instr` is already the
canonical name being specified, but before Step 6 so that `checker/`
sees the collapsed surface rather than 151 names.

### Step 6 — Ascribe and instantiate in `checker/`

`checker/Bytecode/InterpretChecker.v`:

```coq
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec Run.
From OCamlInterp.Automatic.Bytecode Require Import HandleInstr.

(* Module ascription: the trust-boundary check that the automatic impl
   in automatic/Bytecode/HandleInstr.v satisfies the manual spec in
   manual/Bytecode/Interpret/HandleInstrSpec.v. This is the point the
   Rocq kernel verifies the signature match. *)
Module HandleInstrCheck <: HandleInstrSpec.
  Definition handle_instr := HandleInstr.handle_instr.
End HandleInstrCheck.

(* Instantiate the functor at the checked module. *)
Module Interp := Run.Make HandleInstrCheck.

(* Re-export names so downstream callers don't need to qualify through Interp. *)
Definition step := Interp.step.
Definition run_micro := Interp.run_micro.
Definition handle_bcmicro := Interp.handle_bcmicro.
Definition run := Interp.run.
Definition run_pure := Interp.run_pure.
```

Two things happen here — keep them in this order:

1. `Module HandleInstrCheck <: HandleInstrSpec` is the ascription.
   Rocq's kernel verifies that `HandleInstr.handle_instr` has the type
   declared in `HandleInstrSpec.handle_instr`. If the automatic impl
   ever drifts from the spec, compilation of this file fails — which
   is precisely the `checker/` guarantee.
2. `Run.Make HandleInstrCheck` instantiates the functor against the
   *checked* module, not the raw one. This means downstream code
   never holds a handle to `HandleInstr` directly; it only sees the
   signature-constrained view.

This is the single point where the abstract and concrete sides meet.
Everything downstream (`checker/Bytecode/Main.v`, `checker/Extract.v`,
PBT) consumes these re-exports and is unaware of the functor.

### Step 7 — Update extraction

`checker/Extract.v` already lives in `checker/` — the restructure
already moved it. Update its imports:

```coq
(* Before *)
From OCamlInterp.Manual.Bytecode Require Import ... Interpret ...

(* After *)
From OCamlInterp.Checker.Bytecode Require Import InterpretChecker.
(* step / run / run_micro / etc. come from InterpretChecker's re-exports. *)
```

The `Extraction "Interp_extracted.ml" ... step run run_pure ...` line
stays unchanged — it now extracts the instantiated functor outputs.

### Step 8 — Update call sites

Anywhere `manual/Bytecode/Interpret` was imported, either:

- The importer was in `manual/` and used a data type (`step_result`,
  `bcmicro`) — switch to `manual/Bytecode/Interpret/Types`.
- The importer was in `manual/` and used `step` / `run` — this is a
  layering violation that the refactor exposes. `manual/` should not
  depend on the concrete interpreter. Either (a) the call site moves
  to `checker/`, or (b) the call site becomes a functor parameter
  itself.
- The importer was in `automatic/` — switch to
  `automatic/Bytecode/HandleInstr` for the concrete functions, or
  `manual/Bytecode/Interpret/Run` + local instantiation if it needs to
  be generic.
- The importer was in `checker/` — switch to
  `checker/Bytecode/InterpretChecker`.

Expect the bulk of this step to be mechanical `From ... Require Import`
edits. The interesting cases are any `manual/` file that calls `step`
directly — those are real layering bugs and deserve review.

### Step 9 — Delete the stale file

Remove `manual/Bytecode/Interpret.v`. Confirm no `_RocqProject` /
`dune` references remain.

### Step 10 — Verify build and PBT

1. From `verified-ocaml/`, verify Rocq compilation with the `coq_makefile`
   flow (see CLAUDE.md "Verifying Rocq compilation"):
   ```bash
   make Makefile.coq.checker
   make -f Makefile.coq.checker
   ```
   No new Admitted / axioms beyond the baseline.
2. `make extract` produces the same `Interp_extracted.ml` byte-for-byte
   (the functor instantiation should extract identically to the
   current direct definition — confirm with a diff on the output).
3. All PBT suites under `checker/Bytecode/test/` pass unchanged.
4. `Print Assumptions InterpretChecker.run.` — zero axioms.
5. `Print Assumptions InstructSpec.handle_instr_correct.` — no more
   axioms than the union of the 151 original `correct_<OP>` theorems
   (i.e. the dispatcher collapse must not introduce a new admit).

## Extraction boundary check

After the move, only `checker/` and `automatic/` should import the
raw `automatic/Bytecode/HandleInstr.v`. Grep for violations:

```bash
rg 'Automatic\.Bytecode\.HandleInstr' verified-ocaml/manual/ && echo "LAYER VIOLATION"
```

Should produce no output. `manual/` may legitimately reference
`HandleInstrSpec` (it defines it), and `checker/` legitimately imports
both sides — that's the whole point of the ascription there.

A second check: the `<: HandleInstrSpec` ascription should appear in
exactly one place — `checker/Bytecode/InterpretChecker.v`.

```bash
rg '<:\s*HandleInstrSpec' verified-ocaml/ | grep -v checker/ \
  && echo "ASCRIPTION IN WRONG LAYER"
```

Should also produce no output.

## Ordering

1. Steps 1-3 (types, spec, functor) together — can be done in one PR
   since the functor doesn't compile without the spec and the spec is
   trivial without the types.
2. Step 4 (move implementation) in the same PR to keep
   `make -f Makefile.coq` green; the move is strictly cut-and-paste
   until the module ascription at the bottom.
3. Step 5 (collapse the 151 specs) is independent of the functor
   plumbing and of `checker/`. It can ride the same PR or split out —
   the only requirement is that `handle_instr` exists as a name by
   then (Step 4 guarantees that). The five dispatcher `match`es are
   mechanical; the proof of `handle_instr_correct` is a 151-arm
   `destruct` + `exact`.
4. Step 6 (instantiation) to re-wire downstream — mechanical.
5. Steps 7-9 (extraction, call sites, deletion) — can be split if
   needed; Step 8 is where hidden coupling shows up.
6. Step 10 verifies.

Prefer one big atomic PR rather than staged — the intermediate states
are broken (missing file or missing ascription). Staging only helps if
step 8 turns up surprises, in which case pausing between 6 and 7 is
the natural checkpoint.

Step 5 is the one piece that can safely ride in a follow-up PR
without leaving `make -f Makefile.coq` red — the 151 `correct_<OP>`
lemmas keep compiling even if `handle_instr_correct` has not yet been
added.

## Interactions with other plans

- **`META_SPEC_PLAN.md`**: The meta-spec declares a stronger interface
  (uniqueness mod errors) sitting on top of `HandleInstrSpec`. Doing
  this functorization first makes the meta-spec trivial to state — it
  becomes "any two implementations of `HandleInstrSpec` are `em_eq`".
  Step 5's dispatchers are the same dispatchers the meta-spec wants
  for its `HandlerSpecBundle` table, so this plan pays down part of
  that work.
- **`automatic/Bytecode/InstructVerification/PLAN.md`**: Partially
  affected. The per-handler `correct_<OP>` lemmas are preserved but get
  inlined as the 151 arms of `handle_instr_correct` in Step 5. The
  outstanding proof work from the sibling `PROGRESS.md` (8 compile
  failures, 2 Admitted, 23 missing) is *unchanged* — until those lemmas
  exist, the corresponding arms of `handle_instr_correct` are the same
  `Admitted.` they are today.
- **`EXTRACT_SIMPLIFICATION_PLAN.md`**: Mildly interacts. The
  parametric handlers proposed there (CLOSURE/CLOSUREREC,
  OFFSETCLOSURE*, INT_COMP, etc.) each become one arm in each of the
  five dispatchers. Landing that plan first reduces the arm count in
  the dispatchers; landing this plan first does not block it.

## Open questions

1. Should `handle_instr` return a `step_result` or a step_result
   polymorphic over the "continuation state" (so that CCall_request
   can carry a state typed by the functor)? Current `step_result`
   embeds `state` directly, so the simpler typing works.
2. Should `HandleInstrSpec` include a spec-level obligation like
   "`handle_instr` agrees with the per-instruction specs in
   `InstructSpec.v`"? No — keep `HandleInstrSpec` an interface type
   only. The combined obligation lives in `InstructSpec.v` as
   `correct_handle_instr` (Step 5); a Module Type that bundles
   `handle_instr` *with* its Clight-correctness proof belongs in the
   meta-spec Module Interface (see `META_SPEC_PLAN.md`), not here.

4. Should the five dispatchers (`f_instr`, `step_pre_instr`,
   `P_error_instr`, `P_halt_instr`, `P_ccall_instr`) be packaged as
   one `HandlerSpecBundle` record indexed by `instruction`, or stay as
   five parallel `match`es? A record flips the orientation
   (per-instruction bundle vs. per-field dispatcher) and is what
   `META_SPEC_PLAN.md` ultimately wants. Default to five parallel
   `match`es for this plan — the record shape is a trivial packaging
   step once the dispatchers exist, and the meta-spec plan can take
   that step when it lands.
3. Do we want `HandleInstrSpec` and `HandleInstr` to share the `Type`
   for `state` by parameterization (`Module Type HandleInstrSpec
   (M : MachineSpec) := ...`), or to concretely depend on
   `manual/Bytecode/Machine.v`? The latter is simpler and there is no
   near-term need for multiple machine models; default to concrete.
