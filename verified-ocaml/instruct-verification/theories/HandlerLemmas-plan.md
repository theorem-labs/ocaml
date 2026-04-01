# HandlerLemmas.v Axiom Elimination Plan

Ordered steps to eliminate all 10 axioms from HandlerLemmas.v.
Each step is self-contained: after completing it, `dune build instruct-verification` must pass.

**Phase 0** (structural refactoring) is a prerequisite. It does two things:
(a) converts `abs_rel_with_ard` from a nested conjunction to a Rocq Record,
so that later phases can add fields without cascading edits; and
(b) unifies `handler_correct`, `handler_correct_with_pre`, and
`handler_correct_with_pre_env` into a single most-general definition,
so that adding/changing preconditions is a one-argument change.

---

## Background: destruct/reconstruct patterns (pre-Phase-0 state)

Every handler proof has two halves:

1. **Destruct `abs_rel`** to get field hypotheses (`Hpc_load`, `Haccu_load`, `Hsp_load`, etc.).
2. **Reconstruct `abs_rel`** for the post-state by re-supplying each conjunct with updated loads.

There are two patterns depending on the theorem form:

**Pattern A (`handler_correct`):** The Step case starts with
```coq
intro Hpre. destruct Hpre as [ard Hpre].
```
which gives `Hpre : <body of abs_rel after exists>`.

**Pattern B (`handler_correct_with_pre`):** The Step case starts with
```coq
intros ard Hpre Hstep_pre.
```
where `Hpre : abs_rel_with_ard e le m s ard`.  Some proofs `unfold abs_rel_with_ard in Hpre` before destructing; others rely on Coq seeing through `let` bindings.

Both patterns then destruct `Hpre` with the same 7-conjunct shape:
```coq
destruct Hpre as (Hle_s &
  [pc_ptr [Hpc_load Hpc_rel]] &
  [accu_v [Haccu_load Haccu_repr]] &
  [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
    [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
  [env_v [Henv_load Henv_repr]] &
  Hextra_load &
  [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
  [ts_ptr [Hts_load Htrap_rel]]).
```

The reconstruction is a `split` into 7 conjuncts of the same shape.

**Key insight:** Adding new conjuncts to `abs_rel` changes both the destruct pattern and the reconstruction. Choosing WHERE to add them determines how many proof files need editing.

---

## Phase 0: Structural refactoring (Record + handler_correct unification)

**Goal:** Two changes, done together because both touch all ~50 handler files:

1. Replace the `Definition abs_rel_with_ard ... : Prop := <7-way /\>` with
   a `Record` in `Prop`. This makes adding/removing conjuncts in later
   phases a one-line record-field change instead of restructuring every
   destruct/reconstruct pattern.

2. Unify `handler_correct`, `handler_correct_with_pre`, and
   `handler_correct_with_pre_env` into a single definition. The most
   general form (with `Clight.env` in the precondition) becomes THE
   definition. Simpler derived notions are defined in terms of it.

**Files:** `InstructSpec.v`, all ~50 `_correct.v` handler proofs,
`HandlerLemmas.v` (if it destructs `abs_rel`), `BOOLNOT_correct.v`,
`ISINT_correct.v` (custom statements that can now use `handler_correct`).

### Step 0.1: Define the Record in InstructSpec.v

Replace the current `Definition abs_rel_with_ard` (lines 253-296) with:

```coq
Record abs_rel_with_ard (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) (ard : abs_rel_data) : Prop :=
  mk_abs_rel_with_ard {
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let go := ar_global_ofs ard in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in

  ar_le_s_field :
    le ! _s = Some (Vptr sb so);

  ar_pc_field :
    exists pc_ptr,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr /\
      pc_rel pc_ptr cb co s.(pc);

  ar_accu_field :
    exists accu_v,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v /\
      val_repr hm s.(accu) accu_v;

  ar_sp_field :
    exists sp_ptr sp_b sp_ofs,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
      sp_ptr = Vptr sp_b sp_ofs /\
      stack_repr hm m s.(stack) sp_b sp_ofs /\
      sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b;

  ar_env_field :
    exists env_v,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
      val_repr hm s.(Machine.env) env_v;

  ar_extra_field :
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
      Some (Vlong (Int64.repr (Z.of_nat s.(extra_args))));

  ar_global_field :
    exists gd_ptr,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
      gd_ptr = Vptr gb go /\
      global_repr hm m s.(global) gb go /\
      gb <> sb;

  ar_trapsp_field :
    exists ts_ptr,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
      trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp);
}.
```

**Important:** Rocq may not support `let ... in` inside Record field
types directly. If that fails, inline the projections:
`ar_sptr_block ard` instead of `sb`, etc. Or define a `Section` with
local variables and close it afterward.

### Step 0.2: Update `abs_rel`

`abs_rel` stays as:
```coq
Definition abs_rel (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data), abs_rel_with_ard e le m s ard.
```

This should work without change since `abs_rel_with_ard` is now a Record
type applied to its parameters (still a Prop).

### Step 0.3: Update `abs_rel_pre`

`abs_rel_pre` has the same body but with `s.(pc) + 1` instead of `s.(pc)`
in the pc field. Two options:

**(a) Parameterize the record by pc value:**
Add a `rocq_pc : Z` parameter to the record. Define:
```coq
Definition abs_rel_with_ard e le m s ard := abs_rel_fields e le m s ard s.(pc).
Definition abs_rel_pre_with_ard e le m s ard := abs_rel_fields e le m s ard (s.(pc) + 1).
```
This avoids duplication but adds a parameter everywhere.

**(b) Define a separate record for `abs_rel_pre`:**
Copy-paste with the one-field difference. More code but simpler.

**(c) Keep `abs_rel_pre` as a conjunction Definition:**
Since `abs_rel_pre` is NOT used in any handler proof file (only in
InstructSpec.v and HandlerLemmas.v), converting it is optional.

**Recommended:** Option (c) for now. Convert `abs_rel_pre` later if
needed. The handler proofs only use `abs_rel` and `abs_rel_with_ard`.

### Step 0.4: Update `abs_rel_iff_with_ard`

The current lemma:
```coq
Lemma abs_rel_iff_with_ard : forall e le m s,
  abs_rel e le m s <-> exists ard, abs_rel_with_ard e le m s ard.
Proof. intros. unfold abs_rel, abs_rel_with_ard. reflexivity. Qed.
```

After the change, `abs_rel_with_ard` is a Record (inductive), not a
Definition. `unfold abs_rel_with_ard` won't work. Replace with:

```coq
Lemma abs_rel_iff_with_ard : forall e le m s,
  abs_rel e le m s <-> exists ard, abs_rel_with_ard e le m s ard.
Proof. intros. unfold abs_rel. reflexivity. Qed.
```

This works because `abs_rel` unfolds to `exists ard, abs_rel_with_ard e le m s ard`,
which is exactly the RHS (definitional equality).

### Step 0.5: Update all destruct patterns (~50 files)

**The change is mechanical.** A conjunction `A /\ B /\ ... /\ H` is
destructed as `(H1 & H2 & ... & H8)` which desugars to nested
`[H1 [H2 [... [H7 H8] ...]]]`. A Record with 8 fields is destructed
as `[H1 H2 H3 H4 H5 H6 H7 H8]` (flat, not nested).

**Pattern A (`handler_correct` proofs):**

Old:
```coq
intro Hpre. destruct Hpre as [ard Hpre].
destruct Hpre as (Hle_s &
  [pc_ptr [Hpc_load Hpc_rel]] &
  [accu_v [Haccu_load Haccu_repr]] &
  [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
    [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]] &
  [env_v [Henv_load Henv_repr]] &
  Hextra_load &
  [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
  [ts_ptr [Hts_load Htrap_rel]]).
```

New:
```coq
intro Hpre. destruct Hpre as [ard Hpre].
destruct Hpre as [Hle_s
  [pc_ptr [Hpc_load Hpc_rel]]
  [accu_v [Haccu_load Haccu_repr]]
  [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
    [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]]
  [env_v [Henv_load Henv_repr]]
  Hextra_load
  [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]]
  [ts_ptr [Hts_load Htrap_rel]]].
```

The change: `( ... & ... & ... )` → `[ ... ... ... ]`. Each inner
pattern (the existential destructs) stays identical.

**Pattern B (`handler_correct_with_pre` proofs):**

Old:
```coq
intros ard Hpre Hstep_pre.
unfold abs_rel_with_ard in Hpre.    (* optional, some proofs have this *)
destruct Hpre as (Hle_s & ... ).
```

New:
```coq
intros ard Hpre Hstep_pre.
destruct Hpre as [Hle_s ... ].
```

The `unfold abs_rel_with_ard in Hpre` line is no longer needed (and would
fail, since `abs_rel_with_ard` is now an inductive, not a Definition).
**Delete all such unfold lines.**

**Mechanical find-replace strategy:**

1. Replace all `destruct Hpre as (Hle_s &` with `destruct Hpre as [Hle_s`
2. Replace all `&\n  [pc_ptr` (or `& [pc_ptr`) with just `[pc_ptr`
3. Similarly for each `&` between fields
4. Close with `].` instead of `).`
5. Delete all `unfold abs_rel_with_ard in Hpre.` lines

A regex replacement is feasible: change `&` between field patterns to
whitespace, and outer `( )` to `[ ]`. But due to variations in
formatting, a per-file manual pass may be safer.

### Step 0.6: Update all reconstruction patterns (~50 files)

**Old pattern:**
```coq
exists ard.
split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
{ (* le_s *) ... }
{ (* pc *) ... }
{ (* accu *) ... }
{ (* sp *) ... }
{ (* env *) ... }
{ (* extra *) ... }
{ (* global *) ... }
{ (* trap_sp *) ... }
```

**New pattern:**
```coq
exists ard.
constructor.
{ (* le_s *) ... }
{ (* pc *) ... }
{ (* accu *) ... }
{ (* sp *) ... }
{ (* env *) ... }
{ (* extra *) ... }
{ (* global *) ... }
{ (* trap_sp *) ... }
```

The change: replace `split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].`
with `constructor.`

Each brace block stays exactly the same — the subgoals are identical
because each Record field has the same type as the corresponding conjunct.

**Variations:**
- Some proofs use `repeat split.` instead of explicit nesting — replace
  with `constructor.`
- Some proofs use bullet `-` instead of braces `{ }` — no change needed
  in the subgoals, only in the split line.
- Some proofs have `unfold abs_rel.` before `exists ard.` — this still
  works since `abs_rel` is still a `Definition` that unfolds to
  `exists ard, abs_rel_with_ard ...`.

**Mechanical find-replace:**
```
split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
```
→
```
constructor.
```

### Step 0.7: Update `mk_abs_rel` call sites (10 files)

These files construct a NEW `ard'` via `mk_abs_rel` for the post-state:
- `CONSTINT_correct.v`
- `PUSHCONSTINT_correct.v`
- `ASSIGN_correct.v`
- `OFFSETINT_correct.v`
- `BRANCH_correct.v`
- `GETGLOBAL_correct.v`
- `SETGLOBAL_correct.v`
- `ATOM_correct.v`
- `MAKEBLOCK1_correct.v`
- `POP_correct.v`

These are unaffected by the `abs_rel_with_ard` Record change — they
construct `abs_rel_data` (unchanged), not `abs_rel_with_ard`. The
`mk_abs_rel` constructor is for the `abs_rel_data` record, which already
exists and is NOT being changed in Phase 0.

The reconstruction in these files says `exists ard'. constructor. ...`
instead of `exists ard. constructor. ...` — same pattern, same change.

**No special handling needed** for these files beyond the standard
Step 0.6 replacement.

### Step 0.8: Unify `handler_correct` definitions in InstructSpec.v

Currently three variants exist:

```coq
(* 1. No precondition, abs_rel existentially quantified *)
handler_correct handler f P_error P_halt P_ccall

(* 2. Precondition takes (m, s, ard) *)
handler_correct_with_pre handler f step_pre P_error P_halt P_ccall

(* 3. Precondition takes (e, m, s, ard) — most general *)
handler_correct_with_pre_env handler f step_pre P_error P_halt P_ccall
```

Replace all three with a single definition. The most general form
(`_with_pre_env`) becomes THE definition, renamed to `handler_correct`:

```coq
Definition handler_correct
    (handler : Z -> state -> step_result)
    (f : function)
    (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  forall e le m s,
    match handler s.(pc) s with
    | Step s' =>
        forall ard,
        abs_rel_with_ard e le m s ard ->
        step_pre e m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m f.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => P_error msg s
    | Halt v => P_halt v
    | CCall_request nargs args s' => P_ccall nargs args s'
    end.
```

Delete `handler_correct_with_pre` and `handler_correct_with_pre_env`.

**Convenience notation** (optional, for backward compatibility):

```coq
(* handler_correct with no precondition *)
Notation handler_correct_no_pre handler f P_error P_halt P_ccall :=
  (handler_correct handler f (fun _ _ _ _ => True) P_error P_halt P_ccall).
```

Or define it as a `Definition` if `Notation` causes issues:

```coq
Definition handler_correct_simple handler f P_error P_halt P_ccall :=
  handler_correct handler f (fun _ _ _ _ => True) P_error P_halt P_ccall.
```

### Step 0.9: Update theorem statements in handler proof files

**Three categories of change:**

**Category 1: Old `handler_correct` proofs (~35 files, e.g. ACC*, PUSH, CONST*, arithmetic)**

Old:
```coq
Theorem verify_ACC1_correct :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ACC. simpl nth_error.
  intro Hpre. destruct Hpre as [ard Hpre].
```

New:
```coq
Theorem verify_ACC1_correct :
    handler_correct (handle_ACC 1) f_instr_ACC1
      (fun _ _ _ _ => True)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s. unfold handler_correct, handle_ACC. simpl nth_error.
  intros ard Hpre _.
```

Changes:
1. Add `(fun _ _ _ _ => True)` as the `step_pre` argument.
2. Replace `intro Hpre. destruct Hpre as [ard Hpre].` with
   `intros ard Hpre _.` (the `_` eats `True`).
3. Delete `unfold handler_correct,` from the unfold (now it's the same
   definition). Or keep it — doesn't matter.

**Category 2: Old `handler_correct_with_pre` proofs (~23 files, e.g. CONSTINT, BRANCH, GETFIELD0, comparisons)**

Old:
```coq
Theorem verify_CONSTINT_correct : forall n,
    handler_correct_with_pre (handle_CONSTINT n) f_instr_CONSTINT
      (fun m s ard => ...)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  unfold handler_correct_with_pre, handle_CONSTINT. simpl.
  intros ard Hpre Hstep_pre.
```

New:
```coq
Theorem verify_CONSTINT_correct : forall n,
    handler_correct (handle_CONSTINT n) f_instr_CONSTINT
      (fun _e m s ard => ...)            (* add ignored _e parameter *)
      (fun _ _ => False) (fun _ => False) (fun _ _ _ => False).
Proof.
  unfold handler_correct, handle_CONSTINT. simpl.
  intros ard Hpre Hstep_pre.
```

Changes:
1. `handler_correct_with_pre` → `handler_correct`.
2. Add `_e` (or `_`) parameter to the `step_pre` lambda.
3. `unfold handler_correct_with_pre` → `unfold handler_correct`.

**Category 3: Old `handler_correct_with_pre_env` proofs (1 file: SETGLOBAL)**

Old:
```coq
Theorem verify_SETGLOBAL_correct : forall n,
    handler_correct_with_pre_env (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (fun e m s ard => ...)
```

New:
```coq
Theorem verify_SETGLOBAL_correct : forall n,
    handler_correct (handle_SETGLOBAL n) f_instr_SETGLOBAL
      (fun e m s ard => ...)
```

Only change: `handler_correct_with_pre_env` → `handler_correct`.
The precondition lambda already has the right signature.

**Category 4: Custom-statement proofs (BOOLNOT, ISINT)**

These used a hand-written theorem statement because the old
`handler_correct` had no precondition slot. They can now use
`handler_correct` directly:

Old (BOOLNOT):
```coq
Theorem verify_BOOLNOT_correct :
  forall e le m s,
    match handle_BOOLNOT s.(pc) s with
    | Step s' =>
        boolnot_precond s ->
        abs_rel e le m s ->
        exists le' m' out, ...
    | Error msg => True
    | Halt v => False
    | CCall_request _ _ _ => False
    end.
```

New:
```coq
Theorem verify_BOOLNOT_correct :
    handler_correct (fun _ => handle_BOOLNOT) f_instr_BOOLNOT
      (fun _e _m s _ard => boolnot_precond s)
      (fun _ _ => True) (fun _ => False) (fun _ _ _ => False).
```

Changes:
1. Replace custom match statement with `handler_correct`.
2. Precondition wraps `boolnot_precond s` in a lambda ignoring `e`, `m`, `ard`.
3. Proof opening changes from `intros e le m s.` to
   `intros e le m s. unfold handler_correct, handle_BOOLNOT.`
   then `intros ard Hpre Hstep_pre.`

**Note on precondition ordering:** BOOLNOT/ISINT currently have the
precondition BEFORE `abs_rel` in the implication chain. The unified
definition puts it AFTER (`abs_rel_with_ard -> step_pre -> ...`).
This changes which hypotheses are available when, but since Coq
tactics access hypotheses by name (not position), the proof scripts
should need minimal adjustment.

### Step 0.10: Build and verify

```bash
dune build instruct-verification
```

Expect: all files compile. No semantic change — the unified
`handler_correct` subsumes all three old variants.

### Why Phase 0 first

**Record refactor:** Later phases add fields to `abs_rel`. With the
conjunction layout, adding a field means changing the nesting of
`split; [| split; ...]` and every `( ... & ... )` destruct across
~50 files. With a Record: add one line + one `constructor` block per
handler. O(n * fields) → O(n) edits per new field.

**Handler unification:** Later phases may convert `handler_correct`
proofs to `handler_correct_with_pre` (e.g. PUSH needing `sp_ofs >= 16`).
With three separate definitions, that's a theorem-form migration.
With one definition, it's just changing the `step_pre` argument from
`(fun _ _ _ _ => True)` to a real precondition — the proof structure
is identical.

**Both refactors touch all ~50 files.** Doing them together avoids a
second full pass. The combined diff is still mechanical: record
destruct/reconstruct patterns change, `unfold handler_correct_with_pre`
→ `unfold handler_correct`, and precondition-free proofs add
`(fun _ _ _ _ => True)` + replace `intro Hpre. destruct Hpre as [ard Hpre].`
with `intros ard Hpre _.`

**Future-proofing:** The unified `handler_correct` is general enough
for all foreseeable handler categories (heap allocation, external calls,
conditional branching, exception handling). These don't need a different
theorem shape — they need better helper lemmas and tactics, which later
phases provide independently.

---

## Phase 1: Add `ar_global_ne_sptr` to the record

**Files:** `InstructSpec.v`, `HandlerLemmas.v`

### Step 1.1: Edit `abs_rel_data` in InstructSpec.v

Add the field after the existing separation fields (line 65 area):

```coq
Record abs_rel_data := mk_abs_rel {
  ar_sptr_block : block;
  ar_sptr_ofs   : ptrofs;
  ar_heap_map   : nat -> option (block * ptrofs);
  ar_code_base_block : block;
  ar_code_base_ofs   : ptrofs;
  ar_global_block : block;
  ar_global_ofs   : ptrofs;
  ar_stack_block    : block;
  ar_stack_base_ofs : ptrofs;
  ar_code_ne_sptr   : ar_code_base_block <> ar_sptr_block;
  ar_code_ne_global : ar_code_base_block <> ar_global_block;
  ar_global_ne_sptr : ar_global_block <> ar_sptr_block;    (* NEW *)
  ar_sptr_ofs_bound : Ptrofs.unsigned ar_sptr_ofs + 56 < Ptrofs.modulus;
}.
```

### Step 1.2: Fix all `mk_abs_rel` call sites

Search for `mk_abs_rel` or `{| ar_sptr_block :=` across the codebase. Each
construction must supply the new `ar_global_ne_sptr` proof. In every case,
the `abs_rel` conjunct `gb <> sb` (named `Hgb_ne_sb`) is already in scope;
pass it as the new field.

**How to find them:** `grep -rn 'mk_abs_rel\|{| ar_sptr' instruct-verification/`

If there are no explicit constructions (because proofs say `exists ard` and
reuse the same `ard` from the pre-state), then no changes are needed at
call sites -- the pre-state `ard` already satisfies the record because
its construction (somewhere upstream) supplied the field.

However: the FIRST construction of `abs_rel_data` (the initial state setup,
likely not in instruct-verification/) MUST be updated.

### Step 1.3: Replace the axiom in HandlerLemmas.v

Replace:

```coq
Axiom global_block_ne_sptr : forall (ard : abs_rel_data),
  ar_global_block ard <> ar_sptr_block ard.
```

With:

```coq
Lemma global_block_ne_sptr : forall (ard : abs_rel_data),
  ar_global_block ard <> ar_sptr_block ard.
Proof. intros. exact (ar_global_ne_sptr ard). Qed.
```

**Build and test.** No downstream proof files change because the lemma keeps
the same name and type.

---

## Phase 2: Delete the two false axioms

**Files:** `HandlerLemmas.v`, ~50 handler `_correct.v` files

### Step 2.1: Delete the axioms

Remove from HandlerLemmas.v:

```coq
Axiom sp_block_ne_sptr : forall (ard : abs_rel_data) sp_b,
  sp_b <> ar_sptr_block ard.
```

```coq
Axiom sp_block_ne_global : forall (ard : abs_rel_data) sp_b,
  sp_b <> ar_global_block ard.
```

### Step 2.2: Fix all callers of `sp_block_ne_sptr`

~50 files contain exactly one of:
```coq
pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
```

In every case, the destruct of `abs_rel` already produced `Hsp_ne_sb : sp_b <> sb`.
This is the SAME fact (possibly with arguments reversed).

**Replacement:** Delete the `pose proof` line. Then either:

(a) If `Hblock_sep` was used with the exact same orientation as `Hsp_ne_sb`,
    rename `Hsp_ne_sb` to `Hblock_sep` with:
    ```coq
    rename Hsp_ne_sb into Hblock_sep.
    ```
    This is a zero-risk change that preserves all downstream references.

(b) If `Hblock_sep` was used in a context that needs `sp_b <> sb`
    (same orientation as `Hsp_ne_sb`), no rename needed -- just replace
    `Hblock_sep` with `Hsp_ne_sb` at each use site.

**Checking orientation:** The typical use is:
```coq
intro Heq; exact (Hblock_sep (eq_sym Heq))
```
which needs `sp_b <> sb`. The `abs_rel` conjunct is `sp_b <> sb` (same).
So in most cases, a simple rename suffices.

**Mechanical approach:** Do a global find-replace:
```
pose proof (sp_block_ne_sptr ard sp_b) as Hblock_sep. fold sb in Hblock_sep.
```
->
```
rename Hsp_ne_sb into Hblock_sep.
```

### Step 2.3: Fix the sole caller of `sp_block_ne_global`

Only `PUSH_correct.v` (line 53) uses it:
```coq
pose proof (sp_block_ne_global ard sp_b) as Hsp_ne_gb_legacy.
```

This is redundant with `Hsp_ne_gb` from the destruct. Delete the line and
replace any uses of `Hsp_ne_gb_legacy` with `Hsp_ne_gb`.

**Build and test.**

---

## Phase 3: Add new `abs_rel` conjuncts

**Files:** `InstructSpec.v`, all ~50 handler proof files

After Phase 0, `abs_rel_with_ard` is a Record. Adding conjuncts means
adding fields to the Record — no changes to nesting depth of
destruct/reconstruct patterns.

We add 4 new pieces of information. Two become new Record fields (top-level),
and two go inside the existing `ar_sp_field` existential (because they
are about the stack pointer block).

### Step 3.1: Add new Record fields

Add to the `abs_rel_with_ard` Record definition in `InstructSpec.v`:

```coq
  (* NEW: stack block is writable over the full frame [0, sp_top) *)
  ar_sp_writable :
    exists sp_ptr sp_b sp_ofs,
      Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
      sp_ptr = Vptr sp_b sp_ofs /\
      Mem.range_perm m sp_b 0
        (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
        Cur Writable;

  (* NEW: struct block is writable over all fields *)
  ar_sb_writable :
    Mem.range_perm m sb (Ptrofs.unsigned so)
      (Ptrofs.unsigned so + 56) Cur Writable;
```

**Alternative (simpler):** Instead of duplicating the sp existentials in
`ar_sp_writable`, strengthen the existing `ar_sp_field` by appending
conjuncts inside its `exists`:

```coq
  ar_sp_field :
    exists sp_ptr sp_b sp_ofs,
      ... /\
      sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
      (* NEW *) Ptrofs.unsigned sp_ofs >= 8 /\
      (* NEW *) Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack))
                  < Ptrofs.modulus /\
      (* NEW *) Mem.range_perm m sp_b 0
                  (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
                  Cur Writable;
```

And add `ar_sb_writable` as a standalone new Record field. This is
better because the sp-related invariants stay grouped.

### Step 3.2: Update destruct patterns

The `ar_sp_field` destruct changes inside its inner pattern only:

Old (after Phase 0):
```coq
[sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
  [Hsp_ne_sb [Hsp_ne_gb Hcb_ne_sp]]]]]]]]
```

New:
```coq
[sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
  [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp
  [Hsp_ge8 [Hsp_rep Hsp_writable]]]]]]]]]]]
```

For proofs that don't need the new hypotheses, use a wildcard:
```coq
[sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr
  [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp _]]]]]]]]]
```

And add `Hsb_writable` (or `_`) as a new positional entry in the
top-level Record destruct:
```coq
destruct Hpre as [Hle_s ... [ts_ptr [Hts_load Htrap_rel]] Hsb_writable].
```

### Step 3.3: Update reconstruction

After Phase 0, reconstruction uses `constructor.` followed by one
brace/bullet block per field. Adding a new Record field just means
adding one more block at the end:

```coq
constructor.
{ (* ar_le_s_field *) ... }
{ (* ar_pc_field *) ... }
{ (* ar_accu_field *) ... }
{ (* ar_sp_field *) ... 4 new sub-conjuncts inside ... }
{ (* ar_env_field *) ... }
{ (* ar_extra_field *) ... }
{ (* ar_global_field *) ... }
{ (* ar_trapsp_field *) ... }
{ (* ar_sb_writable — NEW *)
  intros ofs' [Hlo Hhi]. apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore).
  apply Hsb_writable. lia. }
```

No changes to the number of splits or nesting depth — just one more block.

For each new conjunct:

**(a) `Ptrofs.unsigned sp_ofs >= 8`:**
- Handlers that DON'T change sp: the new sp_ofs is the same. Prove: `exact Hsp_ge8.`
- PUSH: new sp = old sp - 8. The pre-state has old sp >= 8.
  After push, new sp = old sp - 8 >= 0, and the old stack grew by 1.
  Must show new sp >= 8 too, which requires old sp >= 16.
  **Issue:** The current conjunct only says >= 8. For PUSH to preserve
  it, we'd need >= 16 (room for *two* pushes). This is too strong in general.
  **Resolution:** Make this a `handler_correct_with_pre` precondition for
  PUSH instead, or weaken the invariant to >= 0 and make sp_ofs_ge_8 a
  per-handler precondition. Alternatively, keep the axiom for sp_ofs_ge_8
  and only eliminate the others. See "Design Decision" below.

**(b) `Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus`:**
- Handlers that don't change sp or stack: `exact Hsp_rep.`
- PUSH: new stack = accu :: old_stack, new sp = old sp - 8.
  `Ptrofs.unsigned (old_sp - 8) + 8 * (1 + length old_stk)`
  `= (old_sp_uns - 8) + 8 + 8 * length old_stk`
  `= old_sp_uns + 8 * length old_stk`
  `< Ptrofs.modulus` by the pre-state invariant. Works.
- POP: new stack is shorter, new sp is bigger. Both directions help.

**(c) `Mem.range_perm m sp_b 0 (Ptrofs.unsigned sp_ofs) Cur Writable`:**
- After store to sb (different block): `Mem.perm_store_1` preserves perms.
  ```coq
  intros ofs' [Hlo Hhi]. apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore).
  apply Hsp_writable. lia.
  ```
- After store to sp_b: `Mem.perm_store_1` still works (same block is fine).
- PUSH: new sp = old sp - 8. New range is `[0, old_sp - 8)`, which is a
  subset of `[0, old_sp)`. So preservation is trivial.
- POP: new sp = old sp + 8*n. New range is `[0, old_sp + 8*n)`, strictly
  larger. Need to argue that the old `stack_repr` implies Readable at
  `[old_sp, old_sp + 8*n)`, but we need Writable. **Issue:** same
  Readable-vs-Writable problem at the new offsets.
  **Resolution:** Use `[0, Ptrofs.unsigned sp_ofs + 8 * length stk)` as the
  writable range instead of `[0, sp_ofs)`. This covers the full stack frame
  and doesn't shrink/grow with push/pop (the product `sp_ofs + 8*len`
  stays constant modulo push/pop). See "Design Decision" below.

**(d) `Mem.range_perm m sb so (so + 56) Cur Writable`:**
- After store to sb at offset `so + k`: `Mem.perm_store_1` preserves.
- After store to sp_b (different block): `Mem.perm_store_1` preserves.

---

### Design Decision: stack writability range

The simplest correct formulation is a FIXED range covering the entire
stack frame, not just `[0, sp_ofs)`:

```coq
Mem.range_perm m sp_b 0
  (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack))) Cur Writable
```

This range `[0, sp_top)` where `sp_top = sp_ofs + 8 * |stack|` is invariant
under push (sp decreases by 8, stack grows by 1: sp_top unchanged) and pop
(sp increases, stack shrinks: sp_top unchanged). Other handlers don't touch
sp or stack, so it's trivially preserved.

Combined with representability (`sp_top < Ptrofs.modulus`), this range is
always positive and well-defined.

**Revised sp clause:**

```coq
(exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack))
      < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable)
```

And struct writability as a separate (9th) top-level conjunct,
placed after the `trap_sp` clause:

```coq
  ... /\
  (exists ts_ptr, ...) /\
  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
    Cur Writable
```

This changes the top-level split from 7-way to 8-way. Every reconstruction
site needs one more bullet. But it is cleaner than burying struct
writability inside the sp clause where it doesn't logically belong.

---

## Phase 4: Prove the memory axioms

**Files:** `HandlerLemmas.v` only

After Phase 3, the new conjuncts are available.

### Step 4.1: Prove `store_succeeds_from_load`

Replace the axiom with:

```coq
Lemma store_succeeds_from_load : forall m sb so b ofs v_old v_new,
  Mem.range_perm m b ofs (ofs + 8) Cur Writable ->
  (8 | ofs) ->
  exists m', Mem.store Mint64 m b ofs v_new = Some m'.
Proof.
  intros.
  apply Mem.valid_access_store.
  split; assumption.
Qed.
```

**But wait:** the current axiom signature doesn't take `range_perm`; it
takes `Mem.load ... = Some v_old`. Changing the signature would break
all 40+ callers. Two approaches:

**(a) Keep the old signature, change the proof to use the new conjuncts.**
This doesn't work -- the old signature doesn't have access to
`range_perm`; it only has `Mem.load`.

**(b) Change the signature AND fix all callers.**
The new signature should be:

```coq
Lemma store_succeeds_at_field : forall m sb so field_ofs v_new,
  Mem.range_perm m sb so (so + 56) Cur Writable ->
  0 <= field_ofs -> field_ofs + 8 <= 56 ->
  (8 | so + field_ofs) ->
  exists m', Mem.store Mint64 m sb (so + field_ofs) v_new = Some m'.
Proof.
  intros m sb so field_ofs v_new Hwr Hlo Hhi Halign.
  apply Mem.valid_access_store.
  split.
  - intros ofs' [H1 H2].
    change (size_chunk Mint64) with 8%Z in H2.
    apply Hwr. lia.
  - change (align_chunk Mint64) with 8%Z. exact Halign.
Qed.
```

This is clean but changes every call site. A transition path is to
keep the old name as a wrapper:

```coq
(* Wrapper: caller provides the range_perm separately *)
Lemma store_succeeds_from_load : forall m b ofs v_old v_new,
  Mem.load Mint64 m b ofs = Some v_old ->
  Mem.range_perm m b ofs (ofs + 8) Cur Writable ->
  exists m', Mem.store Mint64 m b ofs v_new = Some m'.
Proof.
  intros m b ofs v_old v_new _ Hwr.
  apply Mem.valid_access_store. split.
  - intros ofs' [H1 H2].
    change (size_chunk Mint64) with 8%Z in H2.
    apply Hwr. lia.
  - apply Mem.load_valid_access in H.  (* get alignment from the load *)
    (* Actually: we don't use H at all. We need alignment. *)
Abort.
```

**Cleanest approach:** Add a NEW lemma with the right signature and update
callers incrementally. Keep the old axiom temporarily, then delete it when
all callers are migrated. Or: add an extra `range_perm` argument to the
axiom and update all callers in one pass.

**Recommended signature (minimally invasive):**

```coq
Lemma store_succeeds_from_load : forall m b ofs v_old v_new,
  Mem.load Mint64 m b ofs = Some v_old ->
  Mem.range_perm m b ofs (ofs + 8) Cur Writable ->
  exists m', Mem.store Mint64 m b ofs v_new = Some m'.
Proof.
  intros m b ofs v_old v_new Hload Hwr.
  apply Mem.valid_access_store. split.
  - intros ofs' [H1 H2]. apply Hwr. change (size_chunk Mint64) with 8%Z in H2. lia.
  - exact (proj2 (Mem.load_valid_access _ _ _ _ _ Hload)).
Qed.
```

This uses the old load to get the alignment, and the new `range_perm` for
the Writable permission. Callers add one extra argument.

At each call site, the current pattern is:
```coq
destruct (store_succeeds_from_load m sb (uso + K) old_v new_v Hload) as [m' Hstore].
```
Change to:
```coq
destruct (store_succeeds_from_load m sb (uso + K) old_v new_v Hload
            (sub_range_perm ... Hsb_writable ...)) as [m' Hstore].
```
where `sub_range_perm` extracts the `[uso+K, uso+K+8)` sub-range from
`Hsb_writable : range_perm m sb uso (uso+56) Cur Writable`.

**Helper lemma** (add to HandlerLemmas.v):
```coq
Lemma range_perm_subrange : forall m b lo hi lo' hi' k p,
  Mem.range_perm m b lo hi k p ->
  lo <= lo' -> hi' <= hi ->
  Mem.range_perm m b lo' hi' k p.
Proof. unfold Mem.range_perm. intros. apply H. lia. Qed.
```

### Step 4.2: Prove `store_to_other_block`

Similar approach. New signature adds `range_perm`:

```coq
Lemma store_to_other_block : forall m m' sb ofs_store v sp_b new_ofs cv,
  Mem.store Mint64 m sb ofs_store v = Some m' ->
  sb <> sp_b ->
  Mem.range_perm m sp_b new_ofs (new_ofs + 8) Cur Writable ->
  (8 | new_ofs) ->
  exists m'', Mem.store Mint64 m' sp_b new_ofs cv = Some m''.
Proof.
  intros m m' sb ofs_store v sp_b new_ofs cv Hstore Hne Hwr Halign.
  apply Mem.valid_access_store. split.
  - intros ofs' [H1 H2].
    apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore).
    apply Hwr. change (size_chunk Mint64) with 8%Z in H2. lia.
  - change (align_chunk Mint64) with 8%Z. exact Halign.
Qed.
```

Callers pass `Hsp_writable` (sub-ranged) and an alignment fact.

### Step 4.3: Prove `store_succeeds_stack`

Similar to `store_to_other_block` but same block:

```coq
Lemma store_succeeds_stack : forall m sp_b sp_ofs v,
  Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some v ->
  forall v_new ofs,
  ofs + 8 <= Ptrofs.unsigned sp_ofs ->
  ofs >= 0 ->
  Mem.range_perm m sp_b ofs (ofs + 8) Cur Writable ->
  exists m', Mem.store Mint64 m sp_b ofs v_new = Some m'.
```

Or eliminate it entirely by having callers use `Mem.valid_access_store`
directly with the range_perm from `abs_rel`. Check how many callers exist
and whether a dedicated lemma is worth it.

### Step 4.4: Prove `sp_ofs_ge_8` and `sp_ofs_stack_representable`

These become trivial extractions from the new conjuncts:

```coq
Lemma sp_ofs_ge_8 : forall hm m stk sp_b sp_ofs,
  stack_repr hm m stk sp_b sp_ofs ->
  Ptrofs.unsigned sp_ofs >= 8 ->  (* NEW argument *)
  Ptrofs.unsigned sp_ofs >= 8.
Proof. intros. assumption. Qed.
```

But this changes the signature. Better: leave the old signature and add
`Ptrofs.unsigned sp_ofs >= 8` as an argument. Or: callers already have
`Hsp_ge8` from the destruct, so they can use it directly instead of
calling the lemma. **Simplest:** delete the lemma and replace all callers
with `Hsp_ge8`.

Same for `sp_ofs_stack_representable`: delete and replace callers with
`Hsp_rep`.

---

## Phase 5: Prove the stack repr lemmas

**Files:** `HandlerLemmas.v` only

### Step 5.1: Prove `stack_repr_store_same_block_lower`

Now that `sp_ofs_stack_representable` is available as a hypothesis at
each call site, we need it as an argument. New signature:

```coq
Lemma stack_repr_store_same_block_lower :
  forall hm m m' stk sp_b sp_ofs ofs v,
  stack_repr hm m stk sp_b sp_ofs ->
  Mem.store Mint64 m sp_b ofs v = Some m' ->
  ofs + 8 <= Ptrofs.unsigned sp_ofs ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
  stack_repr hm m' stk sp_b sp_ofs.
```

**Proof by induction on `stk` (not on `stack_repr` -- avoids dependent match issues):**

```
Base: stk = []. stack_repr is sr_nil. constructor.

Step: stk = v :: vs. Invert stack_repr to get:
  Hload : Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some cv
  Hval  : val_repr hm v cv
  Htail : stack_repr hm m vs sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))

  (a) Head: Show Mem.load Mint64 m' sp_b (Ptrofs.unsigned sp_ofs) = Some cv.
      By Mem.load_store_other: store at ofs, load at Ptrofs.unsigned sp_ofs.
      Need: ofs + 8 <= Ptrofs.unsigned sp_ofs (given).
      Result: load preserved.

  (b) Tail: Apply IH with sp_ofs' = Ptrofs.add sp_ofs (Ptrofs.repr 8).
      Need: ofs + 8 <= Ptrofs.unsigned sp_ofs'
        = Ptrofs.unsigned sp_ofs + 8    (by representability)
      This holds since ofs + 8 <= Ptrofs.unsigned sp_ofs
                     <= Ptrofs.unsigned sp_ofs + 8.

      Need: Ptrofs.unsigned sp_ofs' + 8 * length vs < Ptrofs.modulus.
        = (Ptrofs.unsigned sp_ofs + 8) + 8 * length vs
        = Ptrofs.unsigned sp_ofs + 8 * (1 + length vs)
        = Ptrofs.unsigned sp_ofs + 8 * length (v :: vs)
        < Ptrofs.modulus (given).

  Key ptrofs lemma needed:
    Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8))
      = Ptrofs.unsigned sp_ofs + 8
    when Ptrofs.unsigned sp_ofs + 8 < Ptrofs.modulus.
  This follows from ptrofs_add_unsigned (already in HandlerLemmas.v).

  Apply sr_cons with the preserved load, same val_repr, and IH result.
```

### Step 5.2: Prove `stack_repr_cons_after_store`

Uses `load_after_store_same`, `val_repr_load_result`, and
`stack_repr_store_same_block_lower`.

```coq
Lemma stack_repr_cons_after_store :
  forall hm m m' stk sp_b sp_ofs v cv,
  stack_repr hm m stk sp_b sp_ofs ->
  val_repr hm v cv ->
  Mem.store Mint64 m sp_b
    (Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 8))) cv = Some m' ->
  Ptrofs.unsigned sp_ofs >= 8 ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus ->
  stack_repr hm m' (v :: stk) sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
Proof.
  intros.
  set (new_sp := Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
  assert (Ptrofs.unsigned new_sp = Ptrofs.unsigned sp_ofs - 8) by ...
  apply sr_cons with cv.
  - (* head load *)
    rewrite <- H_unsigned.
    apply Mem.load_store_same in H1.
    rewrite (val_repr_load_result _ _ _ H0) in H1.
    exact H1.
  - (* val_repr *) exact H0.
  - (* tail: stack_repr at new_sp + 8 = sp_ofs *)
    assert (Ptrofs.add new_sp (Ptrofs.repr 8) = sp_ofs) by ...
    rewrite H_add.
    apply (stack_repr_store_same_block_lower _ m m' stk sp_b sp_ofs
             (Ptrofs.unsigned new_sp) cv H H1).
    + rewrite H_unsigned. lia.
    + exact H3.
Qed.
```

The ptrofs cancellation `Ptrofs.add (Ptrofs.sub x 8) 8 = x` needs a
dedicated lemma (straightforward from `Ptrofs.unsigned sp_ofs >= 8`).

---

## Phase 6: Update all handler proofs for new conjuncts

**Files:** all ~50 `_correct.v` files

### For handlers that DON'T change sp or stack (ACC, CONST, arithmetic, etc.):

**Destruct:** Use the wildcard pattern from Phase 3 Step 3.3.

**Reconstruct:** The sp clause needs the 3 new sub-conjuncts. Since sp_ofs
and stack are unchanged, and memory only changed on sb (different block):

```coq
- (* sp_ofs >= 8 *) exact Hsp_ge8.
- (* representability *) simpl. exact Hsp_rep.  (* or rewrite length *)
- (* stack writable *)
  intros ofs' [Hlo Hhi]. apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore).
  apply Hsp_writable. lia.
```

And struct writability (new 8th top-level conjunct):
```coq
- (* struct writable *)
  intros ofs' [Hlo Hhi]. apply (Mem.perm_store_1 _ _ _ _ _ _ Hstore).
  apply Hsb_writable. lia.
```

### For PUSH:

- sp_ofs >= 8: requires pre-state sp_ofs >= 16. Add as `handler_correct_with_pre` precondition if not already. Or use the weakened invariant sp_ofs >= 0 and make sp_ofs >= 8 a per-handler pre.
- representability: arithmetic (see Phase 5).
- stack writable: sub-range of old writable (new range is smaller).
- struct writable: preserved by store to different block.

### For POP:

- sp_ofs >= 8: new sp = old_sp + 8*n >= 8 + 8*n >= 8. Trivial.
- representability: new product <= old product. Trivial.
- stack writable: new range `[0, old_sp + 8n)` is larger. Since the
  full frame `[0, sp_top)` is writable and sp_top is invariant, this works
  with the fixed-range formulation.
- struct writable: preserved by store to different block.

---

## Summary of file-change counts

| Phase | Files changed | Risk |
|-------|--------------|------|
| 0 (record refactor) | ~52 | Medium (mechanical but many files) |
| 1 (record field) | 2 | Low |
| 2 (delete false axioms) | ~51 | Low (mechanical) |
| 3 (new conjuncts) | ~52 | Low (with records, just add field + block) |
| 4 (prove memory axioms) | 1 | Low |
| 5 (prove stack lemmas) | 1 | Low |
| 6 (handler updates) | ~50 | Medium (case-by-case) |

Total: ~52 unique files, most touched in phases 0+2+3+6.

**Recommended approach:** Phase 0 first (standalone). Then do phases
1-6, combining phases 2, 3, and 6 in a single pass per file to
minimize re-reading. For each `_correct.v` file:
1. Delete `pose proof (sp_block_ne_sptr ...)` line, rename hypothesis
2. Add new field bindings or wildcards in the Record destruct
3. Add new `constructor` subgoal blocks for new Record fields
4. Build and fix

Phases 1, 4, 5 are independent of the per-file work and can be done
between the per-file passes.
