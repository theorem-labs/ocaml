# timeout-PLAN.md — Fixing eval_cbn Timeouts

## Affected files

| File | Lines | eval_cbn calls | Structure |
|------|-------|----------------|-----------|
| DIVINT_correct.v | 418 | 11 | pop + shr + if-zero + div + retag |
| MODINT_correct.v | 519 | 18 | pop + shr + if-zero + mod + retag |
| BRANCHIF_correct.v | 880 | 85 | case split on accu, if-then-else |
| BRANCHIFNOT_correct.v | 1113 | 105 | case split on accu, if-then-else |

## Root cause

`eval_cbn` is `cbn` with an exclusion list. Each call normalizes the
**entire** goal. For these handlers:

1. `cbn` recurses into both branches of `Sifthenelse` before
   a rewrite resolves which branch is taken.
2. `cbn` eagerly unfolds `comp_eval_stmt`/`comp_eval_expr` into
   the large function body AST, getting stuck on opaque `Mem.load`
   only after expensive traversal.
3. Term size compounds — each rewrite + cbn makes subsequent calls
   slower.

Working handlers (CONST3: 4 calls, ADDINT: 28) are fast because
their bodies are linear sequences with no branching.

## Fix: manual bigstep construction

Replace `eval_stmt_to_exec` + eval_cbn chains with direct
`exec_stmt` derivation using ClightBigstep constructors.
Zero `cbn` calls — each constructor application is O(1) unification.

This is already used in SETGLOBAL_correct.v and MAKEBLOCK1_correct.v
and compiles in seconds.

### What changes per file

- Keep all `Local Lemma` semantic helpers — they compile fast.
- Keep Part 2 of each proof (abs_rel reconstruction) — no eval_cbn there.
- **Rewrite only Part 1** (exec_stmt derivation):
  delete `apply (eval_stmt_to_exec ...)` and all `eval_cbn` / `rewrite` lines,
  replace with constructor-based proof.

### Constructors needed

```coq
(* Statements *)
exec_Sseq_1 ge e le m s1 t1 le1 m1 s2 t2 le2 m2 out :
  exec_stmt ... s1 t1 le1 m1 Out_normal ->
  exec_stmt ... s2 t2 le2 m2 out ->
  exec_stmt ... (Ssequence s1 s2) (t1**t2) le2 m2 out

exec_Sset ge e le m id a v :
  eval_expr ... a v ->
  exec_stmt ... (Sset id a) E0 (PTree.set id v le) m Out_normal

exec_Sassign ge e le m a1 a2 loc ofs bf v2 v m' :
  eval_lvalue ... a1 loc ofs bf ->
  eval_expr ... a2 v2 ->
  sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
  assign_loc (genv_cenv ge) (typeof a1) m loc ofs bf v m' ->
  exec_stmt ... (Sassign a1 a2) E0 le m' Out_normal

exec_Sifthenelse ge e le m a s1 s2 v1 b t le' m' out :
  eval_expr ... a v1 ->
  bool_val v1 (typeof a) m = Some b ->
  exec_stmt ... (if b then s1 else s2) t le' m' out ->
  exec_stmt ... (Sifthenelse a s1 s2) t le' m' out

exec_Sreturn_some ge e le m a v :
  eval_expr ... a v ->
  exec_stmt ... (Sreturn (Some a)) E0 le m (Out_return (Some (v, typeof a)))

exec_Sskip ge e le m :
  exec_stmt ... Sskip E0 le m Out_normal

(* Expressions *)
eval_Etempvar ge e le m id ty v :
  le ! id = Some v -> eval_expr ... (Etempvar id ty) v

eval_Econst_int ge e le m i ty :
  eval_expr ... (Econst_int i ty) (Vint i)

eval_Ebinop ge e le m op a1 a2 ty v1 v2 v :
  eval_expr ... a1 v1 -> eval_expr ... a2 v2 ->
  sem_binary_operation (genv_cenv ge) op v1 (typeof a1) v2 (typeof a2) m = Some v ->
  eval_expr ... (Ebinop op a1 a2 ty) v

eval_Ecast ge e le m a ty v1 v :
  eval_expr ... a v1 -> sem_cast v1 (typeof a) ty m = Some v ->
  eval_expr ... (Ecast a ty) v

eval_Elvalue ge e le m a loc ofs bf v :
  eval_lvalue ... a loc ofs bf -> deref_loc (typeof a) m loc ofs bf v ->
  eval_expr ... a v

(* Lvalues *)
eval_Ederef ge e le m a ty b ofs :
  eval_expr ... a (Vptr b ofs) ->
  eval_lvalue ... (Ederef a ty) b ofs Full

eval_Efield_struct ge e le m a i ty b ofs id co att delta bf :
  eval_expr ... a (Vptr b ofs) ->
  typeof a = Tstruct id att ->
  (genv_cenv ge) ! id = Some co ->
  field_offset (genv_cenv ge) i (co_members co) = Errors.OK (delta, bf) ->
  eval_lvalue ... (Efield a i ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) bf

(* Memory access *)
deref_loc_value ty m b ofs chunk v :
  access_mode ty = By_value chunk ->
  Mem.loadv chunk m (Vptr b ofs) = Some v ->
  deref_loc ty m b ofs Full v

deref_loc_copy ty m b ofs :
  access_mode ty = By_copy ->
  deref_loc ty m b ofs Full (Vptr b ofs)

assign_loc_value ce ty m b ofs chunk v m' :
  access_mode ty = By_value chunk ->
  Mem.storev chunk m (Vptr b ofs) v = Some m' ->
  assign_loc ce ty m b ofs Full v m'
```

### Pattern: read struct field (e.g. s->accu)

```coq
(* eval_expr for: Efield (Ederef (Etempvar _s ...) (Tstruct _interp_state _)) _accu tlong *)
eapply eval_Elvalue.
{ eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
    + apply deref_loc_copy. reflexivity.
  - reflexivity.
  - exact Hco.
  - exact Haccu_offset. }
{ apply deref_loc_value with (chunk := Mint64). reflexivity.
  simpl. rewrite Mptr_Mint64.
  rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
  exact Haccu_load. }
```

### Pattern: write struct field (e.g. s->accu = v)

```coq
(* exec_Sassign for field write *)
eapply exec_Sassign.
- (* lvalue: s->accu *)
  eapply eval_Efield_struct.
  + eapply eval_Elvalue.
    * eapply eval_Ederef. eapply eval_Etempvar. exact Hle_s.
    * apply deref_loc_copy. reflexivity.
  + reflexivity.
  + exact Hco.
  + exact Haccu_offset.
- (* rvalue *) ... (* eval_expr for the RHS *)
- (* sem_cast *) exact Hcast.
- (* assign_loc *)
  apply assign_loc_value with (chunk := Mint64). reflexivity.
  simpl. rewrite Mptr_Mint64.
  rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
  exact Hstore.
```

### Pattern: if-then-else

```coq
(* exec_Sifthenelse — only the taken branch needs a proof *)
eapply exec_Sifthenelse.
- (* eval_expr for condition *)
  eapply eval_Ebinop.
  + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
  + (* eval_expr for ((0 << 1) + 1) *)
    eapply eval_Ebinop.
    * eapply eval_Ebinop.
      { eapply eval_Ecast. eapply eval_Econst_int. exact (sem_cast_int_to_long_0 m). }
      { eapply eval_Econst_int. }
      { exact (sem_shl_long_0_1 m). }
    * eapply eval_Econst_int.
    * exact (sem_add_long_int_0_1 m).
  + exact (sem_eq_long_long accu_long (Int64.repr 1) m).
- (* bool_val *) exact (bool_val_of_bool _ m).
- (* exec the taken branch *) simpl. ...
```

### Pattern: return 0

```coq
apply exec_Sreturn_some. eapply eval_Econst_int.
```

## CRITICAL: Memory safety rules

**Your machine WILL run out of memory and crash if you get this wrong.**

### Forbidden tactics

Do NOT use any of the following anywhere in these proofs:

- `compute` — expands everything, instant OOM on clight_ge
- `vm_compute` — same
- `native_compute` — same
- `eval_cbn` / `cbn` on goals containing `clight_ge` or `comp_eval_stmt` — this is the whole reason these files timeout
- `simpl` on large goals — can loop or explode on CompCert terms
- `auto` / `eauto` with high depth on goals containing Clight ASTs

### Safe tactics

- `exact`, `apply`, `eapply` — O(1) unification
- `rewrite` with named hypotheses or small lemmas — fine
- `reflexivity` on small goals — fine
- `lia` — fine (linear arithmetic, bounded)
- `congruence` — fine
- `simpl` on SMALL focused goals only (e.g. `simpl access_mode`)
- `destruct`, `inversion` — fine on small inductive types

### Rule of thumb

If a tactic normalizes or reduces terms, ask: "does the goal
contain `clight_ge`, `f_instr_*`, or `comp_eval_stmt`?" If yes,
do NOT use that tactic. Use explicit constructor applications instead.

## Build instructions

These files live in `timeout/`, NOT in the dune-managed `theories/`
directory. Other agents are working on `theories/` files in parallel
and running `dune build`. Do NOT use `dune build` for these files.

### Compile with coqc directly

**NEVER use `dune build` — other agents are using dune in parallel
and dune takes a lock. Running dune here will either block waiting
for the lock or cause the other agents' builds to fail.**

Use `coqc` directly. The `.vo` dependencies should already exist
in `_build/default/` from prior dune builds. If they don't, wait
for the other agents to finish before proceeding.

```bash
cd /workspaces/theorem-work/theorem-ocaml/verified-ocaml

# Compile a timeout file directly with coqc
coqc -Q _build/default/instruct-verification/theories InstructVerification \
     -Q _build/default/manual/theories/Utils OCamlInterp.Manual.Utils \
     -Q _build/default/manual/theories/Bytecode OCamlInterp.Manual.Bytecode \
     instruct-verification/timeout/DIVINT_correct.v
```

If the exact flags are wrong, look at a `.v.d` file or a build log
in `_build/` to find the right `-Q`/`-R` flags. Do NOT run
`dune rules` either — it can trigger a build.

### Setting a memory limit

To avoid crashing the machine, run coqc with a memory limit:
```bash
ulimit -v 8000000  # 8GB virtual memory limit
coqc [flags] instruct-verification/timeout/DIVINT_correct.v
```

If it hits the limit, the process dies instead of taking down the OS.

### Timeout detection

Set a timeout too — compilation should take under 2 minutes:
```bash
timeout 120 coqc [flags] instruct-verification/timeout/DIVINT_correct.v
```

If it takes longer, something is wrong (likely a tactic is
normalizing a large term). Stop and fix before retrying.

## Execution order

1. DIVINT — smallest, one if-else (zero-check skipped via precondition)
2. MODINT — same structure as DIVINT
3. BRANCHIF — 2 main cases (taken/not-taken) x accu shapes
4. BRANCHIFNOT — same as BRANCHIF, reversed condition

## After conversion

1. Verify with `coqc` as above — must complete in < 2 minutes
2. Move file from `timeout/` to `theories/`
3. Integration build happens later when no other agents are running
