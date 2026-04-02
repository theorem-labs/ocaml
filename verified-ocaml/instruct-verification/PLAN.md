# Handler Verification Plan

## Current State

- **151 handlers** in `instruct_handlers.v`
- **62 proved** (Qed, no Admitted): ACC0-7, ADDINT, ANDINT, ASRINT, ASSIGN,
  ATOM, BOOLNOT, BRANCH, BRANCHIF, BRANCHIFNOT, CHECK_SIGNALS, CONST0-3,
  CONSTINT, DIVINT, EQ, GEINT, GETFIELD0, GETGLOBAL, GTINT, ISINT, LEINT,
  LSLINT, LSRINT, LTINT, MAKEBLOCK1, MODINT, MULINT, NEGINT, NEQ, OFFSETINT,
  ORINT, POP, PUSH, PUSHACC1-7, PUSHCONST0-3, PUSHCONSTINT, SETGLOBAL,
  STOP, SUBINT, UGEINT, ULTINT, VECTLENGTH, XORINT
- **2 Admitted** proofs: MAKEBLOCK1_correct.v, SETGLOBAL_correct.v
- **22 axioms** to eliminate: 5 in HandlerLemmas.v, 11 in MAKEBLOCK1_correct.v,
  6 in VECTLENGTH_correct.v
- **89 missing** handler proofs
- **1 Admitted** in StepToBigstep.v (unused reference, not a real axiom)

**Goal: 151 handler proofs, 0 axioms, 0 Admitted.**

---

## Part I: Axiom Elimination (22 axioms + 2 Admitted -> 0)

### Axiom Inventory

| # | Axiom | File | Strategy |
|---|-------|------|----------|
| **HandlerLemmas.v** |||
| 1 | `store_succeeds_from_load` | HL:178 | Prove from `Hsb_writable` + load alignment |
| 2 | `store_to_other_block` | HL:132 | Prove from `Hsp_writable` + `Mem.perm_store_1` |
| 3 | `store_succeeds_stack` | HL:218 | Delete (unused) |
| 4 | `sp_ofs_ge_8` | HL:226 | Delete (redundant with `Hsp_ge8` in abs_rel) |
| 5 | `sp_ofs_stack_representable` | HL:232 | Delete (redundant with `Hsp_rep` in abs_rel) |
| **MAKEBLOCK1_correct.v** |||
| 6 | `heap_alloc_find_funct` | MB1:188 | Move to step_pre via `ext_func_findable` |
| 7 | `heap_alloc_external_call` | MB1:211 | Move to step_pre via `heap_alloc_spec` |
| 8 | `heap_alloc_preserves_stack` | MB1:238 | Subsumed by `heap_alloc_spec` load preservation |
| 9 | `heap_alloc_preserves_global` | MB1:252 | Same |
| 10 | `heap_alloc_block_ne_sp` | MB1:266 | Subsumed by `heap_alloc_spec` freshness |
| 11 | `heap_alloc_block_ne_gb` | MB1:279 | Same |
| 12 | `heap_alloc_block_ne_cb` | MB1:292 | Same |
| 13 | `store_new_block_preserves_stack` | MB1:305 | Delete (use existing `stack_repr_store_other_block`) |
| 14 | `store_new_block_preserves_global` | MB1:313 | Delete (use existing `global_repr_store_other_block`) |
| 15 | `heap_alloc_preserves_code` | MB1:324 | Subsumed by `heap_alloc_spec` load preservation |
| 16 | `eval_expr_heap_alloc` | MB1:342 | Provable from Genv + step_pre `e ! _heap_alloc = None` |
| **Admitted proofs** |||
| A1 | MAKEBLOCK1 Admitted | MB1:1230 | Close via writable preservation through `heap_alloc_spec` |
| A2 | SETGLOBAL Admitted | SG:749 | Close via writable preservation through `caml_modify_spec` |
| **VECTLENGTH_correct.v** |||
| 17 | `heap_header_load` | VL:58 | Eliminated by `heap_block_well_formed` in abs_rel |
| 18 | `heap_tag_not_double_array` | VL:71 | Same |
| 19 | `heap_block_ofs_ge_8` | VL:76 | Same |
| 20 | `heap_block_ne_sptr` | VL:82 | Same |
| 21 | `heap_tag_range` | VL:87 | Same |
| 22 | `heap_header_shr_size` | VL:93 | Provable from heap_header_load + Int64 arithmetic |

### Axiom Elimination Details

#### Group 1: HandlerLemmas Store Axioms (unblocks all 62 handler files)

**Axiom 1: `store_succeeds_from_load`** -- Used by 60 handler files on
struct block `sb`. Replace with `store_succeeds_sb`:

```coq
Lemma store_succeeds_sb : forall m sb so ofs v,
  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable ->
  Mem.load Mint64 m sb (Ptrofs.unsigned so + ofs) = Some v ->
  0 <= ofs -> ofs + 8 <= 56 ->
  forall v_new, exists m', Mem.store Mint64 m sb (Ptrofs.unsigned so + ofs) v_new = Some m'.
Proof.
  intros. apply Mem.valid_access_store.
  pose proof (Mem.load_valid_access _ _ _ _ _ H0) as [Hrp Halign].
  split. - intros ofs' Hofs'. apply H. lia. - exact Halign.
Qed.
```

Uses load for alignment, `Hsb_writable` for Writable. No new abs_rel fields.

**Axiom 2: `store_to_other_block`** -- Used by 13 PUSH/PUSHACC handlers.
After storing to `sb`, need to store to `sp_b`. Prove from `Hsp_writable`
+ `Mem.perm_store_1`:

```coq
Lemma store_to_sp_after_sb_store :
  forall m m' sb ofs_sb v sp_b sp_ofs stk new_ofs cv,
  Mem.store Mint64 m sb ofs_sb v = Some m' ->
  Mem.range_perm m sp_b 0
    (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk)) Cur Writable ->
  0 <= new_ofs -> new_ofs + 8 <= Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) ->
  Mem.load Mint64 m sp_b new_ofs = Some cv ->  (* for alignment *)
  forall cv_new, exists m'', Mem.store Mint64 m' sp_b new_ofs cv_new = Some m''.
```

**Axiom 3: `store_succeeds_stack`** -- 0 references. Delete.

**Axiom 4: `sp_ofs_ge_8`** -- Redundant with `Hsp_ge8` from abs_rel. Delete.
At PUSH handler call sites on the post-state stack, make `sp_ofs >= 16` a
step_pre for PUSH-family handlers ("stack has room"). For non-PUSH handlers,
post sp >= pre sp >= 8 trivially.

**Axiom 5: `sp_ofs_stack_representable`** -- Redundant with `Hsp_rep`. Delete.
For post-state: PUSH has `new_sp + 8*(len+1) = old_sp + 8*len = Hsp_rep`.

#### Group 2: MAKEBLOCK1 Heap Allocation Axioms

**Approach: Move to step_pre via shared `heap_alloc_spec`.**

Axioms 6-12, 15-16 become postconditions bundled in `heap_alloc_spec`
(see External Call Modeling below). Axioms 13-14 are trivially provable
(exact instances of existing `stack_repr_store_other_block` /
`global_repr_store_other_block`). Delete and use existing lemmas.

**Admitted A1** (sp_writable/sb_writable through heap_alloc): Close using
the permission preservation clause in `heap_alloc_spec`. Chain:
`Mem.perm_store_1` through stores + `Hext_perm_preserve` through external call.

#### Group 3: VECTLENGTH Heap Introspection Axioms

**Approach: Add `heap_block_well_formed` to abs_rel_with_ard.**

This single invariant eliminates axioms 17-22. See New Invariants below.

#### Group 4: SETGLOBAL Admitted

**Admitted A2** (sp_writable/sb_writable through caml_modify): Close
using permission preservation in `caml_modify_spec`. Same chain pattern.

### Axiom Elimination Steps

| Step | Action | Axioms remaining | Admitted remaining |
|------|--------|-----------------|-------------------|
| 1 | Delete axioms 3-5 (unused/redundant), prove axioms 1-2 | 17 | 2 |
| 2 | Create ExternalCallSpecs.v (definitions only) | 17 | 2 |
| 3 | Refactor MAKEBLOCK1: delete 13-14, move 6-12,15-16 to step_pre, close A1 | 6 | 0 |
| 4 | Refactor SETGLOBAL: use caml_modify_spec, close A2 | 6 | 0 |
| 5 | Add heap_block_well_formed to abs_rel, eliminate 17-22 | 0 | 0 |

---

## Part II: External Call Modeling

Three external functions appear across handlers:

| Function | Handlers | Count |
|----------|----------|-------|
| `heap_alloc` | MAKEBLOCK1/2/3, MAKEBLOCK(loop), MAKEFLOATBLOCK, CLOSURE, CLOSUREREC, GRAB | ~8 |
| `caml_modify` | SETGLOBAL, SETFIELD(param), SETVECTITEM, SETFLOATFIELD, SETBYTESCHAR | ~5 |

Define shared specs in `ExternalCallSpecs.v`:

### heap_alloc_spec

```coq
Definition heap_alloc_spec
  (ge : genv) (m : mem) (sb : block) (so : ptrofs)
  (sp_b : block) (sp_ofs : ptrofs) (stk : list Values.val)
  (gb cb : block) (tag_z sz_z : Z) : Prop :=
  0 <= tag_z <= 255 -> 0 <= sz_z ->
  exists m_alloc new_b new_ofs,
    external_call heap_alloc_ef ge [...] m E0 (Vptr new_b new_ofs) m_alloc /\
    (* Freshness *)
    new_b <> sb /\ new_b <> sp_b /\ new_b <> gb /\ new_b <> cb /\
    (* Load preservation on existing blocks *)
    (forall b ofs chunk v,
       Mem.load chunk m b ofs = Some v -> b <> new_b ->
       Mem.load chunk m_alloc b ofs = Some v) /\
    (* Permission preservation on existing blocks *)
    (forall b ofs k p,
       Mem.valid_block m b -> Mem.perm m b ofs k p ->
       Mem.perm m_alloc b ofs k p) /\
    (* New block storable at field offsets *)
    (forall field_ofs cv, 0 <= field_ofs -> field_ofs < sz_z * 8 ->
       (8 | new_ofs + field_ofs) ->
       exists m_store, Mem.store Mint64 m_alloc new_b
         (Ptrofs.unsigned new_ofs + field_ofs) cv = Some m_store) /\
    (* Stores to new block preserve loads on existing blocks *)
    (forall m_store new_v field_ofs,
       Mem.store Mint64 m_alloc new_b
         (Ptrofs.unsigned new_ofs + field_ofs) new_v = Some m_store ->
       forall b ofs chunk v, b <> new_b ->
         Mem.load chunk m_alloc b ofs = Some v ->
         Mem.load chunk m_store b ofs = Some v).
```

Replaces MAKEBLOCK1 axioms 7-15.

### caml_modify_spec

```coq
Definition caml_modify_spec
  (ge : genv) (m : mem) (ptr_b : block) (ptr_ofs : ptrofs)
  (new_val : Values.val) (sb : block) (so : ptrofs)
  (sp_b : block) (gb cb : block) : Prop :=
  exists m_cm,
    external_call caml_modify_ef ge [Vptr ptr_b ptr_ofs; new_val]
      m E0 Vundef m_cm /\
    Mem.load Mint64 m_cm ptr_b (Ptrofs.unsigned ptr_ofs) = Some new_val /\
    (forall b ofs chunk v,
       Mem.load chunk m b ofs = Some v ->
       (b <> ptr_b \/ ofs <> Ptrofs.unsigned ptr_ofs) ->
       Mem.load chunk m_cm b ofs = Some v) /\
    (forall b ofs k p,
       Mem.valid_block m b -> Mem.perm m b ofs k p ->
       Mem.perm m_cm b ofs k p).
```

### ext_func_findable

```coq
Definition ext_func_findable (ge : genv) (e : env)
  (id : ident) (ef : external_function) : Prop :=
  exists b,
    Genv.find_symbol ge id = Some b /\
    Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (External ef ...) /\
    e ! id = None.
```

### step_pre Usage

| Handler family | step_pre includes |
|---------------|-------------------|
| Simple (ACC, CONST, PUSH, ADDINT, ...) | `True` |
| PUSH family | `sp_ofs >= 16` (stack room) |
| MAKEBLOCK1/2/3 | `heap_alloc_spec` + `ext_func_findable _heap_alloc` |
| CLOSURE, CLOSUREREC, GRAB | same + closure layout |
| SETGLOBAL | `caml_modify_spec` + `ext_func_findable _caml_modify` |
| SETFIELD(param), SETVECTITEM | `caml_modify_spec` + `ext_func_findable _caml_modify` |
| ENVACC, GETFIELD (via heap) | heap field loadable (from `heap_block_well_formed`) |
| APPLY, APPTERM, RETURN | `closure_code_loadable` |
| PUSHTRAP, POPTRAP, RAISE | `trap_frame_well_formed` |

---

## Part III: New Invariants

### 3A. heap_block_well_formed (in abs_rel_with_ard)

**Needed by**: ~40 handlers that dereference heap pointers (GETFIELD,
SETFIELD, ENVACC, VECTLENGTH, GETVECTITEM, SETVECTITEM, OFFSETREF,
GETMETHOD, GETPUBMET, GETDYNMET, GETSTRINGCHAR, GETBYTESCHAR, ...).

```coq
(forall addr b ofs,
   hm addr = Some (b, ofs) ->
   b <> sb /\ b <> sp_b /\ b <> gb /\ b <> cb /\
   Ptrofs.unsigned ofs >= 8 /\
   (forall tag fields,
      heap_lookup hp addr = Some (tag, fields) ->
      (0 <= Z.of_nat tag <= 255) /\ Z.of_nat tag <> 254 /\
      exists hdr_word,
        Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) /\
        Int64.shru hdr_word (Int64.repr 10) =
          Int64.repr (Z.of_nat (length fields)) /\
        (forall i v, nth_error fields i = Some v ->
           exists cv, Mem.load Mint64 m b
             (Ptrofs.unsigned ofs + Z.of_nat i * 8) = Some cv /\
           val_repr hm cv v)))
```

Eliminates VECTLENGTH axioms 17-22. Also provides field-loadability
needed by GETFIELD, ENVACC, etc. without per-handler preconditions.

**Maintenance**: Non-heap-modifying handlers preserve it trivially via
`Mem.load_store_other` (different blocks). Heap-modifying handlers
(MAKEBLOCK, SETFIELD, CLOSURE) must re-establish for modified/new blocks.

### 3B. closure_code_loadable (in step_pre)

**Needed by**: ~25 handlers (OFFSETCLOSURE, APPLY, APPTERM, RETURN,
RESTART, GRAB, CLOSURE, CLOSUREREC and their PUSH variants).

```coq
Definition closure_code_loadable
  (hm : heap_map) (m : mem) (v : Machine.value) (cb : block) : Prop :=
  forall addr arity code_ofs env_vals,
    v = Val_closure addr arity code_ofs env_vals ->
    exists b ptr_ofs,
      hm addr = Some (b, ptr_ofs) /\
      exists code_ptr,
        Mem.load Mint64 m b (Ptrofs.unsigned ptr_ofs) = Some (Vptr cb code_ptr) /\
        Ptrofs.unsigned code_ptr = code_ofs * 4.
```

Goes in step_pre, not abs_rel (not all values are closures).
APPLY/APPTERM: assert on `Machine.accu s`.
OFFSETCLOSURE: assert on `Machine.env s`.

### 3C. trap_frame_well_formed (in abs_rel_with_ard)

**Needed by**: 5 handlers (PUSHTRAP, POPTRAP, RAISE, RERAISE, RAISE_NOTRACE).

```coq
Definition trap_frame_well_formed
  (m : mem) (sp_b : block) (trap_sp_val : Values.val) : Prop :=
  forall trap_ofs,
    trap_sp_val = Vptr sp_b trap_ofs ->
    (exists v, Mem.load Mint64 m sp_b (Ptrofs.unsigned trap_ofs) = Some v) /\
    (exists v, Mem.load Mint64 m sp_b (Ptrofs.unsigned trap_ofs + 8) = Some v) /\
    (exists v, Mem.load Mint64 m sp_b (Ptrofs.unsigned trap_ofs + 16) = Some v) /\
    (exists v, Mem.load Mint64 m sp_b (Ptrofs.unsigned trap_ofs + 24) = Some v).
```

PUSHTRAP establishes it; POPTRAP and RAISE consume it.

### 3D. code_buffer_load_at (reusable lemma, not new invariant)

**Needed by**: ~40 parameterized handlers that read from code buffer.

```coq
Lemma code_buffer_load_at : forall m cb code pc n,
  code_repr m cb code ->
  (pc + n < length code)%nat ->
  exists v, Mem.load Mint32 m cb (4 * Z.of_nat (pc + n)) = Some v.
```

Already implicit in BRANCHIF/CONSTINT proofs. Extract to HandlerLemmas.v.

---

## Part IV: Writable Preservation

Every handler must prove sp_writable and sb_writable in the postcondition.

### Store-only handlers (trivial)

Chain `Mem.perm_store_1` through each store:
```coq
intros ofs' Hofs'.
eapply Mem.perm_store_1. exact Hstore2.
eapply Mem.perm_store_1. exact Hstore1.
apply Hsp_writable. exact Hofs'.
```

### External-call handlers

`heap_alloc_spec` and `caml_modify_spec` include permission preservation:
```coq
(forall b ofs k p,
   Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m_post b ofs k p)
```

Chain through external call + stores:
```coq
intros ofs' Hofs'.
eapply Mem.perm_store_1. exact Hstore_final.     (* store after ext call *)
eapply Hext_perm_preserve.                        (* ext call *)
- eapply Mem.perm_valid_block.
  eapply Mem.perm_store_1. exact Hstore_before.
  apply Hsp_writable. lia.
- eapply Mem.perm_store_1. exact Hstore_before.   (* store before ext call *)
  apply Hsp_writable. exact Hofs'.
```

### Per-family summary

| Family | Memory chain | Writable proof |
|--------|-------------|----------------|
| Simple (ACC, CONST, ADDINT) | m -> m1 (sb store) | 1x perm_store_1 |
| PUSH (PUSHACC, PUSHCONST) | m -> m1 (sb) -> m2 (sp) | 2x perm_store_1 |
| MAKEBLOCK1/2/3 | m -> m1 (sb) -> m_alloc (ext) -> m2..n (stores) | perm_store_1 + ext_perm + Nx perm_store_1 |
| SETGLOBAL | m -> m1 (sb) -> m_cm (ext) -> m2 (sb) | same pattern |
| SETFIELD0-3 | m -> m1 (sp pop) -> m2 (heap) -> m3 (sb) | 3x perm_store_1 |
| SETFIELD(param) | m -> m1 (sp) -> m_cm (ext) -> m2 (sb) | perm_store_1 + ext_perm + perm_store_1 |

---

## Part V: Missing Handler Table (89 handlers)

### Category Key

| Symbol | Category |
|--------|----------|
| **S** | Simple: linear body, struct field reads/writes only |
| **P** | Pop: pops stack |
| **U** | Push: pushes to stack |
| **B** | Branch: has `Sifthenelse` |
| **X** | External: calls heap_alloc, caml_modify, etc. |
| **C** | Complex: loops, closures, exception handling |
| **N** | No-op: C body is just `return 0` or `return 3` |

### Difficulty Key

| Level | Description |
|-------|-------------|
| 1 | Trivial: no-op or near-identical to existing proof |
| 2 | Easy: direct template copy with parameter changes |
| 3 | Medium: new structure but uses existing lemma patterns |
| 4 | Hard: new lemmas, external calls, or branching logic |
| 5 | Very hard: loops, closure layout, exception frames, heap mutation |

### Group 1: No-ops / Stubs (6 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| EVENT | N | 1 | CHECK_SIGNALS | C: `return 0`. Identity on state. |
| BREAK | N | 1 | CHECK_SIGNALS | C: `return 0`. Same. |
| PERFORM | N | 1 | CHECK_SIGNALS | Stub. No Rocq handler. |
| RESUME | N | 1 | CHECK_SIGNALS | Stub. Same. |
| RESUMETERM | S | 2 | BRANCH | C: `pc += 1; return 0`. |
| REPERFORMTERM | S | 2 | BRANCH | Same. |

### Group 2: ENVACC family (6 handlers)

C body: read `s->env`, dereference `((long*)env)[n]`, store to `s->accu`.
Needs heap-field-loadable precondition (from `heap_block_well_formed`).

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| ENVACC1 | S | 2 | ACC0 | Env deref instead of stack. |
| ENVACC2 | S | 2 | ENVACC1 | Offset 2. |
| ENVACC3 | S | 2 | ENVACC1 | Offset 3. |
| ENVACC4 | S | 2 | ENVACC1 | Offset 4. |
| ENVACC | S | 3 | ENVACC1+CONSTINT | Reads n from code buffer. |
| PUSHENVACC | U | 3 | PUSHACC1+ENVACC1 | Push + code-buffer read. |

### Group 3: PUSHENVACC family (4 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| PUSHENVACC1 | U | 3 | PUSHACC1+ENVACC1 | Push + env deref. |
| PUSHENVACC2 | U | 3 | PUSHENVACC1 | |
| PUSHENVACC3 | U | 3 | PUSHENVACC1 | |
| PUSHENVACC4 | U | 3 | PUSHENVACC1 | |

### Group 4: GETFIELD1-3 + parameterized GETFIELD (4 handlers)

Identical to GETFIELD0. Needs `heap_block_well_formed`.

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| GETFIELD1 | S | 2 | GETFIELD0 | Offset 1. |
| GETFIELD2 | S | 2 | GETFIELD0 | Offset 2. |
| GETFIELD3 | S | 2 | GETFIELD0 | Offset 3. |
| GETFIELD | S | 3 | GETFIELD0+CONSTINT | Code-buffer read + heap deref. |

### Group 5: SETFIELD0-3 + parameterized SETFIELD (5 handlers)

Pop stack top, write to `((long*)accu)[n]`, set accu to `val_unit`.
Fixed-offset variants inline the store. Parameterized SETFIELD calls `caml_modify`.

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| SETFIELD0 | P | 3 | ADDINT+GETFIELD0 | Pop + heap store + unit. |
| SETFIELD1 | P | 3 | SETFIELD0 | Offset 1. |
| SETFIELD2 | P | 3 | SETFIELD0 | Offset 2. |
| SETFIELD3 | P | 3 | SETFIELD0 | Offset 3. |
| SETFIELD | PX | 4 | SETGLOBAL+SETFIELD0 | Calls `caml_modify`. |

### Group 6: OFFSETCLOSURE family (8 handlers)

Reads `s->env`, computes pointer arithmetic, stores to `s->accu`.

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| OFFSETCLOSURE0 | S | 2 | ACC0 | `accu = env`. Trivial. |
| OFFSETCLOSURE2 | S | 3 | OFFSETCLOSURE0 | `accu = env + 24`. Ptr arith. |
| OFFSETCLOSUREM2 | S | 3 | OFFSETCLOSURE2 | `accu = env - 24`. |
| OFFSETCLOSURE | S | 3 | OFFSETCLOSURE2+CONSTINT | Code-buffer read. |
| PUSHOFFSETCLOSURE0 | U | 3 | PUSHACC1+OFFSETCLOSURE0 | Push + env copy. |
| PUSHOFFSETCLOSURE2 | U | 3 | PUSHOFFSETCLOSURE0 | Push + env + 24. |
| PUSHOFFSETCLOSUREM2 | U | 3 | PUSHOFFSETCLOSURE0 | Push + env - 24. |
| PUSHOFFSETCLOSURE | U | 4 | PUSHOFFSETCLOSURE0+CONSTINT | Code-buffer read. |

### Group 7: ATOM0 + PUSHATOM variants (3 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| ATOM0 | S | 2 | ATOM | Simpler (no code buffer read). Same abstraction mismatch: use `handle_ATOM_fixed`. |
| PUSHATOM0 | U | 3 | PUSHCONST0+ATOM0 | Push + atom. |
| PUSHATOM | U | 3 | PUSHATOM0+ATOM | Code-buffer read. |

### Group 8: Global access variants (3 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| GETGLOBALFIELD | S | 3 | GETGLOBAL+GETFIELD0 | Two code-buffer reads. |
| PUSHGETGLOBAL | U | 3 | PUSHCONSTINT+GETGLOBAL | Push + global access. |
| PUSHGETGLOBALFIELD | U | 4 | PUSHGETGLOBAL+GETGLOBALFIELD | Push + two reads + global + field. |

### Group 9: B-comparison branch family (8 handlers)

All identical C skeleton: read operand + offset from code buffer, compare
with `accu >> 1`, conditionally update pc. Once BEQ is proved, rest are clones.

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| BEQ | B | 3 | BRANCHIF | `==` comparison. |
| BNEQ | B | 3 | BEQ | `!=`. |
| BLTINT | B | 3 | BEQ | `<`. |
| BLEINT | B | 3 | BEQ | `<=`. |
| BGTINT | B | 3 | BEQ | `>`. |
| BGEINT | B | 3 | BEQ | `>=`. |
| BULTINT | B | 4 | BEQ | Unsigned `<`. |
| BUGEINT | B | 4 | BEQ | Unsigned `>=`. |

### Group 10: ACC (parameterized) (1 handler)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| ACC | S | 3 | ACC0+CONSTINT | Code-buffer read + stack access at computed offset. |

### Group 11: C_CALL family (6 handlers)

C body: advance pc, return 3 (CCall_request). Very simple C bodies.

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| C_CALL1 | S | 2 | BRANCH | Returns 3 not 0. P_ccall predicate. |
| C_CALL2 | S | 2 | C_CALL1 | |
| C_CALL3 | S | 2 | C_CALL1 | |
| C_CALL4 | S | 2 | C_CALL1 | |
| C_CALL5 | S | 2 | C_CALL1 | |
| C_CALLN | S | 3 | C_CALL1+CONSTINT | Two code-buffer reads. |

### Group 12: Heap mutation (4 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| OFFSETREF | PX | 4 | SETFIELD0+OFFSETINT | Heap read + modify + write. |
| GETSTRINGCHAR | P | 4 | GETVECTITEM | Pop index + heap deref. |
| GETBYTESCHAR | P | 4 | GETSTRINGCHAR | Identical C body. |
| GETVECTITEM | P | 4 | GETFIELD0+ADDINT | Pop index + computed heap offset. |

### Group 13: External heap mutation (4 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| SETVECTITEM | PX | 5 | SETFIELD+GETVECTITEM | `caml_modify` call. |
| SETBYTESCHAR | PX | 5 | SETVECTITEM | Heap byte write. |
| GETFLOATFIELD | S | 3 | GETFIELD | Float variant. |
| SETFLOATFIELD | PX | 5 | SETFIELD | Float variant, `caml_modify`. |

### Group 14: MAKEBLOCK2/3 + parameterized (3 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| MAKEBLOCK2 | X | 4 | MAKEBLOCK1 | 2 field stores. |
| MAKEBLOCK3 | X | 4 | MAKEBLOCK1 | 3 field stores. |
| MAKEBLOCK | CX | 5 | MAKEBLOCK1 | Loop over fields. `Sloop` in C. |

### Group 15: MAKEFLOATBLOCK (1 handler)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| MAKEFLOATBLOCK | CX | 5 | MAKEBLOCK | Heap alloc + loop. Float tag. |

### Group 16: Function call machinery (9 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| PUSH_RETADDR | U | 4 | PUSHTRAP | Push 3 values. Code-buffer read. |
| APPLY | S | 3 | BRANCH+CONSTINT | Closure deref + jump. |
| APPLY1 | C | 4 | PUSH_RETADDR+APPLY | Push frame + jump. |
| APPLY2 | C | 4 | APPLY1 | 2 args. |
| APPLY3 | C | 5 | APPLY1 | 3 args. |
| APPTERM | C | 5 | APPTERM1 | Loop-like stack copy. |
| APPTERM1 | C | 4 | APPLY1 | Stack pop + rewrite. |
| APPTERM2 | C | 5 | APPTERM1 | 2 args. |
| APPTERM3 | C | 5 | APPTERM1 | 3 args. |

### Group 17: Control flow + closures (5 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| RETURN | CB | 4 | BRANCHIF+POP | Branch on extra_args. Closure deref. |
| RESTART | C | 5 | RETURN | Loop over closure fields. |
| GRAB | CB | 5 | RETURN | Branch + possible closure alloc. |
| CLOSURE | CX | 5 | MAKEBLOCK1+PUSH_RETADDR | Heap alloc for closure. |
| CLOSUREREC | CX | 5 | CLOSURE | Multiple allocs + loop. Most complex. |

### Group 18: Exception handling (5 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| PUSHTRAP | U | 4 | PUSH_RETADDR | Push 4 values + update trap_sp. |
| POPTRAP | P | 4 | POP | Pop 4 + restore trap_sp. |
| RAISE | C | 5 | POPTRAP | Restore from trap frame. |
| RERAISE | C | 5 | RAISE | Identical C body. |
| RAISE_NOTRACE | C | 5 | RAISE | Identical C body. |

### Group 19: OO dispatch + SWITCH (4 handlers)

| Handler | Cat | Diff | Template | Notes |
|---------|-----|------|----------|-------|
| SWITCH | C | 5 | BRANCHIF | Computed goto. Most complex branching. |
| GETMETHOD | C | 5 | GETFIELD0 | Double heap deref. |
| GETPUBMET | C | 5 | GETMETHOD | Code-buffer + push + scan loop. |
| GETDYNMET | C | 5 | GETPUBMET | Tag from accu. |

---

## Part VI: New Lemmas & Infrastructure

### New Lemmas in HandlerLemmas.v

| # | Lemma | Needed by |
|---|-------|-----------|
| 1 | `sem_add_sp_n` (generalized) | PUSH_RETADDR, PUSHTRAP, POPTRAP, RETURN |
| 2 | `sem_sub_sp_n` (generalized) | PUSH_RETADDR, PUSHTRAP |
| 3 | `stack_repr_popn` | SETFIELD0-3, POPTRAP, RETURN |
| 4 | `stack_repr_push_multiple` | PUSH_RETADDR (3), PUSHTRAP (4) |
| 5 | `sem_cmp_long_long` family | BEQ..BUGEINT |
| 6 | `sem_shr_long_1` (untag) | BEQ..BUGEINT |
| 7 | `sem_cast_int_to_long` | BEQ..BUGEINT |
| 8 | `heap_field_store_lemma` | SETFIELD0-3, OFFSETREF |
| 9 | `closure_offset_ptr_arith` | OFFSETCLOSURE family |
| 10 | `code_buffer_load_at` | All parameterized handlers (~40) |
| 11 | `global_repr_nth` | GETGLOBAL, GETGLOBALFIELD, PUSHGETGLOBAL |
| 12 | `store_succeeds_sb` | All 60+ handlers (replaces axiom 1) |
| 13 | `store_to_sp_after_sb_store` | 13 PUSH handlers (replaces axiom 2) |

### New Infrastructure Files

| File | Purpose | Needed by |
|------|---------|-----------|
| `ExternalCallSpecs.v` | Shared heap_alloc_spec, caml_modify_spec, ext_func_findable | All external-call handlers |
| `BranchLemmas.v` | Code-buffer two-read, comparison semantics, branch pc update | BEQ..BUGEINT (8 handlers) |
| `ClosureLemmas.v` | Closure repr, code pointer extraction, env offset arithmetic | APPLY, APPTERM, OFFSETCLOSURE, GRAB, CLOSURE, CLOSUREREC (~25 handlers) |
| `ExceptionLemmas.v` | Trap frame layout, trap_sp manipulation | PUSHTRAP, POPTRAP, RAISE, RERAISE, RAISE_NOTRACE (5 handlers) |

---

## Part VII: Execution Order

### Step 1: Axiom Quick Wins
- Delete axioms 3-5 (unused/redundant)
- Prove axioms 1-2 as lemmas
- Update all 62 handler files to use new lemmas
- **Result**: HandlerLemmas.v has 0 axioms

### Step 2: Create ExternalCallSpecs.v
- Define heap_alloc_spec, caml_modify_spec, ext_func_findable
- Definitions only, no proofs, no build breakage

### Step 3: Refactor MAKEBLOCK1
- Delete axioms 13-14 (trivially provable)
- Refactor step_pre to use heap_alloc_spec
- Delete remaining 9 local axioms
- Close 2 Admitted via writable preservation
- **Result**: MAKEBLOCK1 has 0 axioms, 0 Admitted

### Step 4: Refactor SETGLOBAL
- Refactor step_pre to use caml_modify_spec
- Close 2 Admitted via writable preservation
- **Result**: SETGLOBAL has 0 axioms, 0 Admitted

### Step 5: Add heap_block_well_formed to abs_rel
- Add invariant with field loadability
- Update all 62 handler proofs (mechanical: loads preserved through stores)
- Refactor VECTLENGTH (eliminates axioms 17-22)
- **Result**: 0 axioms, 0 Admitted across all existing files

### Step 6: Missing Handler Waves

**Prerequisite infrastructure per wave:**

| Wave | Infra needed | Handlers | Count |
|------|-------------|----------|-------|
| 1 | (none) | EVENT, BREAK, PERFORM, RESUME, RESUMETERM, REPERFORMTERM | 6 |
| 2 | HW, HA, EF | GETFIELD1-3, C_CALL1-5, ATOM0, SETFIELD0-3, OFFSETCLOSURE0, MAKEBLOCK2/3 | 17 |
| 3 | HW, CL, CB | ENVACC1-4, PUSHENVACC1-4, BEQ..BUGEINT, OFFSETCLOSURE2/M2, PUSHATOM0/PUSHATOM, PUSHGETGLOBAL, PUSHOFFSETCLOSURE0/2, ACC(param), C_CALLN | 27 |
| 4 | TF, CL, CB, WP | GETFIELD(param), OFFSETCLOSURE(param), PUSHOFFSETCLOSURE(param), ENVACC(param), PUSHENVACC(param), OFFSETREF, GETSTRINGCHAR, GETBYTESCHAR, GETVECTITEM, GETFLOATFIELD, GETGLOBALFIELD, PUSH_RETADDR, PUSHGETGLOBALFIELD, PUSHTRAP, POPTRAP, RETURN, APPLY | 18 |
| 5 | CM, EF, all | SETFIELD(param), SETFLOATFIELD, SETVECTITEM, SETBYTESCHAR, APPLY1-3, APPTERM1-3, RAISE/RERAISE/RAISE_NOTRACE | 14 |
| 6 | all | APPTERM, RESTART, GRAB, CLOSURE, CLOSUREREC, MAKEBLOCK(loop), MAKEFLOATBLOCK, SWITCH, GETMETHOD/GETPUBMET/GETDYNMET | 11 |

**Invariant key**: HW = heap_block_well_formed, HA = heap_alloc_spec,
CM = caml_modify_spec, CL = closure_code_loadable, TF = trap_frame_well_formed,
CB = code_buffer_load_at, EF = ext_func_findable, WP = writable preservation pattern.

### Critical Path

```
Step 1-4          Step 5              Step 6
axiom elim  ->  heap_block_wf  ->  Wave 1 (no deps)
                + ExternalCall     Wave 2 (HW, HA)
                  Specs.v          Wave 3 (HW, CL, CB)
                                   Wave 4 (TF, CL, full)
                                   Wave 5 (CM, full)
                                   Wave 6 (everything)
```

---

## Part VIII: Agent Parallelization

### Wave 1 (6 agents)
- Agent A: EVENT, BREAK, PERFORM, RESUME
- Agent B: RESUMETERM, REPERFORMTERM

### Wave 2 (6 agents)
- Agent A: GETFIELD1, GETFIELD2, GETFIELD3
- Agent B: C_CALL1, C_CALL2, C_CALL3, C_CALL4, C_CALL5
- Agent C: ATOM0, OFFSETCLOSURE0
- Agent D: SETFIELD0 (prototype)
- Agent E: SETFIELD1, SETFIELD2, SETFIELD3
- Agent F: MAKEBLOCK2, MAKEBLOCK3

### Wave 3 (6 agents)
- Agent A: ENVACC1, ENVACC2, ENVACC3, ENVACC4
- Agent B: PUSHENVACC1, PUSHENVACC2, PUSHENVACC3, PUSHENVACC4
- Agent C: BEQ (prototype), BNEQ, BLTINT, BLEINT
- Agent D: BGTINT, BGEINT, BULTINT, BUGEINT
- Agent E: OFFSETCLOSURE2, OFFSETCLOSUREM2, PUSHOFFSETCLOSURE0, PUSHOFFSETCLOSURE2
- Agent F: PUSHATOM0, PUSHATOM, PUSHGETGLOBAL, ACC(param), C_CALLN

### Wave 4 (6 agents)
- Agent A: GETFIELD(param), GETFLOATFIELD, GETGLOBALFIELD
- Agent B: OFFSETREF, PUSHGETGLOBALFIELD
- Agent C: PUSH_RETADDR, PUSHTRAP
- Agent D: POPTRAP, RETURN
- Agent E: APPLY, APPLY1
- Agent F: Parameterized: OFFSETCLOSURE, PUSHOFFSETCLOSURE, ENVACC, PUSHENVACC, PUSHOFFSETCLOSUREM2

### Wave 5 (4 agents)
- Agent A: APPLY2, APPLY3
- Agent B: APPTERM1, APPTERM2, APPTERM3
- Agent C: RAISE, RERAISE, RAISE_NOTRACE
- Agent D: SETFIELD(param), SETVECTITEM, SETFLOATFIELD, SETBYTESCHAR

### Wave 6 (4 agents)
- Agent A: APPTERM, RESTART
- Agent B: GRAB, CLOSURE
- Agent C: CLOSUREREC, MAKEBLOCK(loop), MAKEFLOATBLOCK
- Agent D: SWITCH, GETMETHOD, GETPUBMET, GETDYNMET

---

## Part IX: Risk Areas

1. **Heap model gap**: `abs_rel` lacks heap invariant until Step 5. All
   heap-derefing handlers blocked on `heap_block_well_formed`.

2. **Atom abstraction mismatch**: Rocq `handle_ATOM` uses `heap_alloc`
   returning `Val_ptr`; C stores `Vlong(tag << 10)`. Must use
   `handle_ATOM_fixed` returning `Val_block t []`.

3. **External function specs**: `heap_alloc_spec` and `caml_modify_spec`
   must be correct for all user handlers. Test thoroughly on MAKEBLOCK1
   and SETGLOBAL before scaling.

4. **Closure representation**: ~25 handlers depend on `closure_code_loadable`.
   Must match OCaml's actual closure layout (code ptr at field 0, env at 1+).

5. **Exception frame layout**: PUSHTRAP pushes 4 values; RAISE reads them.
   The `trap_frame_well_formed` invariant must match exactly.

6. **SWITCH handler**: Computed goto via array indexing. Most complex branching.

7. **Memory safety**: Never use `compute`/`vm_compute`/`cbn` on large terms.
   Use `coqc` directly for problematic files (not `dune build`). See
   `timeout/timeout-PLAN.md` for safe tactic list.

---

## Counts

| After Step | Axioms | Admitted | Handlers proved |
|-----------|--------|----------|-----------------|
| Current | 22 | 2 | 62 |
| Step 1 | 17 | 2 | 62 |
| Step 2 | 17 | 2 | 62 |
| Step 3 | 6 | 0 | 62 |
| Step 4 | 6 | 0 | 62 |
| Step 5 | 0 | 0 | 62 |
| Wave 1 | 0 | 0 | 68 |
| Wave 2 | 0 | 0 | 85 |
| Wave 3 | 0 | 0 | 112 |
| Wave 4 | 0 | 0 | 130 |
| Wave 5 | 0 | 0 | 144 |
| Wave 6 | 0 | 0 | **151** |
