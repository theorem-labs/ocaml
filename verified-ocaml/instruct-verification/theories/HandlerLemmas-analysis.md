# HandlerLemmas.v Axiom Audit

## Summary

HandlerLemmas.v contains **10 axioms**. Of these:

- **2 are logically FALSE** as stated (universally quantified over a free block variable)
- **1 is unprovable** from `abs_rel_data` but could be if a record field is added
- **5 are unprovable** from CompCert's memory model without writability/representability invariants
- **2 are provable** from CompCert once the representability dependency is resolved

All unprovable axioms can be eliminated by strengthening `abs_rel_data` and `abs_rel`.

---

## Per-axiom analysis

### 1. `sp_block_ne_sptr` (line 96) -- FALSE

```coq
Axiom sp_block_ne_sptr : forall (ard : abs_rel_data) sp_b,
  sp_b <> ar_sptr_block ard.
```

**Verdict: FALSE.** Instantiate `sp_b := ar_sptr_block ard` to derive `False`.

**Why it hasn't blown up:** Every call site obtains `sp_b` from `abs_rel`, which
carries the conjunct `sp_b <> sb`. The axiom is only ever applied to that
specific `sp_b`, so the proof would go through if each call site used the
conjunct directly.

**Fix:** Delete the axiom. At each call site, replace
`pose proof (sp_block_ne_sptr ard sp_b)` with the existing hypothesis
(typically `Hsp_ne_sb` from destructing `abs_rel`). This is a mechanical
search-and-replace; every call site already has `Hsp_ne_sb` in context.

---

### 2. `global_block_ne_sptr` (line 101) -- UNPROVABLE (missing record field)

```coq
Axiom global_block_ne_sptr : forall (ard : abs_rel_data),
  ar_global_block ard <> ar_sptr_block ard.
```

**Verdict: Not provable from current `abs_rel_data`.** The record has
`ar_code_ne_sptr` and `ar_code_ne_global` but NOT `ar_global_block <> ar_sptr_block`.
The fact IS available as a conjunct in `abs_rel` (`gb <> sb`) but not as a
record field, so it can't be proved for an arbitrary `ard`.

**Fix:** Add a record field to `abs_rel_data`:

```coq
ar_global_ne_sptr : ar_global_block <> ar_sptr_block;
```

Then prove:

```coq
Lemma global_block_ne_sptr : forall ard,
  ar_global_block ard <> ar_sptr_block ard.
Proof. intros. exact (ar_global_ne_sptr ard). Qed.
```

Constructors of `abs_rel_data` must supply the new field.
In `abs_rel`, the conjunct `gb <> sb` already holds, so the witness
construction just threads it through.

---

### 3. `sp_block_ne_global` (line 106) -- FALSE

```coq
Axiom sp_block_ne_global : forall (ard : abs_rel_data) sp_b,
  sp_b <> ar_global_block ard.
```

**Verdict: FALSE.** Same issue as `sp_block_ne_sptr`. Instantiate
`sp_b := ar_global_block ard`.

**Fix:** Same as #1 -- delete and use the `abs_rel` conjunct `sp_b <> gb`
(typically `Hsp_ne_gb`) at each call site.

---

### 4. `store_to_other_block` (line 140) -- UNPROVABLE (missing writability)

```coq
Axiom store_to_other_block : forall m m' sb ofs_store v sp_b new_ofs cv,
  Mem.store Mint64 m sb ofs_store v = Some m' ->
  sb <> sp_b ->
  new_ofs >= 0 ->
  exists m'', Mem.store Mint64 m' sp_b new_ofs cv = Some m''.
```

**Verdict: Not provable.** `Mem.store` requires `valid_access ... Writable`.
From the successful store to `sb` we know `sb` is Writable.
`Mem.store_valid_access_1` preserves valid_access for `sp_b` across the store,
but we need `valid_access m Mint64 sp_b new_ofs Writable` in the *original*
memory, which is not given.

**How it's used:** Always with `sp_b` as the stack block and `new_ofs` as a
stack offset (specifically `Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 8))`).

**Fix:** Add a stack writability invariant to `abs_rel` (see Recommended
Changes below). Then prove from `Mem.valid_access_store` +
`Mem.store_valid_access_1`.

---

### 5. `store_succeeds_from_load` (line 186) -- UNPROVABLE (Readable != Writable)

```coq
Axiom store_succeeds_from_load : forall m b ofs v_old v_new,
  Mem.load Mint64 m b ofs = Some v_old ->
  exists m', Mem.store Mint64 m b ofs v_new = Some m'.
```

**Verdict: Not provable.** `Mem.load_valid_access` gives `valid_access ...
Readable`. `Mem.valid_access_store` needs `Writable`. CompCert's `perm_order`
has `Writable -> Readable` but NOT `Readable -> Writable`, so there is no
`valid_access_implies` path from Readable to Writable.

**How it's used:** Always with `b = sb` (the struct block) at field offsets
(0, 8, 16, 24, 32, 40, 48).

**Fix:** Add struct block writability to `abs_rel` (see below). Then prove from
`Mem.valid_access_store` directly.

---

### 6. `stack_repr_store_same_block_lower` (line 238) -- PROVABLE (with representability)

```coq
Axiom stack_repr_store_same_block_lower : forall hm m m' stk sp_b sp_ofs ofs v,
  stack_repr hm m stk sp_b sp_ofs ->
  Mem.store Mint64 m sp_b ofs v = Some m' ->
  ofs + 8 <= Ptrofs.unsigned sp_ofs ->
  stack_repr hm m' stk sp_b sp_ofs.
```

**Verdict: Provable by induction on `stack_repr`, IF stack offsets don't wrap.**

Proof sketch:
- **Base (`sr_nil`):** `sr_nil` holds in any memory. Trivial.
- **Step (`sr_cons`):** Head load at `Ptrofs.unsigned sp_ofs` is preserved by
  `Mem.load_store_other` because `ofs + 8 <= Ptrofs.unsigned sp_ofs` (left
  disjunct). For the IH, need
  `ofs + 8 <= Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8))`, i.e.,
  `ofs + 8 <= Ptrofs.unsigned sp_ofs + 8`. This holds IF `Ptrofs.add sp_ofs
  (Ptrofs.repr 8)` doesn't wrap modulo `2^64`.

The wrapping argument requires knowing that all stack slot offsets stay within
`[0, Ptrofs.modulus)`. This is exactly `sp_ofs_stack_representable` (#10).

**Dependency chain:** `stack_repr_store_same_block_lower` <-
`sp_ofs_stack_representable` (currently axiomatic).

**Fix:** Once representability is available (from the strengthened `abs_rel`),
prove by induction. Alternatively, strengthen the `stack_repr` inductive with a
representability side-condition so the proof is self-contained.

---

### 7. `stack_repr_cons_after_store` (line 251) -- PROVABLE (given #6)

```coq
Axiom stack_repr_cons_after_store : forall hm m m' stk sp_b sp_ofs v cv,
  stack_repr hm m stk sp_b sp_ofs ->
  val_repr hm v cv ->
  Mem.store Mint64 m sp_b
    (Ptrofs.unsigned (Ptrofs.sub sp_ofs (Ptrofs.repr 8))) cv = Some m' ->
  Ptrofs.unsigned sp_ofs >= 8 ->
  stack_repr hm m' (v :: stk) sp_b (Ptrofs.sub sp_ofs (Ptrofs.repr 8)).
```

**Verdict: Provable from `load_after_store_same`, `val_repr_load_result`,
`stack_repr_store_same_block_lower`, and ptrofs arithmetic.**

Proof sketch: Apply `sr_cons`:
1. **Head load:** `Mem.load_store_same` gives
   `load ... (Ptrofs.unsigned new_sp) = Some (Val.load_result Mint64 cv)`.
   `val_repr_load_result` shows `Val.load_result Mint64 cv = cv`.
2. **val_repr:** Given.
3. **Tail:** Need `stack_repr hm m' stk sp_b (Ptrofs.add new_sp (Ptrofs.repr 8))`.
   Show `Ptrofs.add (Ptrofs.sub sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8) = sp_ofs`
   (ptrofs cancel, valid since `Ptrofs.unsigned sp_ofs >= 8`).
   Then use `stack_repr_store_same_block_lower` with
   `Ptrofs.unsigned new_sp + 8 = Ptrofs.unsigned sp_ofs`.

---

### 8. `store_succeeds_stack` (line 260) -- UNPROVABLE (missing writability)

```coq
Axiom store_succeeds_stack : forall m sp_b sp_ofs v,
  Mem.load Mint64 m sp_b (Ptrofs.unsigned sp_ofs) = Some v ->
  forall v_new ofs,
  ofs + 8 <= Ptrofs.unsigned sp_ofs ->
  ofs >= 0 ->
  exists m', Mem.store Mint64 m sp_b ofs v_new = Some m'.
```

**Verdict: Not provable.** Same Readable-vs-Writable gap as #5. The load at
`sp_ofs` gives Readable at `sp_ofs`, but we need Writable at `ofs` (a
*different* offset on the same block). `valid_access` is per-offset, so
Readable at one offset says nothing about writability at another.

**Fix:** Stack writability invariant in `abs_rel` (see below).

---

### 9. `sp_ofs_ge_8` (line 268) -- UNPROVABLE (not derivable from `stack_repr`)

```coq
Axiom sp_ofs_ge_8 : forall hm m stk sp_b sp_ofs,
  stack_repr hm m stk sp_b sp_ofs ->
  Ptrofs.unsigned sp_ofs >= 8.
```

**Verdict: Not provable.** `sr_nil` holds for ANY `sp_ofs`, including
`Ptrofs.zero`. An empty stack does not force `sp_ofs >= 8`.

**How it's used:** In PUSH-family handlers, to show there's room for one push
(the new sp is `sp_ofs - 8`, which must be non-negative).

**Fix:** Add `Ptrofs.unsigned sp_ofs >= 8` as a conjunct in `abs_rel`'s sp
clause, or add it to `stack_repr` as a side-condition (changing the inductive).
The `abs_rel` conjunct is less invasive.

---

### 10. `sp_ofs_stack_representable` (line 274) -- UNPROVABLE (not derivable from `stack_repr`)

```coq
Axiom sp_ofs_stack_representable : forall hm m stk sp_b sp_ofs,
  stack_repr hm m stk sp_b sp_ofs ->
  Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length stk) < Ptrofs.modulus.
```

**Verdict: Not provable.** Same issue -- `stack_repr` does not carry
representability. On a 64-bit system with `Ptrofs.modulus = 2^64`, this is
easily satisfied in practice, but `sr_cons` does not enforce it.

**Fix:** Add as a conjunct in `abs_rel` (see below).

---

## Recommended changes to `abs_rel_data` and `abs_rel`

### Change 1: Add `ar_global_ne_sptr` to the record

```coq
Record abs_rel_data := mk_abs_rel {
  ...
  ar_global_ne_sptr : ar_global_block <> ar_sptr_block;  (* NEW *)
  ...
}.
```

**Eliminates:** `global_block_ne_sptr` (axiom #2).

**Impact:** Every construction of `abs_rel_data` must supply this proof.
The `abs_rel` conjunct `gb <> sb` already provides it.

### Change 2: Add struct block writability to `abs_rel`

Add to the `abs_rel` / `abs_rel_with_ard` definition:

```coq
  Mem.range_perm m sb (Ptrofs.unsigned so)
    (Ptrofs.unsigned so + 56) Cur Writable /\
```

**Eliminates:** `store_succeeds_from_load` (axiom #5) for struct fields.

**Proof path:** `Mem.range_perm` + `Mem.valid_access` (alignment is 8, offsets
are multiples of 8) -> `Mem.valid_access_store`.

**Impact:** Must establish writability when constructing `abs_rel`. In a real
program, the struct is stack-allocated (`Mem.alloc` grants `Freeable >=
Writable`). Must preserve across stores (`Mem.store_valid_access_1`).

### Change 3: Add stack writability to `abs_rel`

Add to the sp clause:

```coq
  (exists sp_ptr sp_b sp_ofs,
    ...
    Mem.range_perm m sp_b 0 (Ptrofs.unsigned sp_ofs) Cur Writable /\  (* NEW *)
    ...)
```

This says: the stack block is writable from offset 0 up to the current sp.

**Eliminates:** `store_to_other_block` (#4) and `store_succeeds_stack` (#8).

**Proof path:** `Mem.range_perm` over `[0, sp_ofs)` plus alignment ->
`Mem.valid_access_store`. Preservation across stores to *other* blocks is by
`Mem.perm_store_1`.

### Change 4: Add stack representability to `abs_rel`

Add to the sp clause:

```coq
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s))
      < Ptrofs.modulus /\  (* NEW *)
```

**Eliminates:** `sp_ofs_stack_representable` (#10).

**Unlocks:** Proof of `stack_repr_store_same_block_lower` (#6), which in turn
unlocks `stack_repr_cons_after_store` (#7).

### Change 5: Add stack pointer lower bound to `abs_rel`

Add to the sp clause:

```coq
    Ptrofs.unsigned sp_ofs >= 8 /\  (* NEW *)
```

**Eliminates:** `sp_ofs_ge_8` (#9).

### Change 6: Delete false axioms

Delete `sp_block_ne_sptr` and `sp_block_ne_global`. Replace all call sites with
the hypothesis from `abs_rel` (`Hsp_ne_sb` / `Hsp_ne_gb`). This is mechanical:
every call site of `sp_block_ne_sptr ard sp_b` already has `Hsp_ne_sb` in scope.

---

## Dependency graph

```
abs_rel changes
  |
  +-- ar_global_ne_sptr (record field)
  |     \-> proves global_block_ne_sptr (#2)
  |
  +-- struct Writable (range_perm)
  |     \-> proves store_succeeds_from_load (#5)
  |
  +-- stack Writable (range_perm)
  |     +-> proves store_to_other_block (#4)
  |     \-> proves store_succeeds_stack (#8)
  |
  +-- stack representability (Ptrofs bound)
  |     +-> proves sp_ofs_stack_representable (#10)
  |     \-> proves stack_repr_store_same_block_lower (#6)
  |           \-> proves stack_repr_cons_after_store (#7)
  |
  +-- sp_ofs >= 8
  |     \-> proves sp_ofs_ge_8 (#9)
  |
  \-- delete false axioms
        +-> sp_block_ne_sptr (#1) -> use abs_rel conjunct
        \-> sp_block_ne_global (#3) -> use abs_rel conjunct
```

## Preservation obligations

Each new `abs_rel` conjunct must be preserved across handler execution:

| Conjunct | Preservation argument |
|---|---|
| struct Writable | `Mem.perm_store_1`: store preserves all permissions |
| stack Writable | Same; store to struct block preserves stack perms |
| stack representability | Pure arithmetic on Rocq state; unaffected by C memory ops |
| sp_ofs >= 8 | PUSH decreases sp by 8 but the old sp was >= 8, and POP increases it; other handlers don't change sp |

The Writable invariants have the nice property that `Mem.perm_store_1` gives
them for free after any store. The initial establishment (from `Mem.alloc`)
is the only non-trivial obligation, and that is part of the top-level
program setup (outside per-handler proofs).

## Execution order

1. Add `ar_global_ne_sptr` to `abs_rel_data`, fix witness construction
2. Add the 4 new conjuncts to `abs_rel` / `abs_rel_with_ard`
3. Prove `store_succeeds_from_load` and `store_succeeds_stack` from writability
4. Prove `sp_ofs_ge_8` and `sp_ofs_stack_representable` from conjuncts
5. Prove `stack_repr_store_same_block_lower` by induction
6. Prove `stack_repr_cons_after_store` from #5
7. Prove `store_to_other_block` from stack writability + `store_valid_access_1`
8. Delete `sp_block_ne_sptr` and `sp_block_ne_global`, fixup callers
9. Update every handler proof to destruct/preserve the new conjuncts
