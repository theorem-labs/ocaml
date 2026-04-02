# Unified Handler Verification Plan

**Goal: 151 handler proofs, 0 axioms, 0 Admitted.**

---

## Current State (2026-04-02)

| Category | Count | Details |
|----------|-------|---------|
| Handler files exist | 128 / 151 | |
| Clean (Qed, 0 Axiom) | 118 | Compile, no Admitted, no Axiom |
| Compile failures | 8 | APPLY, APPTERM1, CLOSURE, GETDYNMET, MAKEBLOCK2, POPTRAP, SETVECTITEM, VECTLENGTH |
| Timeout/Admitted | 2 | GRAB (line 617), SWITCH (line 738) -- eval_cbn too slow |
| Missing handler files | 23 | Need new files created |
| Not in _RocqProject | 15 | 6 clean + 7 broken + 2 admitted |
| HandlerLemmas.v axioms | 0 | Was 5, all eliminated |
| VECTLENGTH axioms | 6 | Blocked on Phase 6 (heap_block_well_formed) |

**Completed infrastructure** (from prior sessions):
- store_succeeds_sb, store_to_sp_after_sb_store proved in HandlerLemmas.v
- ExternalCallSpecs.v created (heap_alloc_spec, caml_modify_spec)
- MAKEBLOCK1 refactored (0 axiom, 0 Admitted)
- SETGLOBAL refactored (0 axiom, 0 Admitted)
- abs_rel alignment field added to InstructSpec.v

---

## CRITICAL RULES

These rules are NON-NEGOTIABLE. Every agent prompt MUST include them.
Paste the block below into every agent prompt verbatim.

```
=== ABSOLUTE RULES (violating any of these = immediate failure) ===

1. NEVER write `Admitted.` in any file. NOT EVEN TEMPORARILY.
   If you cannot close a goal, add a step_pre precondition instead.

2. NEVER write `Axiom` in any file. NOT EVEN AS A PLACEHOLDER.
   If you need a fact, prove it or add it to step_pre.

3. NEVER run `dune build`. NOT EVEN ONCE.
   Multiple agents run in parallel. dune takes a global lock and will
   fail or corrupt state. Use coqc DIRECTLY:

   cd /workspaces/theorem-work/theorem-ocaml/verified-ocaml/instruct-verification
   coqc -R ../../_build/default/instruct-verification/theories InstructVerification \
        -Q ../../_build/default/manual OCamlInterp.Manual theories/HANDLER_correct.v

4. NEVER use compute, vm_compute, native_compute on large terms.
   These cause memory blowup. Use rewrite, simpl, cbn only on small
   focused subterms. If compilation takes >60s, restructure.

5. Every proof MUST end with `Qed.` -- never Defined, never Admitted.

6. Before declaring success, run BOTH:
   a) coqc command above (must exit 0 with no errors)
   b) grep -c "Admitted\|^Axiom" theories/HANDLER_correct.v (must print 0)

=== END ABSOLUTE RULES ===
```

---

## Agent Protocol

### Concurrency: MAX 5 AGENTS AT ANY TIME

- Launch agents for one batch at a time.
- Wait for ALL agents in the current batch to finish before launching the next.
- If a batch has <5 agents AND the next batch is independent, you MAY
  start both simultaneously (but total running must stay <= 5).
- Example: Batch 1B (3 agents) + Batch 2 (2 agents) = 5 total. OK.

### Per-agent checklist

1. Agent prompt includes the CRITICAL RULES block above.
2. Agent prompt specifies: file to fix/create, exact error or template, coqc command.
3. Agent uses `coqc` (not dune) to verify.
4. Agent runs `grep -c "Admitted\|^Axiom"` on the file.
5. Agent reports success/failure.

### Between batches

After all agents in a batch return:
1. Check each file compiles: `coqc ... theories/HANDLER_correct.v`
2. Check no Admitted/Axiom: `grep -rn "^Admitted\.\|^Axiom " theories/HANDLER_correct.v`
3. If any agent failed, queue the file for the next batch.
4. Update PROGRESS.md with results.
5. Only then launch the next batch.

---

## Phase 1: Fix Compile Failures (8 files)

All 8 files are independent. Fix in 2 batches.

### Batch 1A: Launch 5 agents in parallel

**Agent 1A-1: Fix VECTLENGTH_correct.v**
- Error at line 365: `store_succeeds_from_load` not found
- Fix: replace `store_succeeds_from_load` with `store_succeeds_sb` throughout
- The signature is the same. This is a trivial rename.
- Also has 6 local axioms -- DO NOT touch those yet (Phase 6).
  The 6 axioms are allowed to remain for now. Only fix the compile error.
- Read ADDINT_correct.v for reference on how store_succeeds_sb is used.
- Verify: `coqc -R ../../_build/default/instruct-verification/theories InstructVerification -Q ../../_build/default/manual OCamlInterp.Manual theories/VECTLENGTH_correct.v`

**Agent 1A-2: Fix GETDYNMET_correct.v**
- Error at line 181: `Machine.set_accu` not found in current environment
- Fix: `Machine.set_accu` does not exist. Replace with the record update
  pattern used by all other handlers. Read ADDINT_correct.v to see how
  the post-state is constructed (direct record literal or `mk_state`).
- Verify: `coqc ... theories/GETDYNMET_correct.v`

**Agent 1A-3: Fix APPLY_correct.v**
- Error at line 334: `Found no subterm matching "Mem.store Mint64 m sb (Ptrofs.unsigned so + 32) ea_val"`
- Fix: the rewrite target doesn't match the goal. Read the file around line 334,
  understand the goal shape, and fix the store offset or variable name to
  match what's actually in the goal.
- Verify: `coqc ... theories/APPLY_correct.v`

**Agent 1A-4: Fix POPTRAP_correct.v**
- Error at line 363: `Found no subterm matching "(PTree.set ?M ?M ?M) ! ?M"`
- Fix: the PTree.gss/gso rewrite doesn't find a matching pattern. Read the
  proof around line 363, print/understand the goal, and fix the PTree lemma
  application order or target.
- Verify: `coqc ... theories/POPTRAP_correct.v`

**Agent 1A-5: Fix CLOSURE_correct.v**
- Error at line 192: `Unable to unify "Some (Vlong (Int64.or a (Int64.repr b)))" with "sem_binary_operation ge Oor (Vlong a) tlong (Vint (Int.repr b)) tint m"`
- Fix: CompCert's `sem_binary_operation Oor` with mixed Vlong/Vint (tlong/tint)
  doesn't reduce to Int64.or directly. Either: (a) both arguments need to be
  Vlong/tlong, requiring a cast; or (b) the C AST needs an Ecast wrapping.
  Check how ORINT_correct.v handles the `Oor` operation for reference.
- Verify: `coqc ... theories/CLOSURE_correct.v`

### Batch 1B + Batch 2: Launch 5 agents in parallel (3 fixes + 2 timeouts)

Wait for Batch 1A to complete. Then launch these 5 together:

**Agent 1B-1: Fix MAKEBLOCK2_correct.v**
- Error at line 1355: type mismatch -- hypothesis has `... -> stack_repr ...`
  but goal expects plain `stack_repr ...`
- Fix: the proof provides a term with undischarged `->` premises. Need to
  apply/discharge the extra hypotheses before passing as the stack_repr witness.
  Read the file around line 1355, understand what premises are dangling, and
  apply them. Use `assert` + `exact` or feed the hypotheses explicitly.
- Read MAKEBLOCK1_correct.v for reference on how stack_repr is handled
  after heap allocation.
- Verify: `coqc ... theories/MAKEBLOCK2_correct.v`

**Agent 1B-2: Fix SETVECTITEM_correct.v**
- Error at line 89: `Tactic failure: Cannot find witness`
- Fix: an eexists or eauto can't find a memory state witness (likely for a
  Mem.store existence proof). Provide an explicit `exists m'` where m' comes
  from a Mem.store success hypothesis. Check that store_succeeds_sb is being
  used correctly, and that the right Hsb_writable + load hypotheses are available.
- Read SETGLOBAL_correct.v for reference on external-call handler patterns.
- Verify: `coqc ... theories/SETVECTITEM_correct.v`

**Agent 1B-3: Fix APPTERM1_correct.v**
- Error at line 338: `Unable to unify ... Ptrofs.unsigned (Ptrofs.neg (Ptrofs.repr 8)) = k * Ptrofs.modulus + (Z.of_nat slotsize - 1) * 8`
- Fix: `Ptrofs.unsigned (Ptrofs.neg (Ptrofs.repr 8))` doesn't simplify
  automatically. It equals `Ptrofs.modulus - 8` when 8 < Ptrofs.modulus.
  Add a rewrite using `Ptrofs.unsigned_neg` or prove an intermediate lemma.
  May also need `Ptrofs.unsigned_repr` with modulus bounds.
- Verify: `coqc ... theories/APPTERM1_correct.v`

**Agent 2-1: Fix GRAB_correct.v (remove Admitted)**
- Admitted at line 617. The eval_cbn tactic times out on ~40 C statements.
- Fix: replace the entire Part 1 proof (C execution) with **explicit bigstep
  proof construction** using exec_Ssequence, exec_Sset, eval_Elvalue,
  eval_Ederef, eval_Ebinop, etc. For each C statement `Sset id expr`,
  construct an explicit `exec_Sset` with `eval_expr` derivations that
  use the known hypotheses (Hle_s, Hpc_load, Haccu_load, etc.).
- Lines 347-415 show commented-out eval_cbn attempts -- these show the
  proof structure but eval_cbn is too slow. Build it manually instead.
- Read MAKEBLOCK1_correct.v Part 1 for an example of explicit bigstep style.
- GRAB has two branches (if extra_args >= 1 vs closure construction case).
  Both branches need explicit bigstep proofs.
- **CRITICAL: The proof MUST end with `Qed.` NOT `Admitted.`**
- Verify: `coqc ... theories/GRAB_correct.v`
- Verify: `grep -c "Admitted" theories/GRAB_correct.v` prints 0

**Agent 2-2: Fix SWITCH_correct.v (remove Admitted)**
- Admitted at line 738. Same timeout problem as GRAB.
- Fix: same approach -- replace eval_cbn with explicit bigstep construction.
- Lines 441-581 show eval_cbn calls that work individually but combined
  they timeout. Build the proof manually step by step.
- SWITCH has two code paths (block tag vs int tag). Both need explicit proofs.
- Read MAKEBLOCK1_correct.v Part 1 for explicit bigstep reference.
- **CRITICAL: The proof MUST end with `Qed.` NOT `Admitted.`**
- Verify: `coqc ... theories/SWITCH_correct.v`
- Verify: `grep -c "Admitted" theories/SWITCH_correct.v` prints 0

---

## Phase 3: Create Easy Missing Handlers (4 files)

Template clones with 2-4 line diffs. 1 batch of 4 agents.
Can run as soon as Phase 1+2 finishes (or in parallel if slots available).

### Batch 3: Launch 4 agents

**Agent 3-1: Create BLTINT_correct.v**
- Clone BEQ_correct.v. Change comparison operator from `Ceq` to `Clt`.
- Change the Rocq handler from `handle_BEQ` to whatever the BLTINT handler is
  (check instruct_handlers.v and InstructSpec.v).
- Change the C function from `f_instr_BEQ` to `f_instr_BLTINT`.
- Verify: `coqc ... theories/BLTINT_correct.v`

**Agent 3-2: Create BLEINT_correct.v**
- Clone BEQ_correct.v. Change comparison operator from `Ceq` to `Cle`.
- Same pattern as BLTINT. Check instruct_handlers.v for handler name.
- Verify: `coqc ... theories/BLEINT_correct.v`

**Agent 3-3: Create MAKEBLOCK3_correct.v**
- Clone MAKEBLOCK1_correct.v. Add a third field store (for field index 2).
- The handler allocates a 3-field block. Needs one additional Mem.store for
  the third field and corresponding load-preservation / writable-preservation
  chaining.
- Verify: `coqc ... theories/MAKEBLOCK3_correct.v`

**Agent 3-4: Create SETBYTESCHAR_correct.v**
- Clone GETSTRINGCHAR_correct.v. Reverse direction: write instead of read.
- Check instruct_handlers.v for the exact handler semantics.
- Verify: `coqc ... theories/SETBYTESCHAR_correct.v`

---

## Phase 4: Create Medium Missing Handlers (13 files)

**Prerequisite**: Phase 1 must complete (APPLY, APPTERM1, CLOSURE are templates).
Phase 2 should complete too (GRAB is template for RESTART).

### Batch 4A: Launch 5 agents

**Agent 4A-1: Create RETURN_correct.v**
- Template: STOP_correct.v + POP_correct.v
- Semantics: pop pc, env, extra_args from stack; if extra_args > 0, apply;
  else jump to pc. Check instruct_handlers.v.

**Agent 4A-2: Create APPLY1_correct.v**
- Template: APPLY_correct.v (must be fixed first)
- Semantics: fixed 1-arg apply. Push retaddr frame, jump to closure.

**Agent 4A-3: Create APPLY2_correct.v**
- Template: APPLY_correct.v (fixed)
- Semantics: fixed 2-arg apply.

**Agent 4A-4: Create APPLY3_correct.v**
- Template: APPLY_correct.v (fixed)
- Semantics: fixed 3-arg apply.

**Agent 4A-5: Create PUSH_RETADDR_correct.v**
- Template: PUSH_correct.v
- Semantics: push PC+offset, env, extra_args (3 values) to stack.

All agents: verify with coqc, no Admitted, no Axiom.

### Batch 4B: Launch 5 agents

**Agent 4B-1: Create APPTERM_correct.v**
- Template: APPTERM1_correct.v (must be fixed first)
- Semantics: parametric appterm with stack copy loop.

**Agent 4B-2: Create APPTERM2_correct.v**
- Template: APPTERM1_correct.v (fixed)
- Semantics: fixed 2-arg tail apply.

**Agent 4B-3: Create APPTERM3_correct.v**
- Template: APPTERM1_correct.v (fixed)
- Semantics: fixed 3-arg tail apply.

**Agent 4B-4: Create RESTART_correct.v**
- Template: GRAB_correct.v (must be fixed first -- no Admitted)
- Semantics: inverse of GRAB. Unpack closure fields back to stack.

**Agent 4B-5: Create CLOSUREREC_correct.v**
- Template: CLOSURE_correct.v (must be fixed first)
- Semantics: recursive closure. Multiple heap allocs + infix headers.
- This is the hardest handler in this batch.

All agents: verify with coqc, no Admitted, no Axiom.

### Batch 4C: Launch 3 agents

**Agent 4C-1: Create SETFLOATFIELD_correct.v**
- Template: GETFLOATFIELD_correct.v + SETGLOBAL_correct.v
- Semantics: float field write using caml_modify.

**Agent 4C-2: Create GETPUBMET_correct.v**
- Template: GETMETHOD_correct.v
- Semantics: public method lookup. Code buffer read + push + method table scan.

**Agent 4C-3: Create MAKEBLOCK_correct.v (parametric)**
- Template: MAKEBLOCK1_correct.v
- Semantics: parametric MAKEBLOCK with loop over fields. Uses Sloop in C.

All agents: verify with coqc, no Admitted, no Axiom.

---

## Phase 5: Create Hard Missing Handlers (6 files)

**Prerequisite**: Phase 4 must complete (PUSH_RETADDR, POPTRAP, RAISE templates).

### Batch 5A: Launch 3 agents

**Agent 5A-1: Create PUSHTRAP_correct.v**
- Template: PUSH_RETADDR_correct.v (from Phase 4)
- Semantics: push 4 values (pc+offset, env, extra_args, trap_sp) to stack,
  update trap_sp to current sp.

**Agent 5A-2: Create RAISE_correct.v**
- Template: POPTRAP_correct.v (must be fixed in Phase 1)
- Semantics: pop trap frame, restore pc/sp/trap_sp/extra_args. Complex.

**Agent 5A-3: Create SETFIELD_correct.v (parametric)**
- Template: SETFIELD0_correct.v + SETGLOBAL_correct.v
- Semantics: parametric field set with caml_modify external call.

All agents: verify with coqc, no Admitted, no Axiom.

### Batch 5B: Launch 3 agents

**Agent 5B-1: Create RERAISE_correct.v**
- Template: RAISE_correct.v (from 5A -- must complete first)
- Semantics: same C body as RAISE, different backtrace behavior.

**Agent 5B-2: Create RAISE_NOTRACE_correct.v**
- Template: RAISE_correct.v (from 5A)
- Semantics: same C body as RAISE, no backtrace.

**Agent 5B-3: Create MAKEFLOATBLOCK_correct.v**
- Template: MAKEBLOCK1_correct.v
- Semantics: heap allocation for float array. Double_tag header.

All agents: verify with coqc, no Admitted, no Axiom.

---

## Phase 6: Finalize

### Batch 6A: VECTLENGTH Axiom Elimination (1 agent, run alone)

This touches InstructSpec.v and potentially all handler files.
Run this agent ALONE (no other agents) to avoid conflicts.

**Agent 6A-1: Eliminate VECTLENGTH axioms**
- Add `heap_block_well_formed` invariant to `abs_rel_with_ard` in InstructSpec.v
- Update all 120+ handler proofs (mechanical: thread new conjunct through destructs)
- Refactor VECTLENGTH_correct.v to use new invariant (eliminates 6 local axioms)
- Delete the 6 axiom declarations from VECTLENGTH_correct.v
- **RISK**: touches every handler file. Verify each one compiles after changes.
- Verify: run coqc on EVERY handler file (write a shell loop)
- Verify: `grep -rn "^Axiom " theories/*_correct.v` returns nothing

### Batch 6B: _RocqProject Registration + Final Build (manual, no agents)

After all files compile clean:
1. Add all missing entries to `theories/_RocqProject`
2. Remove stale .glob/.vo/.vos/.vok from source tree:
   `cd theories && rm -f *.glob *.vo *.vos *.vok *.aux`
3. Run `dune build instruct-verification` (OK here -- single build, no agents)
4. Final verification:
   - `grep -rn "^Admitted\." theories/*_correct.v` returns nothing
   - `grep -rn "^Axiom " theories/*_correct.v` returns nothing
   - `ls theories/*_correct.v | wc -l` prints 151

---

## Execution Summary

```
Batch 1A:  5 agents  [VECTLENGTH, GETDYNMET, APPLY, POPTRAP, CLOSURE]
           wait...
Batch 1B:  3 agents  [MAKEBLOCK2, SETVECTITEM, APPTERM1]
Batch 2:  +2 agents  [GRAB, SWITCH]                        = 5 total
           wait...
Batch 3:   4 agents  [BLTINT, BLEINT, MAKEBLOCK3, SETBYTESCHAR]
           wait...
Batch 4A:  5 agents  [RETURN, APPLY1, APPLY2, APPLY3, PUSH_RETADDR]
           wait...
Batch 4B:  5 agents  [APPTERM, APPTERM2, APPTERM3, RESTART, CLOSUREREC]
           wait...
Batch 4C:  3 agents  [SETFLOATFIELD, GETPUBMET, MAKEBLOCK(param)]
           wait...
Batch 5A:  3 agents  [PUSHTRAP, RAISE, SETFIELD(param)]
           wait...
Batch 5B:  3 agents  [RERAISE, RAISE_NOTRACE, MAKEFLOATBLOCK]
           wait...
Batch 6A:  1 agent   [VECTLENGTH axiom elimination -- run ALONE]
           wait...
Batch 6B:  manual    [_RocqProject, dune build, final checks]
```

**Total: 10 agent batches + 1 manual step. Never >5 agents running.**

---

## Reference: Error Details for Phase 1

### VECTLENGTH_correct.v:365
```
The variable store_succeeds_from_load was not found
```
Trivial rename to `store_succeeds_sb`.

### GETDYNMET_correct.v:181
```
The reference Machine.set_accu was not found
```
Replace with record update (see ADDINT_correct.v).

### APPLY_correct.v:334
```
Found no subterm matching "Mem.store Mint64 m sb (Ptrofs.unsigned so + 32) ea_val"
```
Read goal, fix store offset or variable name.

### POPTRAP_correct.v:363
```
Found no subterm matching "(PTree.set ?M ?M ?M) ! ?M"
```
Fix PTree.gss/gso application order.

### CLOSURE_correct.v:192
```
Unable to unify "Some (Vlong (Int64.or a (Int64.repr b)))" with
"sem_binary_operation ge Oor (Vlong a) tlong (Vint (Int.repr b)) tint m"
```
Mixed tlong/tint. Both args must be Vlong. See ORINT_correct.v.

### MAKEBLOCK2_correct.v:1355
```
Type mismatch: "... -> stack_repr ..." expected "stack_repr ..."
```
Discharge `->` premises before passing witness. See MAKEBLOCK1_correct.v.

### SETVECTITEM_correct.v:89
```
Tactic failure: Cannot find witness
```
Provide explicit `exists m'` from store success.

### APPTERM1_correct.v:338
```
Unable to unify ... Ptrofs.unsigned (Ptrofs.neg (Ptrofs.repr 8)) =
k * Ptrofs.modulus + (Z.of_nat slotsize - 1) * 8
```
Add `Ptrofs.unsigned_neg` rewriting.

---

## Reference: External Call Specs (ExternalCallSpecs.v)

| Spec | Used by |
|------|---------|
| `heap_alloc_spec` | MAKEBLOCK1/2/3, MAKEBLOCK(loop), MAKEFLOATBLOCK, CLOSURE, CLOSUREREC, GRAB |
| `caml_modify_spec` | SETGLOBAL, SETFIELD(param), SETVECTITEM, SETFLOATFIELD, SETBYTESCHAR |
| `ext_func_findable` | All external-call handlers |

### step_pre patterns

| Handler family | step_pre includes |
|---------------|-------------------|
| Simple (ACC, CONST, PUSH, ADDINT, ...) | `True` |
| PUSH family | `sp_ofs >= 16` (stack room) |
| MAKEBLOCK1/2/3, CLOSURE, CLOSUREREC, GRAB | `heap_alloc_spec` + `ext_func_findable _heap_alloc` |
| SETGLOBAL, SETFIELD(param), SETVECTITEM | `caml_modify_spec` + `ext_func_findable _caml_modify` |
| APPLY, APPTERM, RETURN | `closure_code_loadable` |
| PUSHTRAP, POPTRAP, RAISE | `trap_frame_well_formed` |

---

## Reference: Invariants

### heap_block_well_formed (Phase 6A -- add to abs_rel_with_ard)

Needed by ~40 handlers. Eliminates VECTLENGTH's 6 axioms. Provides
field-loadability for GETFIELD, ENVACC, etc.

Maintenance: non-heap-modifying handlers preserve it via `Mem.load_store_other`.
Heap-modifying handlers (MAKEBLOCK, SETFIELD, CLOSURE) re-establish it.

### closure_code_loadable (in step_pre)

Needed by ~25 handlers (APPLY, APPTERM, RETURN, GRAB, CLOSURE, CLOSUREREC).
Ensures closure code pointer is loadable from heap block.

### trap_frame_well_formed (in abs_rel_with_ard)

Needed by 5 handlers (PUSHTRAP, POPTRAP, RAISE, RERAISE, RAISE_NOTRACE).
PUSHTRAP establishes it; POPTRAP and RAISE consume it.

---

## Reference: Writable Preservation Patterns

Every handler must prove sp_writable and sb_writable in postcondition.

| Family | Memory chain | Pattern |
|--------|-------------|---------|
| Simple (ACC, CONST, ADDINT) | m -> m1 (sb store) | 1x perm_store_1 |
| PUSH (PUSHACC, PUSHCONST) | m -> m1 (sb) -> m2 (sp) | 2x perm_store_1 |
| MAKEBLOCK | m -> m1 (sb) -> m_alloc (ext) -> m2..n | perm_store_1 + ext_perm + Nx perm_store_1 |
| SETGLOBAL | m -> m1 (sb) -> m_cm (ext) -> m2 (sb) | perm_store_1 + ext_perm + perm_store_1 |
| SETFIELD0-3 | m -> m1 (sp) -> m2 (heap) -> m3 (sb) | 3x perm_store_1 |

---

## Risk Areas

1. **GRAB and SWITCH timeouts**: Explicit bigstep is labor-intensive (~40-50 steps).
   These are the hardest fixes. May need multiple attempts.
2. **CLOSUREREC**: Most complex handler (multiple allocs + loop). May need
   Sloop bigstep reasoning.
3. **Phase 6A**: Touches every handler file. One mistake breaks all.
   Run this agent ALONE and verify every file.
4. **Template dependencies**: APPLY1-3 need APPLY fixed. APPTERM2-3 need
   APPTERM1 fixed. CLOSUREREC needs CLOSURE fixed. RERAISE/RAISE_NOTRACE
   need RAISE done. RESTART needs GRAB done. Batches are ordered for this.
5. **dune build**: NEVER during agent execution. Only in Phase 6B final check.
