# Plan: Eliminate 70 Remaining Admitted Handlers via Parallel Agents

## Context

151 bytecode handler correctness theorems need preconditions composed from named building blocks in InstructSpec.v. **81 are proved (Definition), 70 are Admitted.** All 70 Admitted handlers have completed proofs (Qed) in their `_correct.v` files — the `Admitted` in InstructVerification.v exists because the step_pres don't yet match the Module Type signatures.

**Goal**: Zero Admitted, zero False preconditions, zero contradictory step_pres. Every step_pre auditable by reading InstructSpec.v alone.

## Two Distinct Problems

### Problem 1: 53 handlers need wrapper theorems (building-block step_pres)
These have working proofs with non-contradictory step_pres. They just need wrapper theorems using `handler_correct_weaken` to bridge from building blocks to internal step_pres.

### Problem 2: ~12 handlers have contradictory step_pres (val_repr gap)
These close by `inversion` on an impossible `val_repr` case. The root cause: `val_repr` maps `Val_int` exclusively to `Vlong` (tagged integer), but code pointers in C are `Vptr`. When return addresses or handler PCs are stored on the stack as `Val_int pc` in Rocq, `stack_repr` (which uses `val_repr`) can't represent the corresponding `Vptr` in C memory.

**Affected handlers**:
- APPLY1, APPLY2, APPLY3 — push return address (Val_int pc) as Vptr on stack
- PUSHTRAP, PUSH_RETADDR — push handler_pc / ret_addr as Vptr
- RAISE, RAISE_NOTRACE, RERAISE — read handler_pc (Val_int) as Vptr from trap frame
- RETURN — read return address (Val_int) from stack
- RESTART — step_pre is literally `False` (different issue: data-dependent loop)

Handlers that DON'T have the contradiction despite being in Batch H:
- APPTERM1-3, APPTERM — tail calls, no return address push
- GRAB — closure code loading, not PC contradiction  
- POPTRAP — stack manipulation, no PC val_repr issue
- APPLY — need to verify

### Problem 2 Root Cause

`handler_correct` (InstructSpec.v:261-280) requires:
```rocq
| Step s' =>
    forall ard, abs_rel_with_ard e le m s ard -> step_pre e m s ard ->
    exists le' m' out,
      exec_stmt ... e le m f.(fn_body) E0 le' m' out /\
      abs_rel e le' m' s'    (* POST-state must satisfy abs_rel *)
```

After APPLY1 pushes `Val_int (pc+1)` onto the Rocq stack, the post-state `s'` has this value in `s'.stack`. The C code stores `Vptr code_b (code_ofs + (pc+1)*4)` at the same stack position. `abs_rel` requires `stack_repr` to hold, which uses `val_repr`. Since `val_repr` maps `Val_int` only to `Vlong`, `stack_repr` cannot relate the Rocq and C post-states. **The fix must change either val_repr or stack_repr.**

## val_repr Extension: Add Code Pointer Constructor

```rocq
Inductive val_repr (hm : nat -> option (block * ptrofs)) (cb : block) (co : ptrofs)
    : Value.value -> val -> Prop :=
  | vr_int : forall z,
      val_repr hm cb co (Val_int z) (Vlong (Int64.repr (z * 2 + 1)))
  | vr_ptr : forall addr b ofs,
      hm addr = Some (b, ofs) ->
      val_repr hm cb co (Val_ptr addr) (Vptr b ofs)
  | vr_closure : forall addr offset b ofs delta,
      hm addr = Some (b, ofs) ->
      delta = Ptrofs.repr (Z.of_nat offset * 8) ->
      val_repr hm cb co (Val_closure addr offset) (Vptr b (Ptrofs.add ofs delta))
  | vr_block_atom : forall tag,
      val_repr hm cb co (Val_block tag nil)
        (Vlong (Int64.repr (Z.of_nat tag * 1024)))
  | vr_code_ptr : forall pc,
      val_repr hm cb co (Val_int pc)
        (Vptr cb (Ptrofs.add co (Ptrofs.repr (pc * sizeof_code_t)))).
```

**Impact**: val_repr gains 2 parameters (cb, co). ~661 occurrences across 118 files need `cb co` added. stack_repr, global_repr, abs_rel all propagate cb/co. Mechanical but pervasive.

**Tradeoff**: val_repr becomes non-deterministic for `Val_int` — a `Val_int z` can be represented as either `Vlong` (tagged integer) or `Vptr` (code pointer). Proofs that invert on `val_repr (Val_int ...)` get an extra case to handle.

The non-determinism in val_repr is benign — in practice, the proof context always disambiguates which constructor applies (e.g., if we know the C value is Vlong, only vr_int can fire; if Vptr in the code section, only vr_code_ptr).

## Execution Plan

### Phase 0: val_repr Extension (prerequisite for ~12 handlers)

**Step 0a**: Extend val_repr with `vr_code_ptr` + add `cb co` parameters
**Step 0b**: Update stack_repr, global_repr, abs_rel to propagate cb/co
**Step 0c**: Fix all compilation errors in existing 81 proved handlers
**Step 0d**: Fix the 14 already-converted wrapper theorems (ACC, GETGLOBAL, BEQ, etc.)
**Step 0e**: Build and verify: `dune build instruct-verification/`
**Step 0f**: Commit

This is a large mechanical change. It can be partially parallelized:
- Agent in worktree: fix _correct.v files (add cb co to val_repr/stack_repr uses)
- Main: fix InstructSpec.v, InstructVerification.v, HandlerLemmas.v

**Estimated scope**: ~700 mechanical edits across ~120 files. Each edit is adding `cb co` or `(ar_code_base_block ard) (ar_code_base_ofs ard)` to val_repr/stack_repr calls.

### Phase 1: Central Preparation (building blocks + Module Type)

**Step 1a**: Read all 70 _correct.v files, catalog step_pres, determine building blocks
**Step 1b**: Add new building blocks to InstructSpec.v
**Step 1c**: Update all 70 Module Type entries to use building blocks
**Step 1d**: Update all 70 IV entries to match (still Admitted)
**Step 1e**: Build, commit

### Phase 2: Parallel Wrappers — Non-contradictory Handlers (3 agents, ~53 handlers)

**Constraint**: Maximum 5 agents can run in parallel at any time.

**Agent 1** (Batch A+B — 15 files): Heap read + env access
GETFIELD0-3, GETFIELD, GETFLOATFIELD, GETSTRINGCHAR, GETBYTESCHAR, GETVECTITEM, VECTLENGTH, ENVACC1-4, ENVACC

**Agent 2** (Batch C+D — 15 files): Heap write + closure offset
SETFIELD0-3, SETFIELD, SETFLOATFIELD, SETBYTESCHAR, SETVECTITEM, OFFSETREF, OFFSETCLOSURE2/M2/n, PUSHOFFSETCLOSURE2/M2/n

**Agent 3** (Batch E+F+misc — 23 files): Push+env, code/branch, C-function, non-contradictory control flow
PUSHENVACC1-4, PUSHENVACC, PUSHGETGLOBALFIELD, PUSHCONSTINT, ASSIGN, BRANCHIF, BRANCHIFNOT, GETGLOBALFIELD, SWITCH, GETDYNMET, GETMETHOD, GETPUBMET, MAKEBLOCK1-3, MAKEBLOCK, MAKEFLOATBLOCK, CLOSURE, CLOSUREREC, SETGLOBAL, APPTERM1-3, APPTERM, GRAB, POPTRAP

After agents complete: merge, update IV.v, build.

### Phase 3: Re-prove Contradictory Handlers (~12 handlers)

These need REAL Step case proofs, not inversion tricks. The val_repr extension enables this.

**Agent 4** (5 files): APPLY1, APPLY2, APPLY3, PUSHTRAP, PUSH_RETADDR
- Re-prove Step case: construct post-state abs_rel using `vr_code_ptr` for return address / handler_pc
- Building block step_pre: e.g., `sp_at_least 32` (APPLY) or `sp_at_least 40` (PUSHTRAP)

**Agent 5** (4 files): RAISE, RAISE_NOTRACE, RERAISE, RETURN
- Re-prove Step case: when reading return address / handler_pc from stack, use `vr_code_ptr` case of val_repr inversion (instead of contradiction)
- Building block step_pre: `no_pre` or `stack_has_return_frame`

**RESTART** (1 file): Full axiom-free proof using loop induction. Building block: `pre_and heap_header_consistent (sp_at_least N)`. Proof by induction on num_args (see RESTART section below). This is the hardest handler — ~280 lines of new proof code.

### Phase 4: Final Integration

- Wire all IV.v entries from Admitted to Definition
- `grep -c "Admitted" InstructVerification.v` → 0
- Full build: `dune build instruct-verification/`

## Phase 0 Approach: Mechanical val_repr Extension

The val_repr change is mechanical. Each occurrence follows one of these patterns:

**Pattern 1: val_repr in a type annotation / step_pre**
```diff
- val_repr hm v cv
+ val_repr hm cb co v cv
```
where `cb = ar_code_base_block ard` and `co = ar_code_base_ofs ard` (available from ard).

**Pattern 2: stack_repr usage**
```diff
- stack_repr hm m stk sp_b sp_ofs
+ stack_repr hm cb co m stk sp_b sp_ofs
```

**Pattern 3: Constructing val_repr (apply vr_int, etc.)**
No change needed — constructors just gain implicit parameters.

**Pattern 4: Inverting val_repr**
Extra case for `vr_code_ptr`. For most handlers, this case is vacuous (e.g., if we know the value is `Val_ptr`, the `Val_int` code pointer case can't fire).

**Parallelization** (max 5 agents in parallel): Since each _correct.v file is independent, agents in worktrees can fix batches of files in parallel. The main thread handles InstructSpec.v + HandlerLemmas.v + InstructVerification.v.

## RESTART: Axiom-Free Proof Strategy

RESTART's `False` step_pre is NOT due to val_repr — it's because the C code contains a data-dependent loop. The fix requires real loop verification.

### C Loop Structure
```c
_num_args = (int)((*((long*)env - 1) >> 10) - 3);
s->sp -= _num_args;
for (_i = 0; _i < _num_args; _i++)
    sp[_i] = ((long*)env)[_i + 3];
s->env = ((long*)env)[2];
s->extra_args += _num_args;
```

### Rocq Semantics
```rocq
let fields := skipn ofs all_fields in
let num_args := length fields - 3 in
let args := skipn 3 fields in
Step (s <|stack := args ++ s.(stack)|> <|env := saved_env|> ...)
```

### Building Blocks Needed

**heap_header_consistent** (extend heap_consistent with header access):
```rocq
Definition heap_header_consistent : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun _ m s ard =>
    let hm := ar_heap_map ard in
    forall addr b ofs tag fields,
      hm addr = Some (b, ofs) ->
      heap_lookup s.(hp) addr = Some (tag, fields) ->
      (* Fields loadable *)
      (forall i v, nth_error fields i = Some v ->
        exists cv, Mem.load Mint64 m b (Ptrofs.unsigned ofs + Z.of_nat i * 8) = Some cv /\
                   val_repr hm cb co v cv) /\
      (* Header loadable with correct size *)
      (exists hdr_word,
        Mem.load Mint64 m b (Ptrofs.unsigned ofs - 8) = Some (Vlong hdr_word) /\
        Int64.shru hdr_word (Int64.repr 10) = Int64.repr (Z.of_nat (length fields))) /\
      (* Block is separate from struct/stack/global *)
      b <> ar_sptr_block ard /\ b <> ar_global_block ard.
```

**RESTART step_pre building block**:
```rocq
pre_and heap_header_consistent (sp_at_least (num_args * 8))
```
where num_args is derived from the closure structure.

### Proof Structure (Axiom-Free)

The proof uses **induction on the number of fields to copy** (num_args):

1. **Extract num_args**: From heap_header_consistent, load header word. The C expression `(header >> 10) - 3` equals `length fields - 3` by the header consistency hypothesis.

2. **SP room**: From sp_at_least, the stack pointer can be decremented by num_args * 8 without underflowing.

3. **Loop invariant**: After iteration `i`, the first `i` stack slots contain the corresponding closure fields:
   ```
   forall j < i,
     Mem.load Mint64 m' sp_b (sp_ofs - num_args*8 + j*8) = Some cv_j /\
     val_repr hm (nth (j+3) fields) cv_j
   ```

4. **Base case** (num_args = 0): Loop body doesn't execute. The C code just updates env and extra_args. Straightforward.

5. **Inductive step**: One loop iteration:
   - Load field[i+3] from closure block (from heap_header_consistent)
   - Store to sp[i] (Mem.store succeeds because SP region is writable from abs_rel)
   - Memory after store still satisfies the loop invariant for previous fields (because closure block ≠ stack block, from block separation)
   - Advance loop counter

6. **Post-loop**: After all iterations, the stack region contains `args` (= skipn 3 fields). Load saved_env from field[2] (from heap_header_consistent). Construct post-state abs_rel:
   - Stack: args ++ old_stack → stack_repr holds (each field has val_repr from heap_header_consistent)
   - Env: saved_env → val_repr from heap_header_consistent
   - PC: unchanged (same pc_rel)
   - Extra_args: old + num_args (integer arithmetic)

### CompCert Loop Semantics

In Clight bigstep, the `for` loop is desugared to `Sloop (Sseq Sifthenelse body) Sskip`. Verification uses `exec_Sloop_loop` (loop body returns normally → continue) and `exec_Sloop_stop` (condition false → exit).

The key lemma to prove:
```rocq
Lemma restart_loop_correct :
  forall n env_b env_ofs sp_b sp_ofs m i_val,
    (* n remaining iterations *)
    (* heap fields at env_b are loadable *)
    (* SP region is writable *)
    ...
    exec_stmt ... e le m loop_body ... le' m' Out_normal.
```

This is proved by well-founded induction on `n` (iterations remaining), which decreases at each step.

### Estimated Complexity

This is the hardest single handler proof in the project:
- Loop invariant formulation: ~50 lines
- Loop correctness lemma: ~200 lines (induction + memory reasoning)  
- Wrapper integration: ~30 lines
- Total: ~280 lines of new proof code

But it is **fully axiom-free** — all reasoning follows from heap_header_consistent + abs_rel + CompCert memory model.

## Key Risks

1. **val_repr non-determinism**: After extension, `val_repr hm cb co (Val_int z) cv` has two possible `cv` values. Proofs that assumed determinism (e.g., `val_repr uniqueness lemmas`) may need updating.

2. **Scope of Phase 0**: ~700 mechanical edits is large. May take significant time even with parallel agents. Mitigated by the mechanical nature — each edit follows a fixed pattern.

3. **Re-proving Step cases (Phase 3)**: The ~12 contradictory handlers need real proofs, not just wrappers. This is genuine proof engineering work, not mechanical editing.

4. **RESTART loop proof**: ~280 lines of loop induction reasoning. The hardest single handler, but axiom-free.

## Critical Files

- `instruct-verification/theories/InstructSpec.v` — val_repr, stack_repr, abs_rel, building blocks, Module Type
- `instruct-verification/theories/InstructVerification.v` — Pure direct assignments
- `instruct-verification/theories/HandlerLemmas.v` — Shared lemmas (heavily uses val_repr/stack_repr)
- 151 `_correct.v` files — Per-handler proofs

## Verification

After each phase:
```bash
cd verified-ocaml && dune build instruct-verification/
```

Final checks:
```bash
grep -c "Admitted" instruct-verification/theories/InstructVerification.v  # 0
grep "False" instruct-verification/theories/InstructSpec.v | grep -c "step_pre\|:="  # 0
```
