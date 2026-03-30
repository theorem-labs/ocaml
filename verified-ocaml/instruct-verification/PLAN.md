# Battle Plan: Verify All 79 Instruction Handlers

## Status Quo

**Proved (5):** ACC0, PUSH, CONST0, NEGINT, ADDINT
**Remaining (74):** Everything else in InstructSpec.v

## Architecture: Proof Factory

Every proof follows the same 2-part structure:

1. **Part 1 (exec):** Prove `comp_eval_stmt` computes to `Some (le', m', Out_return (Some (Vint Int.zero)))` via `eval_stmt_to_exec` + interleaved `eval_cbn` / `rewrite` chain
2. **Part 2 (abs_rel):** Reconstruct all 8 fields of `abs_rel` for the post-state

Proof size scales with **number of memory stores**:
- 0 stores (BRANCH, CHECK_SIGNALS): ~80 lines
- 1 store (ACC, CONST, NEGINT): ~120-250 lines
- 2 stores (PUSH, ADDINT, PUSHACC): ~270-400 lines
- 3+ stores (MAKEBLOCK, SETFIELD): ~400+ lines

## Phase 0: Lemma Library Expansion (Sequential, Blocking)

All proofs import `HandlerLemmas.v`. New lemmas must land before proof agents can use them. Expand in one batch.

### Needed lemma families

| Family | Lemmas needed | Used by |
|--------|--------------|---------|
| **Stack indexing** | `sem_add_sp_N` for N=2..7, `stack_repr_nth` for indexed access | ACC1-7, PUSHACC1-7 |
| **Tagged arithmetic** | `tagged_subint_arith`, `tagged_mulint_arith`, `tagged_andint_arith`, `tagged_orint_arith`, `tagged_xorint_arith`, `tagged_lslint_arith`, `tagged_lsrint_arith`, `tagged_asrint_arith` | SUBINT, MULINT, ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT |
| **Tagged constants** | `sem_const_N_arith` for N=1,2,3 (generalize CONST0 pattern) | CONST1-3 |
| **Comparison results** | `tagged_eq_result`, `tagged_neq_result`, `tagged_ltint_result`, `tagged_leint_result`, `tagged_gtint_result`, `tagged_geint_result` | EQ, NEQ, LTINT, LEINT, GTINT, GEINT |
| **Branch PC** | `sem_add_pc_offset` (PC + signed offset) | BRANCH, BRANCHIF, BRANCHIFNOT, BEQ-BGEINT |
| **Heap field access** | `heap_getfield_N` for N=0..3, `heap_setfield_N` | GETFIELD0-3, SETFIELD0-3 |
| **Block allocation** | `heap_makeblock_1/2/3`, `atom_alloc` | MAKEBLOCK1-3, ATOM, PUSHATOM |
| **Global access** | `global_repr_nth`, `global_repr_set_nth` | GETGLOBAL, SETGLOBAL |
| **Boolean/type** | `tagged_boolnot`, `tagged_isint` | BOOLNOT, ISINT |
| **Offset operations** | `tagged_offsetint_arith` | OFFSETINT, OFFSETREF |

**Estimate:** ~40-50 new lemmas. Many are reflexivity proofs or simple `lia` proofs following existing patterns.

## Phase 1: Clone Army (Massively Parallel)

Handlers whose C code is structurally identical to a proved handler, differing only in a constant or a single semantic operation.

### Wave 1A: ACC family (8 handlers, clone ACC0)

`ACC1, ACC2, ACC3, ACC4, ACC5, ACC6, ACC7, ACC`

Each differs from ACC0 only in the stack index. ACC0 loads `*sp`, ACC1 loads `*(sp+1)`, etc. The parameterized `ACC` uses `*(sp+n)` from a function argument.

**Template delta:** Change `handle_ACC 0` -> `handle_ACC N`, `f_instr_ACC0` -> `f_instr_ACCN`, stack offset lemma `sem_add_sp_0` -> `sem_add_sp_N`.

### Wave 1B: CONST family (4 handlers, clone CONST0)

`CONST1, CONST2, CONST3, CONSTINT`

Each differs in the constant value. CONST0 computes `(0<<1)+1=1`, CONST1 computes `(1<<1)+1=3`, etc.

**Template delta:** Change constant value, tagged arithmetic lemma.

### Wave 1C: Trivial no-ops (3 handlers)

`CHECK_SIGNALS, BRANCH, STOP`

- CHECK_SIGNALS: Only modifies PC. Zero stores, zero arithmetic.
- BRANCH: Only modifies PC to `target`. One field update.
- STOP: Returns `Halt`. No state modification at all.

**These are the simplest possible proofs.** ~60-80 lines each.

**Total Wave 1: 15 handlers, 15 parallel agents**

## Phase 2: Binary Arithmetic (Parallel after Phase 0 lemmas)

### Wave 2A: Arithmetic ops (10 handlers, template from ADDINT)

`SUBINT, MULINT, DIVINT, MODINT, ANDINT, ORINT, XORINT, LSLINT, LSRINT, ASRINT`

All share ADDINT's structure: pop stack, compute binary op on tagged ints, store result. The only difference is the arithmetic identity lemma.

- SUBINT: `(2a+1) - (2b+1) + 1 = 2(a-b)+1`
- MULINT: `((2a+1) >> 1) * ((2b+1) - 1) + 1 = 2(a*b)+1` (more complex -- untag, multiply, retag)
- ANDINT: `(2a+1) & (2b+1) = 2(a land b)+1` (tag bit preserved by AND)
- ORINT: `(2a+1) | (2b+1) = 2(a lor b)+1` (tag bit preserved by OR)
- XORINT: `(2a+1) ^ (2b+1) ^ 1 = 2(a lxor b)+1` (XOR flips tag, must fix)
- LSLINT/LSRINT/ASRINT: shift operations with untagging
- DIVINT/MODINT: Same but with zero-check branch -> Error path too

**Template delta from ADDINT:** Replace `tagged_addint_arith` with the op-specific lemma. DIVINT/MODINT need an extra branch for division-by-zero.

### Wave 2B: Unary/offset ops (2 handlers, template from NEGINT)

`OFFSETINT, BOOLNOT`

- OFFSETINT: Like NEGINT but adds offset instead of negating
- BOOLNOT: Simpler -- just flips 0<->1

**Total Wave 2: 12 handlers, 12 parallel agents**

## Phase 3: Comparisons & Branches (Parallel)

### Wave 3A: Integer comparisons (6 handlers)

`EQ, NEQ, LTINT, LEINT, GTINT, GEINT`

All follow the same pattern: pop stack, compare accu vs stack top, push boolean result (Val_int 0 or Val_int 1). Two stores (sp++, accu := result).

**Shared structure:** Identical to ADDINT except the arithmetic is a comparison yielding a boolean.

### Wave 3B: Conditional branches (2 handlers)

`BRANCHIF, BRANCHIFNOT`

Load accu, compare to Val_int 0, set PC to either target or pc'. One store (PC update), conditional logic.

### Wave 3C: Unsigned comparisons (2 handlers)

`ULTINT, UGEINT`

Like LTINT/GEINT but with `z_flip_sign` for unsigned semantics.

### Wave 3D: ISINT (1 handler)

Simple type check -- sets accu based on whether current accu is an int.

**Total Wave 3: 11 handlers, 11 parallel agents**

## Phase 4: Compound Operations (Parallel)

### Wave 4A: PUSHACC family (7 handlers, compose PUSH + ACC)

`PUSHACC1, PUSHACC2, PUSHACC3, PUSHACC4, PUSHACC5, PUSHACC6, PUSHACC7`

Each does PUSH (store accu to stack, sp--) then ACC (load from stack). Three stores total.

### Wave 4B: PUSHCONST family (5 handlers, compose PUSH + CONST)

`PUSHCONST0, PUSHCONST1, PUSHCONST2, PUSHCONST3, PUSHCONSTINT`

### Wave 4C: POP and ASSIGN (2 handlers)

- POP: Increment SP by n (skip n stack elements)
- ASSIGN: Write accu into stack at position n, set accu to unit

### Wave 4D: PUSHGETGLOBAL (1 handler)

PUSH + GETGLOBAL combined.

**Total Wave 4: 15 handlers, 15 parallel agents**

## Phase 5: Heap & Global Operations (Parallel)

### Wave 5A: Field access (10 handlers)

`GETFIELD0, GETFIELD1, GETFIELD2, GETFIELD3, GETFIELD`
`SETFIELD0, SETFIELD1, SETFIELD2, SETFIELD3, SETFIELD`

GETFIELD: Load field from heap block (1 store to accu).
SETFIELD: Store to heap block field + pop stack (2-3 stores).

### Wave 5B: Block construction (5 handlers)

`ATOM, PUSHATOM, MAKEBLOCK1, MAKEBLOCK2, MAKEBLOCK3`

These allocate on the heap. Need heap allocation lemmas.

### Wave 5C: Globals (3 handlers)

`GETGLOBAL, PUSHGETGLOBAL, SETGLOBAL`

### Wave 5D: Vectors (3 handlers)

`VECTLENGTH, GETVECTITEM, SETVECTITEM`

**Total Wave 5: 21 handlers, 21 parallel agents** (can split into sub-waves if lemma work is heavy)

## Phase 6: Complex Control Flow (Sequential pairs)

### Wave 6A: Branch-compare family (6 handlers)

`BEQ, BNEQ, BLTINT, BLEINT, BGTINT, BGEINT`

Conditional branch based on comparing accu to an immediate. Structurally like BRANCHIF but with arithmetic comparison.

### Wave 6B: Unsigned branch-compare (2 handlers)

`BULTINT, BUGEINT`

### Wave 6C: OFFSETREF (1 handler)

Modifies a heap ref cell -- combination of heap read + write.

### Wave 6D: SWITCH (1 handler)

Multi-way branch. Most complex branching handler.

**Total Wave 6: 10 handlers**

## Phase 7: Function Call Machinery (Hardest, needs careful sequencing)

These modify 4-6 state fields, have complex control flow, and interact with closures:

- `APPLY, APPLY1, APPLY2, APPLY3` -- function application
- `APPTERM, APPTERM1, APPTERM2, APPTERM3` -- tail calls
- `RETURN` -- frame restoration with conditional tail call
- `RESTART` -- partial application restart
- `GRAB` -- argument collection (most complex single handler)
- `CLOSURE, CLOSUREREC` -- heap allocation for closures
- `PUSHTRAP, POPTRAP` -- exception frame management
- `C_CALL` -- foreign function interface
- `PUSH_RETADDR` -- return address setup
- `OFFSETCLOSURE, PUSHOFFSETCLOSURE` -- closure offset access
- `ENVACC1-4, PUSHENVACC1-4` -- environment access (if in scope)

**Total Wave 7: ~15-20 handlers**

## Execution Strategy

### Agent Architecture

```
                    +-------------------+
                    |   You (PM)        |
                    | Coordinates all   |
                    +--------+----------+
                             |
              +--------------+--------------+
              |              |              |
     +--------v------+  +---v--------+  +--v-----------+
     | Lemma Agent   |  | Template   |  | Build Agent  |
     | (Phase 0)     |  | Generator  |  | (Validation) |
     | Writes to     |  | Creates    |  | Runs dune    |
     | HandlerLemmas |  | proof      |  | build after  |
     +---------------+  | skeletons  |  | each wave    |
                        +-----+------+  +--------------+
                              |
            +-----------------+-----------------+
            |                 |                 |
     +------v------+  +------v------+  +-------v-----+
     | Proof Agent  |  | Proof Agent |  | Proof Agent |
     | (worktree)  |  | (worktree)  |  | (worktree)  |
     | ACC1        |  | CONST1      |  | SUBINT      |
     +-------------+  +-------------+  +-------------+
            ... up to 15 parallel agents per wave ...
```

### Workflow per wave

1. **You** identify the handlers for the wave and the lemmas they need
2. **Lemma Agent** adds any missing lemmas to HandlerLemmas.v, builds to verify
3. **You** launch N parallel **Proof Agents** (one per handler, in worktrees)
   - Each agent gets: the handler name, the existing proof to clone from, the specific deltas, and a reference to the lemmas
4. **Build Agent** merges worktree results and runs `dune build instruct-verification/`
5. **You** update InstructSpec.v axiom error predicates for proved handlers
6. Commit wave, proceed to next

### Parallelism budget

Claude Code can run ~8-12 agents concurrently in worktrees. Batch waves accordingly:
- Waves 1-4: 8 agents per batch, 2-3 batches per wave
- Waves 5-6: 6-8 agents per batch
- Wave 7: 2-4 agents per batch (complex, need more context per agent)

## Summary Table

| Phase | Handlers | Parallel agents | Blocking on | Est. new lemmas |
|-------|----------|----------------|-------------|-----------------|
| 0 | -- | 1 (lemma agent) | Nothing | ~40-50 |
| 1 | 15 | 15 | Phase 0 | 0 (all pre-built) |
| 2 | 12 | 12 | Phase 0 | 0 |
| 3 | 11 | 11 | Phase 0 | 0 |
| 4 | 15 | 15 | Phase 0 | 0 |
| 5 | 21 | 21 | Phase 0 | ~5 (heap) |
| 6 | 10 | 10 | Phase 5 lemmas | ~3 |
| 7 | ~15 | 2-4 | Phases 1-6 | ~10+ |
| **Total** | **~74** | | | **~60** |

## Critical Path

```
Phase 0 (lemmas) --> Phases 1,2,3,4 (parallel) --> Phase 5 --> Phase 6 --> Phase 7
```

Phases 1-4 can all run simultaneously once Phase 0 lands. That's 53 handlers in one parallel blast.

## Historical Context

This file supersedes the original phased plan (infrastructure-first, VST-based) written before any proofs existed. The proof methodology evolved to use direct CompCert Clight bigstep semantics via `eval_stmt_to_exec` + computational evaluator, which is simpler and more automatable than VST separation logic. The `abs_rel` abstraction relation maps C `interp_state` struct fields to Rocq `Machine.state` via CompCert memory model (8 fields: pc, accu, sp, env, extra_args, global_data, trap_sp + le binding).
