# HandlerLemmas Axiom Elimination — Progress Tracker

See `HandlerLemmas-plan.md` for full instructions.
See `HandlerLemmas-analysis.md` for axiom analysis.

Last updated: 2026-04-01

---

## Stage 1: Shared-file edits (Agent 1 only)

| Step | File | Description | Status | Agent | Notes |
|------|------|-------------|--------|-------|-------|
| 0.1 | InstructSpec.v | Record: define `abs_rel_with_ard` as Record | TODO | 1 | |
| 0.2 | InstructSpec.v | Record: update `abs_rel` wrapper | TODO | 1 | |
| 0.3 | InstructSpec.v | Record: handle `abs_rel_pre` | TODO | 1 | may defer |
| 0.4 | InstructSpec.v | Record: fix `abs_rel_iff_with_ard` | TODO | 1 | |
| 0.8 | InstructSpec.v | Unify: single `handler_correct` definition | TODO | 1 | delete `_with_pre`, `_with_pre_env` |
| 1.1 | InstructSpec.v | Add `ar_global_ne_sptr` to `abs_rel_data` | TODO | 1 | |
| 1.3 | HandlerLemmas.v | Replace `global_block_ne_sptr` axiom with lemma | TODO | 1 | |
| 2.1 | HandlerLemmas.v | Delete `sp_block_ne_sptr`, `sp_block_ne_global` axioms | TODO | 1 | |
| 3.1 | InstructSpec.v | Add new abs_rel conjuncts (sp_ge8, repr, writable) | TODO | 1 | |
| 4.1 | HandlerLemmas.v | Prove `store_succeeds_from_load` | TODO | 1 | |
| 4.2 | HandlerLemmas.v | Prove `store_to_other_block` | TODO | 1 | |
| 4.3 | HandlerLemmas.v | Prove `store_succeeds_stack` | TODO | 1 | |
| 4.4 | HandlerLemmas.v | Prove/delete `sp_ofs_ge_8`, `sp_ofs_stack_representable` | TODO | 1 | |
| 5.1 | HandlerLemmas.v | Prove `stack_repr_store_same_block_lower` | TODO | 1 | |
| 5.2 | HandlerLemmas.v | Prove `stack_repr_cons_after_store` | TODO | 1 | |

---

## Stage 2: Per-handler-file edits (Agents 1-5 in parallel)

Each file needs these changes (all in one pass):
- (P0) Record destruct: `( & )` → `[ ]`, delete `unfold abs_rel_with_ard`
- (P0) Record reconstruct: `split; [| split; ...]` → `constructor.`
- (P0) Unified handler_correct: add `step_pre` arg, fix intro pattern
- (P2) Delete `sp_block_ne_sptr`/`sp_block_ne_global` callers
- (P3+6) Extend sp destruct, add new constructor blocks

Status key: TODO | IN_PROGRESS | DONE | ERROR | SKIP

### Agent 1 — Complex handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| MAKEBLOCK1_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| SETGLOBAL_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | pre_env+mk_abs_rel |
| ASSIGN_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| ISINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | custom statement |

### Agent 2 — mk_abs_rel handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| PUSHCONSTINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| GETGLOBAL_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| OFFSETINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| POP_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| CONSTINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |

### Agent 3 — Mixed handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| BOOLNOT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | custom statement |
| VECTLENGTH_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| ATOM_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| ASRINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| ADDINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| NEGINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| BRANCH_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre+mk_abs_rel |
| GETFIELD0_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |

### Agent 4 — Comparisons + shifts + medium

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| UGEINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| LSRINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| LSLINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| PUSH_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple, stack-mod |
| ACC0_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC2_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ULTINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| MULINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| SUBINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| NEQ_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| EQ_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| GTINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |

### Agent 5 — Simple handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| GEINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| LTINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| LEINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | with_pre |
| PUSHACC7_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC6_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC5_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC4_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC3_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC2_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHACC1_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHCONST3_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHCONST2_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHCONST1_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| PUSHCONST0_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| CONST0_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| CONST1_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| CONST2_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| CONST3_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ANDINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ORINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| XORINT_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC1_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC3_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC4_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC5_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC6_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| ACC7_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| CHECK_SIGNALS_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |
| STOP_correct.v | TODO | TODO | TODO | TODO | TODO | TODO | simple |

---

## Stage 3: Build verification

| Check | Status | Notes |
|-------|--------|-------|
| `dune build instruct-verification` | TODO | run after all Stage 2 agents complete |
| Fix dispatched errors | TODO | assign to owning agent |
| Final clean build | TODO | |
| Axiom audit: `Print Assumptions` on key theorems | TODO | verify no axioms remain |

---

## Axiom elimination scorecard

| Axiom | Status | Eliminated in | Notes |
|-------|--------|---------------|-------|
| `sp_block_ne_sptr` | TODO | Phase 2 | FALSE — delete, use `Hsp_ne_sb` |
| `sp_block_ne_global` | TODO | Phase 2 | FALSE — delete, use `Hsp_ne_gb` |
| `global_block_ne_sptr` | TODO | Phase 1 | add `ar_global_ne_sptr` record field |
| `store_succeeds_from_load` | TODO | Phase 4 | needs struct writability |
| `store_to_other_block` | TODO | Phase 4 | needs stack writability |
| `store_succeeds_stack` | TODO | Phase 4 | needs stack writability |
| `sp_ofs_ge_8` | TODO | Phase 4 | becomes direct hypothesis |
| `sp_ofs_stack_representable` | TODO | Phase 4 | becomes direct hypothesis |
| `stack_repr_store_same_block_lower` | TODO | Phase 5 | induction on stack_repr |
| `stack_repr_cons_after_store` | TODO | Phase 5 | uses previous lemma |

---

## Recovery instructions

If an agent crashes or a session is interrupted:

1. **Read this file** to see what is DONE vs TODO.
2. **Check git status** — uncommitted changes show what was in progress.
3. **Read the Notes column** for any file marked IN_PROGRESS — it may
   describe what was attempted and what failed.
4. **Resume from the first TODO** in the crashed agent's file list.
5. **Do not re-edit DONE files** unless the build (Stage 3) reveals errors.

When updating this file:
- Change status to IN_PROGRESS before starting a file.
- Change status to DONE only after all sub-columns are done for that file.
- If something fails, set status to ERROR and describe in Notes.
- Always update "Last updated" date at the top.
