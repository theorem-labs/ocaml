# HandlerLemmas Axiom Elimination — Progress Tracker

See `HandlerLemmas-plan.md` for full instructions.
See `HandlerLemmas-analysis.md` for axiom analysis.

Last updated: 2026-04-01 (Phase 0 COMPLETE — clean build)

---

## Stage 1: Shared-file edits (Agent 1 only)

| Step | File | Description | Status | Agent | Notes |
|------|------|-------------|--------|-------|-------|
| 0.1 | InstructSpec.v | Extract `abs_rel_with_ard` as separate Definition | DONE | 1 | kept as Definition (not Record) to preserve `let` bindings for `cbn` |
| 0.2 | InstructSpec.v | Define `abs_rel` as wrapper | DONE | 1 | `exists ard, abs_rel_with_ard e le m s ard` |
| 0.3 | InstructSpec.v | Handle `abs_rel_pre` | SKIP | 1 | not used in handlers, left as-is |
| 0.4 | InstructSpec.v | Fix `abs_rel_iff_with_ard` | DONE | 1 | `unfold abs_rel, abs_rel_with_ard. reflexivity.` |
| 0.8 | InstructSpec.v | Unify: single `handler_correct` with `step_pre` arg | DONE | 1 | Module Type commented out; deleted `_with_pre` and `_with_pre_env` |
| 0.9 | 56 handler files | Update for unified `handler_correct` | DONE | 1 | add step_pre arg, change intro pattern, add `unfold abs_rel_with_ard in Hpre` |
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

Phase 0 changes per file (COMPLETED for all 56 handler files + 2 custom):
- Unified handler_correct: add `step_pre` arg, fix intro pattern
- Add `unfold abs_rel_with_ard in Hpre.` (needed because `abs_rel` now wraps `abs_rel_with_ard`)
- For `handler_correct_with_pre` users: rename + wrap step_pre with env param
- For `handler_correct_with_pre_env` users: rename only
- `abs_rel_with_ard` kept as Definition (NOT Record) — `cbn` needs `let` bindings

Remaining per-file changes:
- (P2) Delete `sp_block_ne_sptr`/`sp_block_ne_global` callers
- (P3+6) Extend sp destruct, add new constructor blocks

Status key: TODO | IN_PROGRESS | DONE | ERROR | SKIP

### Agent 1 — Complex handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| MAKEBLOCK1_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| SETGLOBAL_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | pre_env+mk_abs_rel |
| ASSIGN_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| ISINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | custom statement |

### Agent 2 — mk_abs_rel handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| PUSHCONSTINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| GETGLOBAL_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| OFFSETINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| POP_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| CONSTINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |

### Agent 3 — Mixed handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| BOOLNOT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | custom statement |
| VECTLENGTH_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| ATOM_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| ASRINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| ADDINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| NEGINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| BRANCH_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre+mk_abs_rel |
| GETFIELD0_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |

### Agent 4 — Comparisons + shifts + medium

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| UGEINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| LSRINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| LSLINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| PUSH_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple, stack-mod |
| ACC0_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC2_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ULTINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| MULINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| SUBINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| NEQ_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| EQ_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| GTINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |

### Agent 5 — Simple handlers

| File | P0-destruct | P0-reconstr | P0-unify | P2-axioms | P3+6-new | Status | Notes |
|------|-------------|-------------|----------|-----------|----------|--------|-------|
| GEINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| LTINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| LEINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | with_pre |
| PUSHACC7_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC6_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC5_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC4_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC3_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC2_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHACC1_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHCONST3_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHCONST2_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHCONST1_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| PUSHCONST0_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| CONST0_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| CONST1_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| CONST2_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| CONST3_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ANDINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ORINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| XORINT_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC1_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC3_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC4_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC5_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC6_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| ACC7_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| CHECK_SIGNALS_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |
| STOP_correct.v | DONE | DONE | DONE | TODO | TODO | DONE | simple |

---

## Stage 3: Build verification

| Check | Status | Notes |
|-------|--------|-------|
| `dune build instruct-verification` (Phase 0) | DONE | clean build on 2026-04-01 |
| Fix dispatched errors | DONE | CONST0 comment-insertion bug, `unfold abs_rel_with_ard in Hpre` needed everywhere |
| Final clean build (Phase 0) | DONE | all 58 handler files compile |
| Axiom audit: `Print Assumptions` on key theorems | DONE | remaining axioms: store_succeeds_from_load, sp_block_ne_sptr, global_block_ne_sptr (Phase 1-6 work) |

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
