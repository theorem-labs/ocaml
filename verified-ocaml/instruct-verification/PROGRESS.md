# Handler Verification Progress

## RULES FOR AGENTS

```
!!! AXIOM IS FORBIDDEN. NEVER WRITE `Axiom` IN ANY FILE. !!!
!!! ADMITTED IS FORBIDDEN. NEVER WRITE `Admitted.` IN ANY FILE. !!!
!!! EVERY PROOF MUST END WITH `Qed.` !!!

If you cannot close a goal:
  - DO NOT use Admitted or Axiom as a workaround
  - Add a step_pre precondition instead (caller provides the fact)
  - Or add an invariant to abs_rel_with_ard (all handlers maintain it)
  - Ask for help if stuck

Memory safety:
  - NEVER use compute, vm_compute, native_compute, or cbn on large terms
  - Use coqc directly, NOT dune build (lock contention with parallel agents)
  - Safe tactics: exact, apply, eapply, rewrite, lia, destruct, split, exists
  - If compilation takes > 60s, your approach is wrong -- restructure

Before marking done:
  - File compiles with `coqc` (0 errors, 0 warnings about Axiom/Admitted)
  - grep -c "Admitted\|^Axiom" your_file.v returns 0
```

---

## Axiom Elimination Status

| Step | Task | Status | Agent | Notes |
|------|------|--------|-------|-------|
| 1a | Delete `store_succeeds_stack` (unused) | TODO | | HandlerLemmas.v |
| 1b | Delete `sp_ofs_ge_8` (redundant) | TODO | | HandlerLemmas.v, update ~12 PUSH files |
| 1c | Delete `sp_ofs_stack_representable` (redundant) | TODO | | HandlerLemmas.v, update ~12 PUSH files |
| 1d | Prove `store_succeeds_from_load` -> `store_succeeds_sb` | TODO | | HandlerLemmas.v, update 60 files |
| 1e | Prove `store_to_other_block` -> `store_to_sp_after_sb_store` | TODO | | HandlerLemmas.v, update 13 PUSH files |
| 2 | Create `ExternalCallSpecs.v` | TODO | | Definitions only |
| 3a | Delete MAKEBLOCK1 axioms 13-14 (trivially provable) | TODO | | Use existing lemmas |
| 3b | Refactor MAKEBLOCK1 step_pre to use heap_alloc_spec | TODO | | Deletes axioms 6-12, 15-16 |
| 3c | Close MAKEBLOCK1 Admitted (writable preservation) | TODO | | 2 admits -> Qed |
| 4 | Refactor SETGLOBAL step_pre, close Admitted | TODO | | caml_modify_spec, 2 admits -> Qed |
| 5a | Add `heap_block_well_formed` to abs_rel | TODO | | Update all 62 handler proofs |
| 5b | Eliminate VECTLENGTH axioms 17-22 | TODO | | Uses new invariant |

**Axiom count: 22 -> target 0**
**Admitted count: 2 -> target 0**

---

## Proved Handlers (62 / 151)

All files end with `Qed.` and have no `Axiom` declarations (except via
imports of HandlerLemmas.v which still has 5 axioms pending elimination).

| # | Handler | File | Qed | Axiom-free | Notes |
|---|---------|------|-----|------------|-------|
| 1 | ACC0 | ACC0_correct.v | YES | pending HL | |
| 2 | ACC1 | ACC1_correct.v | YES | pending HL | |
| 3 | ACC2 | ACC2_correct.v | YES | pending HL | |
| 4 | ACC3 | ACC3_correct.v | YES | pending HL | |
| 5 | ACC4 | ACC4_correct.v | YES | pending HL | |
| 6 | ACC5 | ACC5_correct.v | YES | pending HL | |
| 7 | ACC6 | ACC6_correct.v | YES | pending HL | |
| 8 | ACC7 | ACC7_correct.v | YES | pending HL | |
| 9 | ADDINT | ADDINT_correct.v | YES | pending HL | |
| 10 | ANDINT | ANDINT_correct.v | YES | pending HL | |
| 11 | ASRINT | ASRINT_correct.v | YES | pending HL | |
| 12 | ASSIGN | ASSIGN_correct.v | YES | pending HL | |
| 13 | ATOM | ATOM_correct.v | YES | pending HL | |
| 14 | BOOLNOT | BOOLNOT_correct.v | YES | pending HL | |
| 15 | BRANCH | BRANCH_correct.v | YES | pending HL | |
| 16 | BRANCHIF | BRANCHIF_correct.v | YES | pending HL | |
| 17 | BRANCHIFNOT | BRANCHIFNOT_correct.v | YES | pending HL | |
| 18 | CHECK_SIGNALS | CHECK_SIGNALS_correct.v | YES | pending HL | |
| 19 | CONST0 | CONST0_correct.v | YES | pending HL | |
| 20 | CONST1 | CONST1_correct.v | YES | pending HL | |
| 21 | CONST2 | CONST2_correct.v | YES | pending HL | |
| 22 | CONST3 | CONST3_correct.v | YES | pending HL | |
| 23 | CONSTINT | CONSTINT_correct.v | YES | pending HL | |
| 24 | DIVINT | DIVINT_correct.v | YES | pending HL | |
| 25 | EQ | EQ_correct.v | YES | pending HL | |
| 26 | GEINT | GEINT_correct.v | YES | pending HL | |
| 27 | GETFIELD0 | GETFIELD0_correct.v | YES | pending HL | |
| 28 | GETGLOBAL | GETGLOBAL_correct.v | YES | pending HL | |
| 29 | GTINT | GTINT_correct.v | YES | pending HL | |
| 30 | ISINT | ISINT_correct.v | YES | pending HL | |
| 31 | LEINT | LEINT_correct.v | YES | pending HL | |
| 32 | LSLINT | LSLINT_correct.v | YES | pending HL | |
| 33 | LSRINT | LSRINT_correct.v | YES | pending HL | |
| 34 | LTINT | LTINT_correct.v | YES | pending HL | |
| 35 | MAKEBLOCK1 | MAKEBLOCK1_correct.v | ADMITTED | has 11 axioms | 2 admits, 11 local axioms |
| 36 | MODINT | MODINT_correct.v | YES | pending HL | |
| 37 | MULINT | MULINT_correct.v | YES | pending HL | |
| 38 | NEGINT | NEGINT_correct.v | YES | pending HL | |
| 39 | NEQ | NEQ_correct.v | YES | pending HL | |
| 40 | OFFSETINT | OFFSETINT_correct.v | YES | pending HL | |
| 41 | ORINT | ORINT_correct.v | YES | pending HL | |
| 42 | POP | POP_correct.v | YES | pending HL | |
| 43 | PUSH | PUSH_correct.v | YES | pending HL | |
| 44 | PUSHACC1 | PUSHACC1_correct.v | YES | pending HL | |
| 45 | PUSHACC2 | PUSHACC2_correct.v | YES | pending HL | |
| 46 | PUSHACC3 | PUSHACC3_correct.v | YES | pending HL | |
| 47 | PUSHACC4 | PUSHACC4_correct.v | YES | pending HL | |
| 48 | PUSHACC5 | PUSHACC5_correct.v | YES | pending HL | |
| 49 | PUSHACC6 | PUSHACC6_correct.v | YES | pending HL | |
| 50 | PUSHACC7 | PUSHACC7_correct.v | YES | pending HL | |
| 51 | PUSHCONST0 | PUSHCONST0_correct.v | YES | pending HL | |
| 52 | PUSHCONST1 | PUSHCONST1_correct.v | YES | pending HL | |
| 53 | PUSHCONST2 | PUSHCONST2_correct.v | YES | pending HL | |
| 54 | PUSHCONST3 | PUSHCONST3_correct.v | YES | pending HL | |
| 55 | PUSHCONSTINT | PUSHCONSTINT_correct.v | YES | pending HL | |
| 56 | SETGLOBAL | SETGLOBAL_correct.v | ADMITTED | no local axioms | 2 admits in proof |
| 57 | STOP | STOP_correct.v | YES | pending HL | |
| 58 | SUBINT | SUBINT_correct.v | YES | pending HL | |
| 59 | UGEINT | UGEINT_correct.v | YES | pending HL | |
| 60 | ULTINT | ULTINT_correct.v | YES | pending HL | |
| 61 | VECTLENGTH | VECTLENGTH_correct.v | YES | has 6 axioms | 6 local axioms |
| 62 | XORINT | XORINT_correct.v | YES | pending HL | |

**"pending HL"** = no local axioms, but imports HandlerLemmas.v which has 5 axioms.
Once Step 1 completes, all "pending HL" become fully axiom-free.

---

## Missing Handlers (89 / 151)

Status codes: `TODO` = not started, `WIP` = agent working, `DONE` = Qed + axiom-free, `BLOCKED` = waiting on infrastructure

### Wave 1: No-ops / Stubs (6 handlers)

| Handler | Diff | Template | Status | Agent | Notes |
|---------|------|----------|--------|-------|-------|
| EVENT | 1 | CHECK_SIGNALS | TODO | | `return 0` |
| BREAK | 1 | CHECK_SIGNALS | TODO | | `return 0` |
| PERFORM | 1 | CHECK_SIGNALS | TODO | | stub |
| RESUME | 1 | CHECK_SIGNALS | TODO | | stub |
| RESUMETERM | 2 | BRANCH | TODO | | `pc += 1; return 0` |
| REPERFORMTERM | 2 | BRANCH | TODO | | `pc += 1; return 0` |

### Wave 2: Template Clones (17 handlers)

| Handler | Diff | Template | Status | Agent | Infra needed |
|---------|------|----------|--------|-------|-------------|
| GETFIELD1 | 2 | GETFIELD0 | TODO | | HW |
| GETFIELD2 | 2 | GETFIELD0 | TODO | | HW |
| GETFIELD3 | 2 | GETFIELD0 | TODO | | HW |
| C_CALL1 | 2 | BRANCH | TODO | | none |
| C_CALL2 | 2 | C_CALL1 | TODO | | none |
| C_CALL3 | 2 | C_CALL1 | TODO | | none |
| C_CALL4 | 2 | C_CALL1 | TODO | | none |
| C_CALL5 | 2 | C_CALL1 | TODO | | none |
| ATOM0 | 2 | ATOM | TODO | | HW |
| SETFIELD0 | 3 | ADDINT+GETFIELD0 | TODO | | HW, WP |
| SETFIELD1 | 3 | SETFIELD0 | TODO | | HW, WP |
| SETFIELD2 | 3 | SETFIELD0 | TODO | | HW, WP |
| SETFIELD3 | 3 | SETFIELD0 | TODO | | HW, WP |
| OFFSETCLOSURE0 | 2 | ACC0 | TODO | | CL |
| MAKEBLOCK2 | 4 | MAKEBLOCK1 | TODO | | HA, EF, HW, WP |
| MAKEBLOCK3 | 4 | MAKEBLOCK1 | TODO | | HA, EF, HW, WP |

### Wave 3: Medium Difficulty (27 handlers)

| Handler | Diff | Template | Status | Agent | Infra needed |
|---------|------|----------|--------|-------|-------------|
| ENVACC1 | 2 | ACC0 | TODO | | HW |
| ENVACC2 | 2 | ENVACC1 | TODO | | HW |
| ENVACC3 | 2 | ENVACC1 | TODO | | HW |
| ENVACC4 | 2 | ENVACC1 | TODO | | HW |
| PUSHENVACC1 | 3 | PUSHACC1+ENVACC1 | TODO | | HW, WP |
| PUSHENVACC2 | 3 | PUSHENVACC1 | TODO | | HW, WP |
| PUSHENVACC3 | 3 | PUSHENVACC1 | TODO | | HW, WP |
| PUSHENVACC4 | 3 | PUSHENVACC1 | TODO | | HW, WP |
| BEQ | 3 | BRANCHIF | TODO | | CB |
| BNEQ | 3 | BEQ | TODO | | CB |
| BLTINT | 3 | BEQ | TODO | | CB |
| BLEINT | 3 | BEQ | TODO | | CB |
| BGTINT | 3 | BEQ | TODO | | CB |
| BGEINT | 3 | BEQ | TODO | | CB |
| BULTINT | 4 | BEQ | TODO | | CB |
| BUGEINT | 4 | BEQ | TODO | | CB |
| OFFSETCLOSURE2 | 3 | OFFSETCLOSURE0 | TODO | | CL |
| OFFSETCLOSUREM2 | 3 | OFFSETCLOSURE2 | TODO | | CL |
| PUSHOFFSETCLOSURE0 | 3 | PUSHACC1+OFFSETCLOSURE0 | TODO | | CL, WP |
| PUSHOFFSETCLOSURE2 | 3 | PUSHOFFSETCLOSURE0 | TODO | | CL, WP |
| PUSHATOM0 | 3 | PUSHCONST0+ATOM0 | TODO | | HW |
| PUSHATOM | 3 | PUSHATOM0+ATOM | TODO | | HW, CB |
| PUSHGETGLOBAL | 3 | PUSHCONSTINT+GETGLOBAL | TODO | | CB |
| ACC | 3 | ACC0+CONSTINT | TODO | | CB |
| C_CALLN | 3 | C_CALL1+CONSTINT | TODO | | CB |
| ENVACC | 3 | ENVACC1+CONSTINT | TODO | | HW, CB |
| PUSHENVACC | 3 | PUSHENVACC1+CONSTINT | TODO | | HW, CB, WP |

### Wave 4: Hard (18 handlers)

| Handler | Diff | Template | Status | Agent | Infra needed |
|---------|------|----------|--------|-------|-------------|
| GETFIELD | 3 | GETFIELD0+CONSTINT | TODO | | HW, CB |
| GETFLOATFIELD | 3 | GETFIELD | TODO | | HW, CB |
| GETGLOBALFIELD | 3 | GETGLOBAL+GETFIELD0 | TODO | | HW, CB |
| OFFSETCLOSURE | 3 | OFFSETCLOSURE2+CONSTINT | TODO | | CL, CB |
| PUSHOFFSETCLOSUREM2 | 3 | PUSHOFFSETCLOSURE0 | TODO | | CL, WP |
| PUSHOFFSETCLOSURE | 4 | PUSHOFFSETCLOSURE0+CONSTINT | TODO | | CL, CB, WP |
| OFFSETREF | 4 | SETFIELD0+OFFSETINT | TODO | | HW |
| GETSTRINGCHAR | 4 | GETVECTITEM | TODO | | HW |
| GETBYTESCHAR | 4 | GETSTRINGCHAR | TODO | | HW |
| GETVECTITEM | 4 | GETFIELD0+ADDINT | TODO | | HW |
| PUSHGETGLOBALFIELD | 4 | PUSHGETGLOBAL+GETGLOBALFIELD | TODO | | HW, CB, WP |
| PUSH_RETADDR | 4 | PUSHTRAP | TODO | | CB, WP |
| PUSHTRAP | 4 | PUSH_RETADDR | TODO | | TF, CB, WP |
| POPTRAP | 4 | POP | TODO | | TF |
| RETURN | 4 | BRANCHIF+POP | TODO | | CL, CB |
| APPLY | 3 | BRANCH+CONSTINT | TODO | | CL, CB |
| APPLY1 | 4 | PUSH_RETADDR+APPLY | TODO | | CL, WP |
| SETFIELD | 4 | SETGLOBAL+SETFIELD0 | TODO | | CM, EF, HW, WP |

### Wave 5: Very Hard (14 handlers)

| Handler | Diff | Template | Status | Agent | Infra needed |
|---------|------|----------|--------|-------|-------------|
| SETFLOATFIELD | 5 | SETFIELD | TODO | | CM, EF, WP |
| SETVECTITEM | 5 | SETFIELD+GETVECTITEM | TODO | | CM, EF, HW, WP |
| SETBYTESCHAR | 5 | SETVECTITEM | TODO | | CM, EF, WP |
| APPLY2 | 4 | APPLY1 | TODO | | CL, WP |
| APPLY3 | 5 | APPLY1 | TODO | | CL, WP |
| APPTERM1 | 4 | APPLY1 | TODO | | CL |
| APPTERM2 | 5 | APPTERM1 | TODO | | CL |
| APPTERM3 | 5 | APPTERM1 | TODO | | CL |
| RAISE | 5 | POPTRAP | TODO | | TF |
| RERAISE | 5 | RAISE | TODO | | TF |
| RAISE_NOTRACE | 5 | RAISE | TODO | | TF |

### Wave 6: Most Complex (11 handlers)

| Handler | Diff | Template | Status | Agent | Infra needed |
|---------|------|----------|--------|-------|-------------|
| APPTERM | 5 | APPTERM1 | TODO | | CL |
| RESTART | 5 | RETURN | TODO | | CL |
| GRAB | 5 | RETURN | TODO | | CL, HA, EF |
| CLOSURE | 5 | MAKEBLOCK1+PUSH_RETADDR | TODO | | HA, EF, CL, WP |
| CLOSUREREC | 5 | CLOSURE | TODO | | HA, EF, CL, WP |
| MAKEBLOCK | 5 | MAKEBLOCK1 | TODO | | HA, EF, HW, WP |
| MAKEFLOATBLOCK | 5 | MAKEBLOCK | TODO | | HA, EF, HW, WP |
| SWITCH | 5 | BRANCHIF | TODO | | CB |
| GETMETHOD | 5 | GETFIELD0 | TODO | | HW |
| GETPUBMET | 5 | GETMETHOD | TODO | | HW, CB |
| GETDYNMET | 5 | GETPUBMET | TODO | | HW |

---

## Infrastructure Status

| Item | Status | Notes |
|------|--------|-------|
| ExternalCallSpecs.v | TODO | heap_alloc_spec, caml_modify_spec, ext_func_findable |
| BranchLemmas.v | TODO | For BEQ..BUGEINT |
| ClosureLemmas.v | TODO | For APPLY, APPTERM, OFFSETCLOSURE, GRAB, CLOSURE |
| ExceptionLemmas.v | TODO | For PUSHTRAP, POPTRAP, RAISE |
| `store_succeeds_sb` lemma | TODO | Replaces axiom 1 in HandlerLemmas.v |
| `store_to_sp_after_sb_store` lemma | TODO | Replaces axiom 2 in HandlerLemmas.v |
| `code_buffer_load_at` lemma | TODO | Extract from existing proofs |
| `heap_block_well_formed` invariant | TODO | Add to abs_rel_with_ard |
| `closure_code_loadable` definition | TODO | For step_pre |
| `trap_frame_well_formed` definition | TODO | For abs_rel_with_ard |

---

## Infra Key

| Code | Meaning |
|------|---------|
| HW | `heap_block_well_formed` in abs_rel |
| HA | `heap_alloc_spec` in step_pre |
| CM | `caml_modify_spec` in step_pre |
| CL | `closure_code_loadable` in step_pre |
| TF | `trap_frame_well_formed` in abs_rel |
| CB | `code_buffer_load_at` lemma |
| EF | `ext_func_findable` in step_pre |
| WP | writable preservation pattern |

---

## Summary

| Category | Done | Total | % |
|----------|------|-------|---|
| Proved (Qed) | 60 | 151 | 40% |
| Proved (Admitted) | 2 | 0 target | |
| Axioms | 22 | 0 target | |
| Missing handlers | 0 | 89 | 0% |
