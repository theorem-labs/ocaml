# Handler Verification Progress

## Summary (2026-04-02)

| Category | Count | Target | Notes |
|----------|-------|--------|-------|
| Clean (Qed, axiom-free) | 118 | 151 | 78% |
| Compile failures | 8 | 0 | See PLAN.md Phase 1 |
| Timeout/Admitted | 2 | 0 | GRAB, SWITCH -- see PLAN.md Phase 2 |
| Missing files | 23 | 0 | See PLAN.md Phases 3-5 |
| Total handler files | 128 | 151 | |
| Axioms remaining | 6 | 0 | All in VECTLENGTH (itself broken) |
| HandlerLemmas.v axioms | 0 | 0 | DONE |
| Not in _RocqProject | 15 | 0 | Add after files compile |

---

## Axiom Elimination Status

| Step | Task | Status |
|------|------|--------|
| 1a | Delete `store_succeeds_stack` (unused) | DONE |
| 1b | Delete `sp_ofs_ge_8` (redundant) | DONE |
| 1c | Delete `sp_ofs_stack_representable` (redundant) | DONE |
| 1d | Prove `store_succeeds_sb` | DONE |
| 1e | Prove `store_to_sp_after_sb_store` | DONE |
| 2 | Create ExternalCallSpecs.v | DONE |
| 3 | Refactor MAKEBLOCK1: 0 axiom, 0 Admitted | DONE |
| 4 | Refactor SETGLOBAL: 0 axiom, 0 Admitted | DONE |
| 5a | Add `heap_block_well_formed` to abs_rel | TODO |
| 5b | Eliminate VECTLENGTH 6 axioms | TODO |

---

## Clean Handlers (118)

All compile with `coqc`, end with `Qed.`, have no `Axiom` or `Admitted`.

| # | Handler | File |
|---|---------|------|
| 1 | ACC0 | ACC0_correct.v |
| 2 | ACC1 | ACC1_correct.v |
| 3 | ACC2 | ACC2_correct.v |
| 4 | ACC3 | ACC3_correct.v |
| 5 | ACC4 | ACC4_correct.v |
| 6 | ACC5 | ACC5_correct.v |
| 7 | ACC6 | ACC6_correct.v |
| 8 | ACC7 | ACC7_correct.v |
| 9 | ACC | ACC_correct.v |
| 10 | ADDINT | ADDINT_correct.v |
| 11 | ANDINT | ANDINT_correct.v |
| 12 | ASRINT | ASRINT_correct.v |
| 13 | ASSIGN | ASSIGN_correct.v |
| 14 | ATOM | ATOM_correct.v |
| 15 | ATOM0 | ATOM0_correct.v |
| 16 | BEQ | BEQ_correct.v |
| 17 | BGEINT | BGEINT_correct.v |
| 18 | BGTINT | BGTINT_correct.v |
| 19 | BNEQ | BNEQ_correct.v |
| 20 | BOOLNOT | BOOLNOT_correct.v |
| 21 | BRANCH | BRANCH_correct.v |
| 22 | BRANCHIF | BRANCHIF_correct.v |
| 23 | BRANCHIFNOT | BRANCHIFNOT_correct.v |
| 24 | BREAK | BREAK_correct.v |
| 25 | BUGEINT | BUGEINT_correct.v |
| 26 | BULTINT | BULTINT_correct.v |
| 27 | C_CALL1 | C_CALL1_correct.v |
| 28 | C_CALL2 | C_CALL2_correct.v |
| 29 | C_CALL3 | C_CALL3_correct.v |
| 30 | C_CALL4 | C_CALL4_correct.v |
| 31 | C_CALL5 | C_CALL5_correct.v |
| 32 | C_CALLN | C_CALLN_correct.v |
| 33 | CHECK_SIGNALS | CHECK_SIGNALS_correct.v |
| 34 | CONST0 | CONST0_correct.v |
| 35 | CONST1 | CONST1_correct.v |
| 36 | CONST2 | CONST2_correct.v |
| 37 | CONST3 | CONST3_correct.v |
| 38 | CONSTINT | CONSTINT_correct.v |
| 39 | DIVINT | DIVINT_correct.v |
| 40 | ENVACC | ENVACC_correct.v |
| 41 | ENVACC1 | ENVACC1_correct.v |
| 42 | ENVACC2 | ENVACC2_correct.v |
| 43 | ENVACC3 | ENVACC3_correct.v |
| 44 | ENVACC4 | ENVACC4_correct.v |
| 45 | EQ | EQ_correct.v |
| 46 | EVENT | EVENT_correct.v |
| 47 | GEINT | GEINT_correct.v |
| 48 | GETBYTESCHAR | GETBYTESCHAR_correct.v |
| 49 | GETFIELD | GETFIELD_correct.v |
| 50 | GETFIELD0 | GETFIELD0_correct.v |
| 51 | GETFIELD1 | GETFIELD1_correct.v |
| 52 | GETFIELD2 | GETFIELD2_correct.v |
| 53 | GETFIELD3 | GETFIELD3_correct.v |
| 54 | GETFLOATFIELD | GETFLOATFIELD_correct.v |
| 55 | GETGLOBAL | GETGLOBAL_correct.v |
| 56 | GETGLOBALFIELD | GETGLOBALFIELD_correct.v |
| 57 | GETMETHOD | GETMETHOD_correct.v |
| 58 | GETSTRINGCHAR | GETSTRINGCHAR_correct.v |
| 59 | GETVECTITEM | GETVECTITEM_correct.v |
| 60 | GTINT | GTINT_correct.v |
| 61 | ISINT | ISINT_correct.v |
| 62 | LEINT | LEINT_correct.v |
| 63 | LSLINT | LSLINT_correct.v |
| 64 | LSRINT | LSRINT_correct.v |
| 65 | LTINT | LTINT_correct.v |
| 66 | MAKEBLOCK1 | MAKEBLOCK1_correct.v |
| 67 | MODINT | MODINT_correct.v |
| 68 | MULINT | MULINT_correct.v |
| 69 | NEGINT | NEGINT_correct.v |
| 70 | NEQ | NEQ_correct.v |
| 71 | OFFSETCLOSURE | OFFSETCLOSURE_correct.v |
| 72 | OFFSETCLOSURE0 | OFFSETCLOSURE0_correct.v |
| 73 | OFFSETCLOSURE3 | OFFSETCLOSURE3_correct.v |
| 74 | OFFSETCLOSUREM3 | OFFSETCLOSUREM3_correct.v |
| 75 | OFFSETINT | OFFSETINT_correct.v |
| 76 | OFFSETREF | OFFSETREF_correct.v |
| 77 | ORINT | ORINT_correct.v |
| 78 | PERFORM | PERFORM_correct.v |
| 79 | POP | POP_correct.v |
| 80 | PUSH | PUSH_correct.v |
| 81 | PUSHACC1 | PUSHACC1_correct.v |
| 82 | PUSHACC2 | PUSHACC2_correct.v |
| 83 | PUSHACC3 | PUSHACC3_correct.v |
| 84 | PUSHACC4 | PUSHACC4_correct.v |
| 85 | PUSHACC5 | PUSHACC5_correct.v |
| 86 | PUSHACC6 | PUSHACC6_correct.v |
| 87 | PUSHACC7 | PUSHACC7_correct.v |
| 88 | PUSHATOM | PUSHATOM_correct.v |
| 89 | PUSHATOM0 | PUSHATOM0_correct.v |
| 90 | PUSHCONST0 | PUSHCONST0_correct.v |
| 91 | PUSHCONST1 | PUSHCONST1_correct.v |
| 92 | PUSHCONST2 | PUSHCONST2_correct.v |
| 93 | PUSHCONST3 | PUSHCONST3_correct.v |
| 94 | PUSHCONSTINT | PUSHCONSTINT_correct.v |
| 95 | PUSHENVACC | PUSHENVACC_correct.v |
| 96 | PUSHENVACC1 | PUSHENVACC1_correct.v |
| 97 | PUSHENVACC2 | PUSHENVACC2_correct.v |
| 98 | PUSHENVACC3 | PUSHENVACC3_correct.v |
| 99 | PUSHENVACC4 | PUSHENVACC4_correct.v |
| 100 | PUSHGETGLOBAL | PUSHGETGLOBAL_correct.v |
| 101 | PUSHGETGLOBALFIELD | PUSHGETGLOBALFIELD_correct.v |
| 102 | PUSHOFFSETCLOSURE | PUSHOFFSETCLOSURE_correct.v |
| 103 | PUSHOFFSETCLOSURE0 | PUSHOFFSETCLOSURE0_correct.v |
| 104 | PUSHOFFSETCLOSURE3 | PUSHOFFSETCLOSURE3_correct.v |
| 105 | PUSHOFFSETCLOSUREM3 | PUSHOFFSETCLOSUREM3_correct.v |
| 106 | REPERFORMTERM | REPERFORMTERM_correct.v |
| 107 | RESUME | RESUME_correct.v |
| 108 | RESUMETERM | RESUMETERM_correct.v |
| 109 | SETFIELD0 | SETFIELD0_correct.v |
| 110 | SETFIELD1 | SETFIELD1_correct.v |
| 111 | SETFIELD2 | SETFIELD2_correct.v |
| 112 | SETFIELD3 | SETFIELD3_correct.v |
| 113 | SETGLOBAL | SETGLOBAL_correct.v |
| 114 | STOP | STOP_correct.v |
| 115 | SUBINT | SUBINT_correct.v |
| 116 | UGEINT | UGEINT_correct.v |
| 117 | ULTINT | ULTINT_correct.v |
| 118 | XORINT | XORINT_correct.v |

---

## Broken Handlers (10)

### Compile Failures (8)

| Handler | File | Line | Error | PLAN Phase |
|---------|------|------|-------|------------|
| APPLY | APPLY_correct.v | 334 | No subterm `Mem.store ... so + 32` | 1A |
| APPTERM1 | APPTERM1_correct.v | 338 | Ptrofs.neg arithmetic | 1B |
| CLOSURE | CLOSURE_correct.v | 192 | Oor Vlong/Vint mismatch | 1A |
| GETDYNMET | GETDYNMET_correct.v | 181 | Machine.set_accu not found | 1A |
| MAKEBLOCK2 | MAKEBLOCK2_correct.v | 1355 | stack_repr undischarged premises | 1B |
| POPTRAP | POPTRAP_correct.v | 363 | PTree.set subterm not found | 1A |
| SETVECTITEM | SETVECTITEM_correct.v | 89 | Cannot find witness | 1B |
| VECTLENGTH | VECTLENGTH_correct.v | 365 | store_succeeds_from_load not found | 1A |

### Timeout/Admitted (2)

| Handler | File | Admitted at | Root Cause | PLAN Phase |
|---------|------|------------|------------|------------|
| GRAB | GRAB_correct.v | 617 | eval_cbn timeout (~40 C stmts) | 2 |
| SWITCH | SWITCH_correct.v | 738 | eval_cbn timeout (~50 C stmts) | 2 |

---

## Missing Handlers (23)

| Handler | Difficulty | Template | PLAN Phase |
|---------|-----------|----------|------------|
| BLTINT | Easy | BEQ_correct.v | 3 |
| BLEINT | Easy | BEQ_correct.v | 3 |
| MAKEBLOCK3 | Easy | MAKEBLOCK1_correct.v | 3 |
| SETBYTESCHAR | Easy | GETSTRINGCHAR_correct.v | 3 |
| RETURN | Medium | STOP + POP | 4A |
| APPLY1 | Medium | APPLY (after fix) | 4A |
| APPLY2 | Medium | APPLY (after fix) | 4A |
| APPLY3 | Medium | APPLY (after fix) | 4A |
| PUSH_RETADDR | Medium | PUSH | 4A |
| APPTERM | Medium | APPTERM1 (after fix) | 4B |
| APPTERM2 | Medium | APPTERM1 (after fix) | 4B |
| APPTERM3 | Medium | APPTERM1 (after fix) | 4B |
| RESTART | Medium | GRAB (after fix) | 4B |
| CLOSUREREC | Medium | CLOSURE (after fix) | 4B |
| SETFLOATFIELD | Medium | GETFLOATFIELD | 4C |
| GETPUBMET | Medium | GETMETHOD | 4C |
| MAKEBLOCK (param) | Medium | MAKEBLOCK1 | 4C |
| PUSHTRAP | Hard | PUSH_RETADDR (from 4A) | 5A |
| RAISE | Hard | POPTRAP (after fix) | 5A |
| SETFIELD (param) | Hard | SETFIELD0 + SETGLOBAL | 5A |
| RERAISE | Hard | RAISE (from 5A) | 5B |
| RAISE_NOTRACE | Hard | RAISE (from 5A) | 5B |
| MAKEFLOATBLOCK | Hard | MAKEBLOCK1 | 5B |

---

## Files Not in _RocqProject (15)

Add to `theories/_RocqProject` once file compiles clean.

### Clean (add now)

BNEQ, DIVINT, GETMETHOD, MAKEBLOCK1, MODINT, SETGLOBAL

### Broken (add after Phase 1 fix)

APPLY, APPTERM1, GETDYNMET, MAKEBLOCK2, POPTRAP, SETVECTITEM, VECTLENGTH

### Admitted (add after Phase 2 fix)

GRAB, SWITCH

---

## Infrastructure Status

| Item | Status |
|------|--------|
| HandlerLemmas.v axioms | DONE (0) |
| ExternalCallSpecs.v | DONE |
| store_succeeds_sb | DONE |
| store_to_sp_after_sb_store | DONE |
| sp_ofs_aligned | DONE |
| sb_writable_after_store | DONE |
| abs_rel alignment field | DONE |
| heap_block_well_formed | TODO (Phase 6A) |
| closure_code_loadable | TODO |
| trap_frame_well_formed | TODO |
