# Per-Instruction MetaSpec Proof Plan

## Goal

For each of the 94 instruction Parameters in the new `MetaSpecFineGrainedSpec`,
fix/write the proof in `automatic/Bytecode/MetaSpecVerification/${INSTR}_unique.v`
so that the corresponding case in `automatic/Bytecode/MetaSpecProof.v` is no longer
`Admitted`, and `checker/Bytecode/MetaSpecChecker.v` no longer depends on an axiom
for that instruction.

## What we're proving

The MetaSpec theorem says: for any instruction `i`, any two handlers `h1` and `h2`
that both satisfy `handler_correct` for `i` produce `em_eq` results on every state.

`em_eq` means: same `Step` post-state, same `Halt` value, same `CCall_request`, or
both are `Error` (possibly with different messages).

Per instruction, the statement is:
```coq
Parameter unique_INSTR : forall <args>,
  forall (h1 h2 : Z -> state -> step_result),
    handler_correct h1 (clight_of (INSTR <args>))
      (pre_of (INSTR <args>)) (P_error_of (INSTR <args>))
      (P_halt_of (INSTR <args>)) (P_ccall_of (INSTR <args>)) ->
    handler_correct h2 (clight_of (INSTR <args>))
      (pre_of (INSTR <args>)) (P_error_of (INSTR <args>))
      (P_halt_of (INSTR <args>)) (P_ccall_of (INSTR <args>)) ->
    forall s, em_eq (h1 s.(pc) s) (h2 s.(pc) s).
```

## Proof strategy

For each instruction, the proof likely proceeds:
1. Unfold `handler_correct` for both `h1` and `h2`.
2. Fix `e`, `le`, `m`, `s` and specialize both hypotheses.
3. Case-split on `h1 s.(pc) s` and `h2 s.(pc) s` (4x4 = 16 cases).
4. Matching cases (both Step, both Error, etc.) are easy.
5. Cross cases (one Step, one Error) require showing contradiction:
   - If h1 returns Step: under abs_rel, there's a Clight execution
   - If h2 returns Error: P_error_of holds (error_message_of = Some msg)
   - Show these are contradictory for the specific instruction
6. For STOP (Halt case) and C_CALL (CCall case), similar reasoning.

**Key difficulty**: showing that two correct handlers can't disagree on whether
the result is Step vs Error. This depends on the determinacy of Clight semantics
and the relationship between error_message_of and the handler's error conditions.

If proving contradiction is hard, an alternative weaker approach: admit the cross
cases and leave a comment explaining what additional lemma is needed.

## Infrastructure (created by initial subagent)

Files in `manual/Bytecode/Interpret/MetaSpec.v`:
- `Module Type MetaSpecFineGrainedSpec` — 94 Parameters, one per instruction
- `Module MetaSpecFromFineGrained (FG : MetaSpecFineGrainedSpec) <: MetaSpec`

Files in `automatic/Bytecode/MetaSpecProof.v`:
- Rewritten to import per-instruction files, 94 Admitted stubs

Files in `automatic/Bytecode/MetaSpecVerification/`:
- One `${INSTR}_unique.v` per instruction (94 stub files)

Files in `checker/Bytecode/MetaSpecChecker.v`:
- Updated to use fine-grained ascription + Print Assumptions per instruction

`_CoqProject` updated to list all new files.

## Approach per instruction subagent

Each subagent (one per instruction, launched in batches):

1. `git pull origin main` to get latest.
2. Read the Parameter type from `MetaSpec.v` for `unique_${INSTR}`.
3. Read/fix `automatic/Bytecode/MetaSpecVerification/${INSTR}_unique.v`.
4. Write the proof. Consult completed proofs in the same directory for guidance.
5. Update `MetaSpecProof.v`: import and replace Admitted with a reference.
6. Build test:
   ```
   make -f Makefile.coq ROCQ="timeout 30s rocq" COQC="timeout 30s coqc" \
     automatic/Bytecode/MetaSpecVerification/${INSTR}_unique.vo
   make -f Makefile.coq ROCQ="timeout 30s rocq" COQC="timeout 30s coqc" \
     automatic/Bytecode/MetaSpecProof.vo
   make -f Makefile.coq ROCQ="timeout 30s rocq" COQC="timeout 30s coqc" \
     checker/Bytecode/MetaSpecChecker.vo
   ```
7. **Constraint**: subagents MUST NOT modify files outside `automatic/`.
   If blocked, create a `.md` bug report alongside the spec in `manual/`,
   leave the case Admitted, keep the build green.
8. Commit and push to main.

## Instruction list (94 total)

ACC, ADDINT, ANDINT, APPLY, APPLY1, APPLY2, APPLY3, APPTERM, APPTERM1, APPTERM2,
APPTERM3, ASRINT, ASSIGN, ATOM, BEQ, BGEINT, BGTINT, BLEINT, BLTINT, BNEQ, BOOLNOT,
BRANCH, BRANCHIF, BRANCHIFNOT, BUGEINT, BULTINT, CHECK_SIGNALS, CLOSURE, CLOSUREREC,
CONSTINT, DIVINT, ENVACC, EQ, GEINT, GETBYTESCHAR, GETDYNMET, GETFIELD, GETFLOATFIELD,
GETGLOBAL, GETGLOBALFIELD, GETMETHOD, GETPUBMET, GETSTRINGCHAR, GETVECTITEM, GRAB,
GTINT, ISINT, LEINT, LSLINT, LSRINT, LTINT, MAKEBLOCK, MAKEBLOCK1, MAKEBLOCK2,
MAKEBLOCK3, MAKEFLOATBLOCK, MODINT, MULINT, NEGINT, NEQ, OFFSETCLOSURE, OFFSETINT,
OFFSETREF, ORINT, POP, POPTRAP, PUSH, PUSHACC, PUSHATOM, PUSHCONSTINT, PUSHENVACC,
PUSHGETGLOBAL, PUSHGETGLOBALFIELD, PUSHOFFSETCLOSURE, PUSHTRAP, PUSH_RETADDR,
RAISE, RAISE_NOTRACE, RERAISE, RESTART, RETURN, SETBYTESCHAR, SETFIELD, SETFLOATFIELD,
SETGLOBAL, SETVECTITEM, STOP, SUBINT, SWITCH, UGEINT, ULTINT, VECTLENGTH, XORINT,
C_CALL
