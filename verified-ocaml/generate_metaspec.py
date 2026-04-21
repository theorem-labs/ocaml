#!/usr/bin/env python3
"""Generate MetaSpec uniqueness proof files for all 94 instructions.

Constructor order in step_result: Step, Halt, Error, CCall_request.
After destruct on h1 and h2, the 16 cases are:
  Step/Step, Step/Halt, Step/Error, Step/CCall,
  Halt/Step, Halt/Halt, Halt/Error, Halt/CCall,
  Error/Step, Error/Halt, Error/Error, Error/CCall,
  CCall/Step, CCall/Halt, CCall/Error, CCall/CCall.

For non-STOP: P_halt_of is False, so all Halt cases are impossible.
For non-C_CALL: P_ccall_of is False, so all CCall cases are impossible.
We use 'all: try ...' to eliminate these in bulk after the destruct.
"""

import re
import os

METASPEC_DIR = "automatic/Bytecode/MetaSpecVerification"

with open("automatic/Bytecode/MetaSpecProof.v") as f:
    proof_content = f.read()

pattern = r'(Lemma unique_(\w+)\s*:(.*?))(?=\nProof\.)'
matches = re.findall(pattern, proof_content, re.DOTALL)


def get_instr_expr(name, sig):
    m = re.search(r'clight_of\s+\(([^)]+)\)', sig)
    if m:
        return m.group(1).strip()
    m = re.search(r'clight_of\s+(\w+)', sig)
    if m:
        return m.group(1).strip()
    return name


def get_params(sig):
    """Extract forall parameters before the handler quantifiers.
    Returns (param_str, param_names) e.g. ('forall n p,', ['n', 'p'])"""
    m = re.search(r'forall\s+(.*?),\s*\n?\s*forall\s+\(h1', sig, re.DOTALL)
    if m:
        params_raw = m.group(1).strip()
        param_names = params_raw.split()
        return params_raw, param_names
    return None, []


def generate_proof(name, full_sig, sig_body):
    instr_expr = get_instr_expr(name, sig_body)
    params_raw, param_names = get_params(sig_body)

    is_stop = (name == "STOP")
    is_ccall = (name == "C_CALL")

    param_intro_str = " ".join(param_names) + " " if param_names else ""
    forall_params = f"forall {params_raw},\n  " if params_raw else ""

    ie = instr_expr
    ie_paren = f"({ie})" if " " in ie else ie

    # Number of _ placeholders for P_halt_False / P_ccall_False
    # (one per instruction parameter, plus 'v' for halt or 'n0 args0 s0' for ccall)
    n_params = len(param_names)
    halt_underscores = " ".join(["_"] * (n_params + 1))
    ccall_underscores = " ".join(["_"] * (n_params + 3))

    # Shorthand for the 5 dispatch arguments
    dispatch = (f"(clight_of {ie_paren})\n"
                f"      (pre_of {ie_paren}) (P_error_of {ie_paren}) "
                f"(P_halt_of {ie_paren}) (P_ccall_of {ie_paren})")

    lines = []
    lines.append(f"(* {name}_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for {name}. *)")
    lines.append("")
    lines.append("From Stdlib Require Import ZArith List Strings.String.")
    lines.append("From compcert Require Import Maps Ctypes Clight Globalenvs Memory Values.")
    lines.append("From OCamlInterp.Manual.Bytecode Require Import AST Machine.")
    lines.append("From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.")
    lines.append("")

    # P_halt helper (False for non-STOP)
    if not is_stop:
        lines.append(f"Lemma {name}_P_halt_False : {forall_params}forall v, P_halt_of {ie_paren} v -> False.")
        lines.append(f"Proof. intros{' ' + params_raw + ' ' if params_raw else ' '}v [_ H]. exact H. Qed.")
        lines.append("")

    # P_ccall helper (False for non-C_CALL)
    if not is_ccall:
        lines.append(f"Lemma {name}_P_ccall_False : {forall_params}forall n0 args0 s0, P_ccall_of {ie_paren} n0 args0 s0 -> False.")
        lines.append(f"Proof. intros{' ' + params_raw + ' ' if params_raw else ' '}n0 args0 s0 [_ H]. exact H. Qed.")
        lines.append("")

    # Step/Step equality (Admitted)
    lines.append(f"Lemma {name}_step_step_eq :")
    lines.append(f"  {forall_params}forall (h1 h2 : Z -> state -> step_result) s s1 s2,")
    lines.append(f"    handler_correct h1 {dispatch} ->")
    lines.append(f"    handler_correct h2 {dispatch} ->")
    lines.append(f"    h1 s.(pc) s = Step s1 -> h2 s.(pc) s = Step s2 -> s1 = s2.")
    lines.append(f"Proof. Admitted.")
    lines.append("")

    # Step/Error exclusivity (Admitted)
    lines.append(f"Lemma {name}_step_error_excl :")
    lines.append(f"  {forall_params}forall (h1 h2 : Z -> state -> step_result) s s' msg,")
    lines.append(f"    handler_correct h1 {dispatch} ->")
    lines.append(f"    handler_correct h2 {dispatch} ->")
    lines.append(f"    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Error msg -> False.")
    lines.append(f"Proof. Admitted.")
    lines.append("")

    # STOP-specific helpers
    if is_stop:
        lines.append(f"Lemma {name}_halt_halt_eq :")
        lines.append(f"  forall (h1 h2 : Z -> state -> step_result) s v1 v2,")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = Halt v1 -> h2 s.(pc) s = Halt v2 -> v1 = v2.")
        lines.append(f"Proof. Admitted.")
        lines.append("")
        lines.append(f"Lemma {name}_step_halt_excl :")
        lines.append(f"  forall (h1 h2 : Z -> state -> step_result) s s' v,")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = Step s' -> h2 s.(pc) s = Halt v -> False.")
        lines.append(f"Proof. Admitted.")
        lines.append("")
        lines.append(f"Lemma {name}_halt_error_excl :")
        lines.append(f"  forall (h1 h2 : Z -> state -> step_result) s v msg,")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = Halt v -> h2 s.(pc) s = Error msg -> False.")
        lines.append(f"Proof. Admitted.")
        lines.append("")

    # C_CALL-specific helpers
    if is_ccall:
        lines.append(f"Lemma {name}_ccall_ccall_eq :")
        lines.append(f"  {forall_params}forall (h1 h2 : Z -> state -> step_result) s n1 args1 s1 n2 args2 s2,")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = CCall_request n1 args1 s1 ->")
        lines.append(f"    h2 s.(pc) s = CCall_request n2 args2 s2 ->")
        lines.append(f"    n1 = n2 /\\ args1 = args2 /\\ s1 = s2.")
        lines.append(f"Proof. Admitted.")
        lines.append("")
        lines.append(f"Lemma {name}_step_ccall_excl :")
        lines.append(f"  {forall_params}forall (h1 h2 : Z -> state -> step_result) s s' n0 args0 s'',")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = Step s' -> h2 s.(pc) s = CCall_request n0 args0 s'' -> False.")
        lines.append(f"Proof. Admitted.")
        lines.append("")
        lines.append(f"Lemma {name}_error_ccall_excl :")
        lines.append(f"  {forall_params}forall (h1 h2 : Z -> state -> step_result) s msg n0 args0 s',")
        lines.append(f"    handler_correct h1 {dispatch} ->")
        lines.append(f"    handler_correct h2 {dispatch} ->")
        lines.append(f"    h1 s.(pc) s = Error msg -> h2 s.(pc) s = CCall_request n0 args0 s' -> False.")
        lines.append(f"Proof. Admitted.")
        lines.append("")

    # Main uniqueness lemma
    lines.append(full_sig.strip())
    lines.append("Proof.")
    lines.append(f"  intros {param_intro_str}h1 h2 Hcorr1 Hcorr2 s.")
    lines.append(f"  pose proof (Hcorr1 empty_env (PTree.empty _) Mem.empty s) as Hs1.")
    lines.append(f"  pose proof (Hcorr2 empty_env (PTree.empty _) Mem.empty s) as Hs2.")
    lines.append(f"  destruct (h1 s.(pc) s) eqn:E1; destruct (h2 s.(pc) s) eqn:E2.")

    # Eliminate impossible cases in bulk using 'all: try ...'
    if not is_stop:
        lines.append(f"  all: try (exfalso; exact ({name}_P_halt_False {halt_underscores} Hs1)).")
        lines.append(f"  all: try (exfalso; exact ({name}_P_halt_False {halt_underscores} Hs2)).")
    if not is_ccall:
        lines.append(f"  all: try (exfalso; exact ({name}_P_ccall_False {ccall_underscores} Hs1)).")
        lines.append(f"  all: try (exfalso; exact ({name}_P_ccall_False {ccall_underscores} Hs2)).")

    # Case order after elimination depends on instruction type.
    # For regular instructions (not STOP, not C_CALL):
    #   After eliminating Halt/CCall: Step/Step, Step/Error, Error/Step, Error/Error
    if not is_stop and not is_ccall:
        lines.append(f"  - (* Step/Step *)")
        lines.append(f"    assert (s0 = s1) by (eapply {name}_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.")
        lines.append(f"  - (* Step/Error *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Error/Step *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* Error/Error *) constructor.")

    # For C_CALL (P_halt False, but P_ccall valid):
    #   After eliminating Halt: Step/Step, Step/Error, Step/CCall, Error/Step, Error/Error, Error/CCall, CCall/Step, CCall/Error, CCall/CCall
    elif is_ccall:
        lines.append(f"  - (* Step/Step *)")
        lines.append(f"    assert (s0 = s1) by (eapply {name}_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.")
        lines.append(f"  - (* Step/Error *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Step/CCall *)")
        lines.append(f"    exfalso. eapply {name}_step_ccall_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Error/Step *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* Error/Error *) constructor.")
        lines.append(f"  - (* Error/CCall *)")
        lines.append(f"    exfalso. eapply {name}_error_ccall_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* CCall/Step *)")
        lines.append(f"    exfalso. eapply {name}_step_ccall_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* CCall/Error *)")
        lines.append(f"    exfalso. eapply {name}_error_ccall_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* CCall/CCall *)")
        lines.append(f"    pose proof ({name}_ccall_ccall_eq {param_intro_str}h1 h2 s _ _ _ _ _ _ Hcorr1 Hcorr2 E1 E2) as [? [? ?]].")
        lines.append(f"    subst. constructor.")

    # For STOP (P_ccall False, but P_halt valid):
    #   After eliminating CCall: Step/Step, Step/Halt, Step/Error, Halt/Step, Halt/Halt, Halt/Error, Error/Step, Error/Halt, Error/Error
    elif is_stop:
        lines.append(f"  - (* Step/Step *)")
        lines.append(f"    assert (s0 = s1) by (eapply {name}_step_step_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.")
        lines.append(f"  - (* Step/Halt *)")
        lines.append(f"    exfalso. eapply {name}_step_halt_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Step/Error *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Halt/Step *)")
        lines.append(f"    exfalso. eapply {name}_step_halt_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* Halt/Halt *)")
        lines.append(f"    assert (v = v0) by (eapply {name}_halt_halt_eq; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2]). subst. constructor.")
        lines.append(f"  - (* Halt/Error *)")
        lines.append(f"    exfalso. eapply {name}_halt_error_excl; [exact Hcorr1 | exact Hcorr2 | exact E1 | exact E2].")
        lines.append(f"  - (* Error/Step *)")
        lines.append(f"    exfalso. eapply {name}_step_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* Error/Halt *)")
        lines.append(f"    exfalso. eapply {name}_halt_error_excl; [exact Hcorr2 | exact Hcorr1 | exact E2 | exact E1].")
        lines.append(f"  - (* Error/Error *) constructor.")

    lines.append("Qed.")
    lines.append("")

    return "\n".join(lines)


generated = 0
for full_sig, name, sig_body in matches:
    pass
    filepath = os.path.join(METASPEC_DIR, f"{name}_unique.v")
    content = generate_proof(name, full_sig, sig_body)
    with open(filepath, 'w') as f:
        f.write(content)
    generated += 1

print(f"Generated {generated} proof files")
