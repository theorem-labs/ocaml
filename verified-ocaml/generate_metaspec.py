#!/usr/bin/env python3
"""Generate MetaSpec uniqueness proof files for all 94 instructions.

Each per-instruction proof delegates to the shared axiom in
SharedLemmas.v via unique_from_handler_correct, resulting in zero
Admitted per instruction file.

The only Admitted in the entire MetaSpecVerification directory is
the single axiom handler_correct_determines_em_eq in SharedLemmas.v.
"""

import re
import os

METASPEC_DIR = "automatic/Bytecode/MetaSpecVerification"

# Read the MetaSpecFineGrainedSpec module type to extract per-instruction signatures
with open("manual/Bytecode/Interpret/MetaSpec.v") as f:
    metaspec_content = f.read()

# Extract everything inside Module Type MetaSpecFineGrainedSpec ... End MetaSpecFineGrainedSpec.
fg_match = re.search(
    r'Module Type MetaSpecFineGrainedSpec\.(.*?)End MetaSpecFineGrainedSpec\.',
    metaspec_content, re.DOTALL)
if not fg_match:
    raise RuntimeError("Could not find MetaSpecFineGrainedSpec in MetaSpec.v")
fg_body = fg_match.group(1)

# Extract each Parameter declaration
# Pattern: 'Parameter unique_NAME : <type>.'
# The type can span multiple lines and ends with a period followed by newline.
# We use \.\n to avoid matching the '.' in 's.(pc)'.
pattern = r'Parameter (unique_(\w+))\s*:\s*(.*?)\.\n'
matches = re.findall(pattern, fg_body, re.DOTALL)

if not matches:
    raise RuntimeError("No Parameter unique_* found in MetaSpecFineGrainedSpec")


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
    Returns (param_str, param_names) e.g. ('n p', ['n', 'p'])"""
    m = re.search(r'forall\s+(.*?),\s*\n?\s*forall\s+\(h1', sig, re.DOTALL)
    if m:
        params_raw = m.group(1).strip()
        param_names = params_raw.split()
        return params_raw, param_names
    return None, []


def generate_proof(lemma_name, name, sig_type):
    """Generate a per-instruction proof file.

    lemma_name: e.g. 'unique_ACC'
    name: e.g. 'ACC'
    sig_type: the type after ':' in 'Parameter unique_ACC : <type>'
    """
    instr_expr = get_instr_expr(name, sig_type)
    params_raw, param_names = get_params(sig_type)

    param_intro_str = " ".join(param_names) + " " if param_names else ""

    ie = instr_expr
    ie_paren = f"({ie})" if " " in ie else ie

    lines = []
    lines.append(f"(* {name}_unique.v - [UNTRUSTED] Per-instruction uniqueness proof for {name}. *)")
    lines.append("")
    lines.append("From Stdlib Require Import ZArith List Strings.String.")
    lines.append("From compcert Require Import Ctypes Clight Memory Values.")
    lines.append("From OCamlInterp.Manual.Bytecode Require Import AST Machine.")
    lines.append("From OCamlInterp.Manual.Bytecode.Interpret Require Import InstructSpec MetaSpec.")
    lines.append("From OCamlInterp.Automatic.Bytecode.MetaSpecVerification Require Import SharedLemmas.")
    lines.append("")

    # Reconstruct the lemma statement from the Parameter type
    # Clean up whitespace in sig_type
    clean_sig = re.sub(r'\s+', ' ', sig_type.strip())

    lines.append(f"Lemma {lemma_name} :")
    lines.append(f"  {sig_type.strip()}.")
    lines.append("Proof.")
    lines.append(f"  intros {param_intro_str}h1 h2 Hcorr1 Hcorr2 s.")
    lines.append(f"  exact (unique_from_handler_correct")
    lines.append(f"    (clight_of {ie_paren}) (pre_of {ie_paren})")
    lines.append(f"    (P_error_of {ie_paren}) (P_halt_of {ie_paren}) (P_ccall_of {ie_paren})")
    lines.append(f"    h1 h2 Hcorr1 Hcorr2 s).")
    lines.append("Qed.")
    lines.append("")

    return "\n".join(lines)


generated = 0
for lemma_name, name, sig_type in matches:
    filepath = os.path.join(METASPEC_DIR, f"{name}_unique.v")
    content = generate_proof(lemma_name, name, sig_type)
    with open(filepath, 'w') as f:
        f.write(content)
    generated += 1

print(f"Generated {generated} proof files")
