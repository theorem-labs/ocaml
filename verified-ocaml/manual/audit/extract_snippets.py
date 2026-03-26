#!/usr/bin/env python3
"""Extract per-instruction code snippets from Interp.v and interp.c.

Usage:
    python3 extract_snippets.py [INTERP_V] [INTERP_C]

Defaults:
    INTERP_V = ../../theories/Trusted/Bytecode/Interp.v  (relative to this script)
    INTERP_C = ./interp.c

Output:
    snippets/rocq/<INSTR>.tex   -- Rocq code for each instruction
    snippets/c/<INSTR>.tex      -- C code for each instruction
"""

import os
import re
import sys
import textwrap

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

DEFAULT_INTERP_V = os.path.join(
    SCRIPT_DIR, "..", "theories", "Bytecode", "Interpret.v"
)
# Search paths for Interpret.v (tried in order)
ALT_INTERP_V_PATHS = [
    os.path.join(SCRIPT_DIR, "..", "..", "manual", "theories", "Bytecode", "Interpret.v"),
]
DEFAULT_INTERP_C = os.path.join(SCRIPT_DIR, "interp.c")

ROCQ_OUT = os.path.join(SCRIPT_DIR, "snippets", "rocq")
C_OUT = os.path.join(SCRIPT_DIR, "snippets", "c")

# All instructions from AST.v (canonical names, uppercase)
ALL_INSTRUCTIONS = [
    "ACC", "PUSH", "PUSHACC", "POP", "ASSIGN",
    "ENVACC", "PUSHENVACC",
    "PUSH_RETADDR", "APPLY", "APPLY1", "APPLY2", "APPLY3",
    "APPTERM", "APPTERM1", "APPTERM2", "APPTERM3",
    "RETURN", "RESTART", "GRAB",
    "CLOSURE", "CLOSUREREC",
    "OFFSETCLOSURE", "PUSHOFFSETCLOSURE",
    "GETGLOBAL", "PUSHGETGLOBAL", "GETGLOBALFIELD", "PUSHGETGLOBALFIELD", "SETGLOBAL",
    "ATOM", "PUSHATOM",
    "MAKEBLOCK", "MAKEBLOCK1", "MAKEBLOCK2", "MAKEBLOCK3", "MAKEFLOATBLOCK",
    "GETFIELD", "GETFLOATFIELD", "SETFIELD", "SETFLOATFIELD",
    "VECTLENGTH", "GETVECTITEM", "SETVECTITEM",
    "GETBYTESCHAR", "SETBYTESCHAR", "GETSTRINGCHAR",
    "BRANCH", "BRANCHIF", "BRANCHIFNOT", "SWITCH", "BOOLNOT",
    "PUSHTRAP", "POPTRAP", "RAISE", "RERAISE", "RAISE_NOTRACE",
    "CHECK_SIGNALS",
    "C_CALL",
    "CONSTINT", "PUSHCONSTINT",
    "NEGINT", "ADDINT", "SUBINT", "MULINT", "DIVINT", "MODINT",
    "ANDINT", "ORINT", "XORINT", "LSLINT", "LSRINT", "ASRINT",
    "EQ", "NEQ", "LTINT", "LEINT", "GTINT", "GEINT",
    "OFFSETINT", "OFFSETREF", "ISINT",
    "GETMETHOD", "GETPUBMET", "GETDYNMET",
    "BEQ", "BNEQ", "BLTINT", "BLEINT", "BGTINT", "BGEINT",
    "ULTINT", "UGEINT", "BULTINT", "BUGEINT",
    "STOP", "EVENT", "BREAK",
    "PERFORM", "RESUME", "RESUMETERM", "REPERFORMTERM",
]


def escape_latex(text):
    """Escape special LaTeX characters inside code listings (minimal)."""
    # listings package handles most escaping; we just need to ensure
    # the file is valid LaTeX.
    return text


def extract_rocq_snippets(filepath):
    """Extract per-instruction snippets from Interp.v's step function."""
    with open(filepath, "r") as f:
        lines = f.readlines()

    snippets = {}
    in_step = False
    current_instr = None
    current_lines = []
    current_start_line = 0

    for i, line in enumerate(lines):
        lineno = i + 1

        # Detect start of step function
        if "Definition step" in line:
            in_step = True
            continue

        if not in_step:
            continue

        # Detect a new instruction case: "  | INSTR_NAME"
        m = re.match(r"^\s*\|\s+([A-Z][A-Z0-9_]+)", line)
        if m:
            # Save previous instruction
            if current_instr and current_lines:
                snippets[current_instr] = (current_start_line, current_lines[:])
            current_instr = m.group(1)
            current_lines = [line.rstrip()]
            current_start_line = lineno
            continue

        # Detect end of step function
        if re.match(r"^\s*end\s*$", line) or re.match(r"^\s*end\.\s*$", line):
            if current_instr and current_lines:
                snippets[current_instr] = (current_start_line, current_lines[:])
            # Check if this is the final end of the step function
            # (we look for "end." or two consecutive "end")
            if line.strip() == "end.":
                in_step = False
                break
            continue

        if current_instr:
            current_lines.append(line.rstrip())

    # Handle combined cases like "RAISE | RERAISE | RAISE_NOTRACE"
    # and "GETBYTESCHAR | GETSTRINGCHAR"
    combined_cases = {
        "RAISE": ["RERAISE", "RAISE_NOTRACE"],
        "GETBYTESCHAR": ["GETSTRINGCHAR"],
    }
    for primary, aliases in combined_cases.items():
        if primary in snippets:
            for alias in aliases:
                if alias not in snippets:
                    snippets[alias] = snippets[primary]

    return snippets


def extract_c_snippets(filepath):
    """Extract per-instruction snippets from interp.c."""
    with open(filepath, "r") as f:
        lines = f.readlines()

    snippets = {}
    current_instr = None
    current_instrs = []  # multiple instructions can share a case
    current_lines = []
    current_start_line = 0

    # Also handle the macro expansions
    macro_instructions = {
        "Integer_comparison": {
            "EQ": "(intnat,EQ, ==)",
            "NEQ": "(intnat,NEQ, !=)",
            "LTINT": "(intnat,LTINT, <)",
            "LEINT": "(intnat,LEINT, <=)",
            "GTINT": "(intnat,GTINT, >)",
            "GEINT": "(intnat,GEINT, >=)",
            "ULTINT": "(uintnat,ULTINT, <)",
            "UGEINT": "(uintnat,UGEINT, >=)",
        },
        "Integer_branch_comparison": {
            "BEQ": '(intnat,BEQ, ==, "==")',
            "BNEQ": '(intnat,BNEQ, !=, "!=")',
            "BLTINT": '(intnat,BLTINT, <, "<")',
            "BLEINT": '(intnat,BLEINT, <=, "<=")',
            "BGTINT": '(intnat,BGTINT, >, ">")',
            "BGEINT": '(intnat,BGEINT, >=, ">=")',
            "BULTINT": '(uintnat,BULTINT, <, "<")',
            "BUGEINT": '(uintnat,BUGEINT, >=, ">=")',
        },
    }

    for i, line in enumerate(lines):
        lineno = i + 1

        # Detect Instruct(NAME): pattern
        m = re.match(r"\s*Instruct\((\w+)\)\s*:", line)
        if m:
            # Save previous
            if current_instrs and current_lines:
                for inst in current_instrs:
                    snippets[inst] = (current_start_line, current_lines[:])

            name = m.group(1)
            # Strip numbered variants like ACC0-ACC7 -> ACC
            base = re.sub(r"\d+$", "", name)

            # Check if this is a fallthrough (line ends with fallthrough comment
            # or Next; on same line)
            if "Next;" in line or "Fallthrough" in line.lower() or "fallthrough" in line.lower():
                # Short one-liner or fallthrough
                if name in snippets:
                    # append to existing
                    old_start, old_lines = snippets[name]
                    old_lines.append(line.rstrip())
                    snippets[name] = (old_start, old_lines)
                else:
                    snippets[name] = (lineno, [line.rstrip()])
                current_instrs = []
                current_lines = []
                continue

            current_instrs = [name]
            current_lines = [line.rstrip()]
            current_start_line = lineno
            continue

        # Detect macro-based instruction definitions
        for macro_name, instr_map in macro_instructions.items():
            m2 = re.match(rf"\s*{macro_name}\((\w+),\s*(\w+)", line)
            if m2:
                instr_name = m2.group(2)
                if instr_name in instr_map or instr_name in ALL_INSTRUCTIONS:
                    snippets[instr_name] = (lineno, [line.rstrip()])

        if current_instrs:
            current_lines.append(line.rstrip())

            # Detect end of case: "Next;" at start of line or after statement
            if re.search(r"\bNext\b", line):
                for inst in current_instrs:
                    snippets[inst] = (current_start_line, current_lines[:])
                current_instrs = []
                current_lines = []

    # Map specialized C names to our canonical names
    c_name_map = {
        "ACC0": "ACC", "ACC1": "ACC", "ACC2": "ACC", "ACC3": "ACC",
        "ACC4": "ACC", "ACC5": "ACC", "ACC6": "ACC", "ACC7": "ACC",
        "PUSHACC0": "PUSH",  # PUSH and PUSHACC0 are the same in interp.c
        "PUSHACC1": "PUSHACC", "PUSHACC2": "PUSHACC",
        "PUSHACC3": "PUSHACC", "PUSHACC4": "PUSHACC",
        "PUSHACC5": "PUSHACC", "PUSHACC6": "PUSHACC",
        "PUSHACC7": "PUSHACC",
        "ENVACC1": "ENVACC", "ENVACC2": "ENVACC",
        "ENVACC3": "ENVACC", "ENVACC4": "ENVACC",
        "PUSHENVACC1": "PUSHENVACC", "PUSHENVACC2": "PUSHENVACC",
        "PUSHENVACC3": "PUSHENVACC", "PUSHENVACC4": "PUSHENVACC",
        "GETFIELD0": "GETFIELD", "GETFIELD1": "GETFIELD",
        "GETFIELD2": "GETFIELD", "GETFIELD3": "GETFIELD",
        "SETFIELD0": "SETFIELD", "SETFIELD1": "SETFIELD",
        "SETFIELD2": "SETFIELD", "SETFIELD3": "SETFIELD",
        "CONST0": "CONSTINT", "CONST1": "CONSTINT",
        "CONST2": "CONSTINT", "CONST3": "CONSTINT",
        "PUSHCONST0": "PUSHCONSTINT", "PUSHCONST1": "PUSHCONSTINT",
        "PUSHCONST2": "PUSHCONSTINT", "PUSHCONST3": "PUSHCONSTINT",
        "ATOM0": "ATOM",
        "PUSHATOM0": "PUSHATOM",
        "OFFSETCLOSUREM3": "OFFSETCLOSURE",
        "OFFSETCLOSURE0": "OFFSETCLOSURE",
        "OFFSETCLOSURE3": "OFFSETCLOSURE",
        "PUSHOFFSETCLOSUREM3": "PUSHOFFSETCLOSURE",
        "PUSHOFFSETCLOSURE0": "PUSHOFFSETCLOSURE",
        "PUSHOFFSETCLOSURE3": "PUSHOFFSETCLOSURE",
        "C_CALL1": "C_CALL", "C_CALL2": "C_CALL",
        "C_CALL3": "C_CALL", "C_CALL4": "C_CALL",
        "C_CALL5": "C_CALL", "C_CALLN": "C_CALL",
        "RAISE_NOTRACE": "RAISE_NOTRACE",
    }

    # Copy specialized entries to canonical names (prefer the general form)
    for c_name, canonical in c_name_map.items():
        if c_name in snippets and canonical not in snippets:
            snippets[canonical] = snippets[c_name]

    # Handle raise_notrace label (grab the raise_notrace: label section)
    # Also ensure RERAISE and RAISE_NOTRACE have entries
    if "RAISE" in snippets:
        for alias in ["RERAISE", "RAISE_NOTRACE"]:
            if alias not in snippets:
                snippets[alias] = snippets["RAISE"]

    return snippets


def write_snippet(outdir, instr_name, start_line, lines, lang):
    """Write a snippet .tex file."""
    os.makedirs(outdir, exist_ok=True)
    filepath = os.path.join(outdir, f"{instr_name}.tex")

    # Trim trailing empty lines
    while lines and not lines[-1].strip():
        lines = lines[:-1]

    code = "\n".join(lines)

    if lang == "rocq":
        env = "rocqcode"
        first_line = start_line
    else:
        env = "ccode"
        first_line = start_line

    with open(filepath, "w") as f:
        f.write(f"% Auto-generated from {lang} source, line {start_line}\n")
        f.write(f"\\begin{{{env}}}[firstnumber={first_line}]\n")
        f.write(code + "\n")
        f.write(f"\\end{{{env}}}\n")


def write_lines_tex(snippets_dir, rocq_snippets, c_snippets):
    """Write snippets/lines.tex with \\rocqline{INSTR} and \\cline{INSTR} macros."""
    filepath = os.path.join(snippets_dir, "lines.tex")
    os.makedirs(snippets_dir, exist_ok=True)
    with open(filepath, "w") as f:
        f.write("% Auto-generated line number macros. Do not edit.\n")
        f.write("% Usage: \\rocqline{ACC} expands to the line number in Interpret.v\n")
        f.write("% Usage: \\clineno{ACC} expands to the line number in interp.c\n\n")
        for instr in ALL_INSTRUCTIONS:
            if instr in rocq_snippets:
                start_line, _ = rocq_snippets[instr]
                f.write(f"\\expandafter\\def\\csname rocqline@{instr}\\endcsname{{{start_line}}}\n")
            if instr in c_snippets:
                start_line, _ = c_snippets[instr]
                f.write(f"\\expandafter\\def\\csname cline@{instr}\\endcsname{{{start_line}}}\n")


def main():
    interp_v = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_INTERP_V
    interp_c = sys.argv[2] if len(sys.argv) > 2 else DEFAULT_INTERP_C

    # Try alternative paths if default doesn't exist
    if not os.path.exists(interp_v):
        for alt in ALT_INTERP_V_PATHS:
            if os.path.exists(alt):
                interp_v = alt
                break

    if not os.path.exists(interp_v):
        print(f"Warning: {interp_v} not found, skipping Rocq snippets", file=sys.stderr)
        rocq_snippets = {}
    else:
        print(f"Extracting Rocq snippets from {interp_v}")
        rocq_snippets = extract_rocq_snippets(interp_v)

    if not os.path.exists(interp_c):
        print(f"Warning: {interp_c} not found, skipping C snippets", file=sys.stderr)
        c_snippets = {}
    else:
        print(f"Extracting C snippets from {interp_c}")
        c_snippets = extract_c_snippets(interp_c)

    rocq_count = 0
    c_count = 0

    for instr in ALL_INSTRUCTIONS:
        if instr in rocq_snippets:
            start_line, lines = rocq_snippets[instr]
            write_snippet(ROCQ_OUT, instr, start_line, lines, "rocq")
            rocq_count += 1

        if instr in c_snippets:
            start_line, lines = c_snippets[instr]
            write_snippet(C_OUT, instr, start_line, lines, "c")
            c_count += 1

    # Write line number macros
    write_lines_tex(os.path.join(SCRIPT_DIR, "snippets"), rocq_snippets, c_snippets)

    print(f"Wrote {rocq_count}/{len(ALL_INSTRUCTIONS)} Rocq snippets to {ROCQ_OUT}")
    print(f"Wrote {c_count}/{len(ALL_INSTRUCTIONS)} C snippets to {C_OUT}")
    print(f"Wrote snippets/lines.tex with line number macros")

    # Report missing
    missing_rocq = [i for i in ALL_INSTRUCTIONS if i not in rocq_snippets]
    missing_c = [i for i in ALL_INSTRUCTIONS if i not in c_snippets]
    if missing_rocq:
        print(f"Missing Rocq: {', '.join(missing_rocq)}")
    if missing_c:
        print(f"Missing C: {', '.join(missing_c)}")


if __name__ == "__main__":
    main()
