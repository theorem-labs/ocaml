(* CorrectnessChecker.v - Checker: verifies that the untrusted compiler,
   source interpreter, and correctness proofs satisfy the trusted
   CorrectnessSpec. *)

From OCamlInterp.Manual.Correctness Require Import CorrectnessSpec.
From OCamlInterp.SemiAutomatic.Interpret Require Import SourceInterp.
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Correctness Require Import CorrectnessProofs.

Module Check <: CorrectnessSpec.
  Definition compile_program := compile_program.
  Definition interpret := interpret.
  Definition compiler_correct := compiler_correct.
  Definition compiler_correctness := compiler_correctness.
End Check.
