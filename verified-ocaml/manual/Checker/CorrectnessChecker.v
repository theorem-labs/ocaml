(* CorrectnessChecker.v - Checker: verifies that the untrusted compiler,
   source interpreter, and correctness proofs satisfy the trusted
   CompileSpec. *)

From OCamlInterp.Manual.Compile Require Import CompileSpec.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Compile Require Import CompileProof.

Module Check <: CompileSpec.
  Definition compile_program := compile_program.
  Definition interpret := interpret.
  Definition compiler_correct := compiler_correct.
  Definition compiler_correctness := compiler_correctness.
End Check.
