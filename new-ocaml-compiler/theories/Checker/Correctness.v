(* Correctness.v - Checker: verifies that the untrusted compiler,
   source interpreter, and correctness proofs satisfy the trusted
   CorrectnessSpec. *)

From OCamlInterp.SemiTrusted Require Import CorrectnessSpec.
From OCamlInterp.Untrusted Require Import SourceInterp Compile CorrectnessProofs.

Module Check <: CorrectnessSpec.
  Definition compile_program := compile_program.
  Definition interpret := interpret.
  Definition compiler_correct := compiler_correct.
  Definition compiler_correctness := compiler_correctness.
End Check.
