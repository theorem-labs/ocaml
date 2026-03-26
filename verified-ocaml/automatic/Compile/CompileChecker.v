(* CompileChecker.v - Verifies that the untrusted proof satisfies the
   concrete CompileSpec (with the semi-auto source interpreter). *)

From OCamlInterp.SemiAutomatic.Compile Require Import CompileSpec.
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Compile Require Import CompileProof.

Module Check <: ConcreteCompileSpec.
  Definition compile_program := compile_program.
  Definition compiler_correctness := compiler_correctness.
End Check.
