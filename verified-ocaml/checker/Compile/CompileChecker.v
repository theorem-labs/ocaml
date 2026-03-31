(* CompileChecker.v - Verifies that the untrusted proof satisfies the
   trusted CompileSpec Module Type (from manual/Compile/CompileSpec.v).
   Supplies the concrete compile_program (from automatic/), interpret
   (from semi-auto/), and the correctness proof (from automatic/). *)

From OCamlInterp.Manual.Compile Require Import CompileSpec.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Compile Require Import CompileProof.

Module Check <: CompileSpec.
  Definition compile_program := compile_program.
  Definition interpret := interpret.
  Definition compiler_correctness := compiler_correctness.
End Check.
