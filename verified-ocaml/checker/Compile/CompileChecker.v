(* CompileChecker.v - Verifies that the untrusted proof satisfies the
   concrete CompileSpec (with the semi-auto source interpreter).

   The ConcreteCompileSpec Module Type is inlined here rather than imported,
   since the original SemiAutomatic.Compile.CompileSpec no longer exists.
   It uses `interpret` from SemiAutomatic.Interpret and `bytecode_behavior`
   from Manual.Compile.CompileSpec directly (not as parameters). *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Compile Require Import CompileSpec.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.
From OCamlInterp.Automatic.Compile Require Import Compile.
From OCamlInterp.Automatic.Compile Require Import CompileProof.

Module Type ConcreteCompileSpec.
  Parameter compile_program : program -> list instruction.
  Axiom compiler_correctness :
    forall (prog : program) (src_fuel : nat),
      match interpret src_fuel prog with
      | {| trace := src_trace; result := Term_normal _ |} =>
        exists (bc_fuel : nat),
          let bc := bytecode_behavior bc_fuel (compile_program prog) (@nil Value.value) in
          bc.(trace) = src_trace /\
          match bc.(result) with
          | Term_normal _ => True
          | _ => False
          end
      | _ => True
      end.
End ConcreteCompileSpec.

Module Check <: ConcreteCompileSpec.
  Definition compile_program := compile_program.
  Definition compiler_correctness := compiler_correctness.
End Check.
