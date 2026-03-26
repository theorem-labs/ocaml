(* CompileSpec.v - [SEMI-AUTO] Concrete CompileSpec with the semi-auto
   source interpreter supplied as the concrete `interpret`.

   This builds on manual/CompileSpec.v (which has interpret as a Parameter)
   by providing the concrete interpret from semi-auto/Interpret. *)

From OCamlInterp.Manual.Compile Require Import CompileSpec.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Utils Require Import Value Syntax Observable.
From OCamlInterp.SemiAutomatic.Interpret Require Import Interpret.

(* Concrete spec: interpret is the fuel-based source interpreter
   from semi-auto/Interpret/Interpret.v *)
Module Type ConcreteCompileSpec.

  (* Compiler (provided by Untrusted) *)
  Parameter compile_program : program -> list instruction.

  (* Correctness with the CONCRETE source interpreter *)
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
