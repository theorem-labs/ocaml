(* CorrectnessSpec.v - [TRUSTED] Module Type specifying what the compiler
   correctness proof must deliver. The compiler and source interpreter are
   declared as Parameters (provided by Untrusted code); the theorem states
   that compilation preserves observable behavior. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Trusted.Bytecode Require Import Value AST Machine Interp.
From OCamlInterp.Trusted Require Import Observable.
From OCamlInterp.SemiTrusted Require Import Syntax.

Module Type CorrectnessSpec.

  (* Compiler and source interpreter (provided by Untrusted) *)
  Parameter compile_program : program -> list instruction.
  Parameter interpret : nat -> program -> behavior.

  (* The correctness statement: if the source interpreter terminates
     normally, the compiled bytecode terminates normally with the
     same output trace. *)
  Parameter compiler_correct : program -> Prop.

  Axiom compiler_correctness :
    forall (prog : program), compiler_correct prog.

End CorrectnessSpec.
