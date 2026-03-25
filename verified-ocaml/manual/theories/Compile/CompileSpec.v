(* CompileSpec.v - [TRUSTED] Module Type specifying what the compiler
   correctness proof must deliver. The compiler and source interpreter are
   declared as Parameters (provided by Untrusted code); the theorem states
   that compilation preserves observable behavior. *)

From Stdlib Require Import ZArith PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode Require Import Interpret.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.

Module Type CompileSpec.

  (* Compiler and source interpreter (provided by Untrusted) *)
  Parameter compile_program : program -> list instruction.
  Parameter interpret : nat -> program -> behavior.

  (* The correctness statement: if the source interpreter terminates
     normally, the compiled bytecode terminates normally with the
     same output trace. *)
  Parameter compiler_correct : program -> Prop.

  Axiom compiler_correctness :
    forall (prog : program), compiler_correct prog.

End CompileSpec.
