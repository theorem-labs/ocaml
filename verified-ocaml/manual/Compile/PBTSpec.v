(* PBTSpec.v - [TRUSTED] Module Type specifying that the compiler
   agrees with a reference oracle on a finite test suite.

   The oracle bytecode is abstract; the checker fills it with concrete
   bytecode obtained by running ocamlc and decoding its output.
   Agreement is checked by computation inside Rocq.

   Trust model: this file defines the CONCRETE correctness statement using
   only trusted components (bytecode_behavior, behavior_equiv, step_list_of
   from CompileSpec.v). The untrusted code must provide compile_program,
   test_programs, oracle_bytecode, and a proof of agreement.

   This file has NO dependencies outside manual/. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Run HandleInstrSpec.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Compile Require Import CompileSpec.
Open Scope list_scope.

Module Type PBTSpec (Import HI : HandleInstrSpec).

  Definition step_fn : list instruction -> state -> step_result :=
    step_list_of HI.handle_instr.

  (* Compiler under test (provided by automatic/) *)
  Parameter compile_program : program -> list instruction.

  (* Finite test suite: concrete list of test programs *)
  Parameter test_programs : list program.

  (* Reference bytecode for each test program, obtained by running ocamlc
     on pp_program(prog) and decoding the resulting .byte file. *)
  Parameter oracle_bytecode : program -> list instruction.

  (* Non-triviality: the test suite must be substantial *)
  Axiom test_suite_nonempty : (length test_programs >= 1)%nat.

  (* Agreement: for every program in the test suite, running bytecode
     from our compiler and from the oracle through the same interpreter
     produces equivalent behaviors at every fuel level. *)
  Axiom pbt_agreement :
    forall (prog : program),
      In prog test_programs ->
      forall (fuel : nat),
        behavior_equiv
          (bytecode_behavior step_fn fuel (compile_program prog) [])
          (bytecode_behavior step_fn fuel (oracle_bytecode prog) []).

End PBTSpec.
