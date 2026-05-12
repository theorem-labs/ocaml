(* PBTProof.v - [UNTRUSTED] Stage 2 PBT obligations.

   This module exposes the roadmap Theorem 2 interface. The external
   ocamlc/decode pipeline and its validation theorem are explicit
   untrusted obligations, not checker-side proof work. *)

From Stdlib Require Import ZArith Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Run HandleInstrSpec.
From OCamlInterp.Manual.Compile Require Import CompileSpec PBTSpec.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Automatic.Compile Require Import Compile.

Module Make (Import HI : HandleInstrSpec) <: PBTSpec HI.
  Definition step_fn := step_list_of HI.handle_instr.

  Definition compile_program := Compile.compile_program.

  Parameter pbt_seed : Type.
  Parameter pbt_program : pbt_seed -> program.
  Parameter ocamlc_compile : program -> option (list Z).
  Parameter ocamlc_decode : list Z -> option (list instruction).

  Axiom compile_models_ocamlc_ok :
    forall (seed : pbt_seed),
      let p := pbt_program seed in
      match ocamlc_compile p with
      | Some ocamlc_bytes =>
        match ocamlc_decode ocamlc_bytes with
        | Some ocamlc_instrs =>
          forall (fuel : nat),
            behavior_equiv
              (bytecode_behavior step_fn fuel (compile_program p) [])
              (bytecode_behavior step_fn fuel ocamlc_instrs [])
        | None => True
        end
      | None => True
      end.

  Parameter golden_seed : pbt_seed.
  Axiom golden_compiles_and_decodes :
    match ocamlc_compile (pbt_program golden_seed) with
    | Some bytes =>
      match ocamlc_decode bytes with
      | Some _ => True
      | None => False
      end
    | None => False
    end.
End Make.
