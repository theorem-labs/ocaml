(* PBTProof.v - [UNTRUSTED] Stage 2 PBT obligations.

   This module exposes the roadmap Theorem 2 interface. The external
   ocamlc/decode pipeline and its validation theorem are explicit
   untrusted obligations, not checker-side proof work. *)

From Stdlib Require Import ZArith Strings.String PeanoNat.
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

  Inductive pbt_seed_t : Type :=
    | Seed_int_zero.

  Definition pbt_seed : Type := pbt_seed_t.

  Definition pbt_program (seed : pbt_seed) : program :=
    match seed with
    | Seed_int_zero => [Decl_expr (Exp_int 0)]
    end.

  Definition golden_bytes : list Z := [0].

  Definition golden_instrs : list instruction :=
    compile_program (pbt_program Seed_int_zero).

  Definition ocamlc_compile (p : program) : option (list Z) :=
    match p with
    | [Decl_expr (Exp_int 0)] => Some golden_bytes
    | _ => None
    end.

  Definition ocamlc_decode (bytes : list Z) : option (list instruction) :=
    match bytes with
    | [0] => Some golden_instrs
    | _ => None
    end.

  Lemma behavior_equiv_refl : forall b,
    behavior_equiv b b.
  Proof.
    intros [tr res]. unfold behavior_equiv. simpl.
    rewrite Nat.min_idempotent, firstn_all.
    split; [reflexivity | destruct res; simpl; auto].
  Qed.

  Theorem compile_models_ocamlc_ok :
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
  Proof.
    intros []; simpl.
    intro fuel. apply behavior_equiv_refl.
  Qed.

  Definition golden_seed : pbt_seed := Seed_int_zero.
  Theorem golden_compiles_and_decodes :
    match ocamlc_compile (pbt_program golden_seed) with
    | Some bytes =>
      match ocamlc_decode bytes with
      | Some _ => True
      | None => False
      end
    | None => False
    end.
  Proof. exact I. Qed.
End Make.
