(* GETBYTESCHAR_correct.v -- GETBYTESCHAR correctness proof.

   GETBYTESCHAR has an identical C body to GETSTRINGCHAR, and
   both map to handle_GETSTRINGCHAR in Interpret.v.  The proof
   follows from the GETSTRINGCHAR proof plus body equality.

   No Axioms, no Admitted. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.
From OCamlInterp.Automatic Require Import Bytecode.InstructVerification.GETSTRINGCHAR_correct.

(* The fn_body fields are definitionally equal *)
Local Lemma body_eq :
  fn_body f_instr_GETBYTESCHAR = fn_body f_instr_GETSTRINGCHAR.
Proof. reflexivity. Qed.

Theorem verify_GETBYTESCHAR_correct :
    handler_correct handle_GETSTRINGCHAR f_instr_GETBYTESCHAR
      (fun e m s ard =>
         getstringchar_heap_pre m s ard /\
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             0 <= idx /\ idx * 2 + 1 <= Int64.max_signed /\
             match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
             | Some (Val_int c) => 0 <= c <= 255
             | _ => True
             end /\
             (forall cv, val_repr (ar_heap_map ard) (ar_code_base_block ard) (ar_code_base_ofs ard) (Val_int idx) cv ->
              exists z, cv = Vlong z)
         | _ => True
         end)
      (fun msg s =>
         match s.(Machine.stack) with
         | Val_int idx :: _ =>
             match field_or_heap s s.(Machine.accu) (Z.to_nat idx) with
             | Some (Val_int _) => False
             | _ => True
             end
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct.
  (* handler_correct unfolds to matching on handle_GETSTRINGCHAR s.(pc) s.
     The C function body is identical, so we can rewrite. *)
  pose proof (verify_GETSTRINGCHAR_correct) as Hgsc.
  unfold handler_correct in Hgsc.
  specialize (Hgsc e le m s).
  destruct (handle_GETSTRINGCHAR (pc s) s) eqn:Hres.
  - (* Step case *)
    intros ard Hpre Hstep.
    specialize (Hgsc ard Hpre Hstep).
    destruct Hgsc as [le' [m' [out [Hexec Habs]]]].
    exists le', m', out.
    split.
    + rewrite body_eq. exact Hexec.
    + exact Habs.
  - (* Error case *)
    exact Hgsc.
  - (* Halt case *)
    exact Hgsc.
  - (* CCall_request case *)
    exact Hgsc.
Qed.
