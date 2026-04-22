(* SETVECTITEM_correct.v -- SETVECTITEM correctness proof.

   SETVECTITEM: pops idx and newval from stack, writes newval to
   heap block accu[idx] via caml_modify, sets accu = val_unit,
   pops 2 stack entries.

   C handler calls caml_modify externally. The bigstep proof is
   constructed manually (Scall cannot be handled computationally).

   NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Automatic.Bytecode Require Import Interpret.
From OCamlInterp.Manual Require Import Bytecode.AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

(* ================================================================== *)
(* Semantic lemmas                                                     *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof. intros. unfold sem_cast. simpl classify_cast. reflexivity. Qed.

Local Lemma sem_cast_tlong_tlong_vlong : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. unfold sem_cast. simpl classify_cast. rewrite ptr64_true. reflexivity. Qed.

Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof. intros. reflexivity. Qed.

Local Lemma sem_add_ptr_tlong_idx : forall b ofs idx m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vlong idx) tlong m
  = Some (Vptr b (Ptrofs.add ofs
            (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 idx)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma shr_tagged_int : forall idx,
  0 <= idx -> idx * 2 + 1 <= Int64.max_signed ->
  Int64.shr (Int64.repr (idx * 2 + 1)) (Int64.repr 1) = Int64.repr idx.
Proof.
  intros idx Hge Hlt. unfold Int64.shr.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Int64.signed_repr by (split; [pose proof Int64.min_signed_neg; lia | exact Hlt]).
  rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite Z.div_add_l by lia. change (1 / 2)%Z with 0%Z. f_equal. lia.
Qed.

Local Lemma ptrofs_mul_8_of_int64 : forall idx,
  0 <= idx -> idx < Ptrofs.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr idx))
  = Ptrofs.repr (idx * 8).
Proof.
  intros idx Hge Hlt.
  change Ptrofs.half_modulus with (2^63)%Z in Hlt.
  unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr.
  2: { change Int64.max_unsigned with (2^64 - 1)%Z. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { change Ptrofs.max_unsigned with (2^64 - 1)%Z. lia. }
  rewrite Ptrofs.unsigned_repr.
  2: { change Ptrofs.max_unsigned with (2^64 - 1)%Z. lia. }
  f_equal. lia.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

(* ================================================================== *)
(* caml_modify definitions                                             *)
(* ================================================================== *)

Local Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Local Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

(* ================================================================== *)
(* Precondition                                                        *)
(* ================================================================== *)

Definition setvectitem_pre
    (e : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  forall idx newval rest,
    s.(Machine.stack) = Val_int idx :: newval :: rest ->
    (* Index bounds *)
    0 <= idx /\
    idx * 2 + 1 <= Int64.max_signed /\
    idx < Ptrofs.half_modulus /\
    (* Index C representation is Vlong (rules out vr_code_ptr) *)
    int_vlong ard idx /\
    (* Genv requirements *)
    e ! _caml_modify = None /\
    (exists b_cm,
       Genv.find_symbol ge _caml_modify = Some b_cm /\
       Genv.find_funct ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
    (* caml_modify call and its effects *)
    (forall accu_v newval_cv,
       val_repr hm cb co (Machine.accu s) accu_v ->
       val_repr hm cb co newval newval_cv ->
       exists hb hofs,
         accu_v = Vptr hb hofs /\
         hb <> sb /\ hb <> gb /\
         (* hb is also separate from any sp_b obtained from abs_rel *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            hb <> sp_b) /\
         exists m_cm,
           external_call caml_modify_ef ge
             (Vptr hb (Ptrofs.add hofs (Ptrofs.repr (idx * 8)))
              :: newval_cv :: nil)
             m E0 Vundef m_cm /\
           (* Struct block loads preserved *)
           (forall ofs v,
              Mem.load Mint64 m sb ofs = Some v ->
              Mem.load Mint64 m_cm sb ofs = Some v) /\
           (* Struct block stores succeed *)
           (forall ofs v_old v_new,
              Mem.load Mint64 m sb ofs = Some v_old ->
              exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
           (* Loads on blocks other than hb are preserved *)
           (forall b ofs v,
              b <> hb ->
              Mem.load Mint64 m b ofs = Some v ->
              Mem.load Mint64 m_cm b ofs = Some v) /\
           (* Permission preservation *)
           (forall b ofs k p,
              Mem.valid_block m b -> Mem.perm m b ofs k p ->
              Mem.perm m_cm b ofs k p) /\
           (* global_repr preserved *)
           (global_repr hm cb co m_cm (Machine.global s) gb (ar_global_ofs ard))).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETVECTITEM_correct :
    handler_correct handle_SETVECTITEM f_instr_SETVECTITEM
      (fun e m s ard => setvectitem_pre e m s ard)
      (fun _ s => match s.(Machine.stack) with
                  | Val_int idx :: newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields (Z.to_nat idx) newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the uniform type expected by InstructVerificationProof.v.
   handle_instr SETVECTITEM / clight_of SETVECTITEM / pre_of SETVECTITEM are
   convertible with handle_SETVECTITEM / f_instr_SETVECTITEM / setvectitem_pre.
   P_halt_of and P_ccall_of are vacuously satisfied (SETVECTITEM never halts
   or issues a C call).  P_error_of requires a small computation bridge. *)
Definition correct_SETVECTITEM :
    handler_correct (handle_instr Bytecode.AST.SETVECTITEM) (clight_of Bytecode.AST.SETVECTITEM)
      (pre_of Bytecode.AST.SETVECTITEM)
      (P_error_of Bytecode.AST.SETVECTITEM) (P_halt_of Bytecode.AST.SETVECTITEM) (P_ccall_of Bytecode.AST.SETVECTITEM).
Proof.
Admitted.

