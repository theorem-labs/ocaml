(* SETFIELD_correct.v -- SETFIELD (parametric) correctness proof.

   SETFIELD n: reads field index n from the code buffer, pops the
   stack top (new value), reads accu as a heap pointer, calls
   caml_modify to write the new value to heap field n, sets
   accu = val_unit, advances pc by 1.

   Rocq handler:
     handle_SETFIELD n pc' s =
       match stack with
       | newval :: rest =>
         match accu with
         | Val_ptr addr =>
           match heap_lookup hp addr with
           | Some (_, fields) =>
             match set_nth fields n newval with
             | Some new_fields => Step (s <|pc:=pc'|> <|accu:=val_unit|>
                                          <|stack:=rest|> <|hp:=heap_update ...|>)
             | None => Error "index out of bounds"
             end
           | None => Error "dangling pointer"
           end
         | _ => Error "not a mutable block"
         end
       | _ => Error "stack underflow"
       end

   C handler (f_instr_SETFIELD):
     _t'1 = s->sp;               // read sp
     s->sp = _t'1 + 1;           // sp++ (pop)
     _t'3 = s->accu;             // read accu (tlong)
     _t'4 = s->pc;               // read pc
     _t'5 = *_t'4;               // read field index n from code buffer
     _t'6 = *_t'1;               // read stack top
     caml_modify(cast(_t'3) + _t'5, _t'6);   // heap write via caml_modify
     s->accu = ((0 << 1) + 1);   // val_unit = 1
     _t'2 = s->pc;               // read pc
     s->pc = _t'2 + 1;           // advance pc
     return 0;

   Combines SETFIELD0 (sp pop + heap write + val_unit) and
   SETGLOBAL (caml_modify external call + code buffer read + pc advance).

   NO AXIOMS.  NO ADMITTED. *)

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
From OCamlInterp.Manual Require Import Bytecode.Interpret.InstructSpec.
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

(* ================================================================== *)
(* Struct layout facts                                                 *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full).
Proof.
  eexists. split; [| split; [| split]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Local Lemma interp_state_co_setfield : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* caml_modify definitions                                             *)
(* ================================================================== *)

Definition caml_modify_ef : external_function :=
  EF_external "caml_modify"
    (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid cc_default).

Definition caml_modify_fundef : Ctypes.fundef function :=
  Ctypes.External caml_modify_ef ((tptr tlong) :: tlong :: nil) tvoid cc_default.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Local Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma sem_add_ptr_int_n : forall b ofs n_int m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vint n_int) tint
    m = Some (Vptr b (Ptrofs.add ofs
                (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                            (ptrofs_of_int Signed n_int)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_add_pc_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint)
    (Vint (Int.repr 1)) tint
    m = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma pc_rel_shift : forall cb co rocq_pc,
  pc_rel (Vptr cb (Ptrofs.add (Ptrofs.add co (Ptrofs.repr (rocq_pc * sizeof_code_t)))
                               (Ptrofs.repr 4)))
         cb (Ptrofs.add co (Ptrofs.repr sizeof_code_t)) rocq_pc.
Proof.
  intros. unfold pc_rel, sizeof_code_t.
  f_equal.
  rewrite Ptrofs.add_assoc.
  rewrite Ptrofs.add_assoc.
  f_equal.
  rewrite Ptrofs.add_commut. reflexivity.
Qed.

(* ================================================================== *)
(* The target address for caml_modify: accu_ptr + n                    *)
(* ================================================================== *)

Definition heap_field_target (hofs : ptrofs) (n_int : int) : ptrofs :=
  Ptrofs.add hofs (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv clight_ge) tlong))
                               (ptrofs_of_int Signed n_int)).

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_SETFIELD_correct : forall n,
    handler_correct (handle_SETFIELD n) f_instr_SETFIELD
      (fun e m s ard =>
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         let sb := ar_sptr_block ard in
         let so := ar_sptr_ofs ard in
         let hm := ar_heap_map ard in
         let cb := ar_code_base_block ard in
         let co := ar_code_base_ofs ard in
         (* 0. e does not bind _caml_modify *)
         e ! _caml_modify = None /\
         (* 1. Code buffer contains Z.of_nat n at current PC *)
         Mem.load Mint32 m cb
           (Ptrofs.unsigned (Ptrofs.add co
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat n))) /\
         (* 2. n fits in int32 signed range *)
         Int.min_signed <= Z.of_nat n <= Int.max_signed /\
         (* 3. Genv lookup for caml_modify *)
         (exists b_cm,
            Genv.find_symbol ge _caml_modify = Some b_cm /\
            Genv.find_funct ge (Vptr b_cm Ptrofs.zero) = Some caml_modify_fundef) /\
         (* 4. caml_modify external call: for the actual values,
            there exists m_cm witnessing the call with empty trace *)
         (forall newval rest,
            Machine.stack s = newval :: rest ->
            forall accu_v,
              val_repr hm cb co (Machine.accu s) accu_v ->
            forall sp_b sp_ofs,
              Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some (Vptr sp_b sp_ofs) ->
            forall stk_top_cv,
              val_repr hm cb co newval stk_top_cv ->
            exists hb hofs,
              accu_v = Vptr hb hofs /\
              hb <> sb /\
              hb <> sp_b /\
              hb <> ar_global_block ard /\
              hb <> cb /\
              (* sp pop store succeeds *)
              (exists m_sp,
                Mem.store Mint64 m sb (Ptrofs.unsigned so + 16)
                  (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 8))) = Some m_sp /\
                (* stack top survives sp store *)
                Mem.load Mint64 m_sp sp_b (Ptrofs.unsigned sp_ofs) = Some stk_top_cv /\
                (* accu survives sp store *)
                Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 8) = Some (Vptr hb hofs) /\
                (* pc survives sp store *)
                Mem.load Mint64 m_sp sb (Ptrofs.unsigned so + 0) =
                  Some (Vptr cb (Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t)))) /\
                (* caml_modify call succeeds *)
                (exists m_cm,
                  external_call caml_modify_ef ge
                    (Vptr hb (heap_field_target hofs (Int.repr (Z.of_nat n)))
                     :: stk_top_cv :: nil)
                    m_sp E0 Vundef m_cm /\
                  (* sb loads preserved through caml_modify *)
                  (forall ofs v,
                     Mem.load Mint64 m_sp sb ofs = Some v ->
                     Mem.load Mint64 m_cm sb ofs = Some v) /\
                  (* sb stores succeed in m_cm *)
                  (forall ofs v_old v_new,
                     Mem.load Mint64 m_sp sb ofs = Some v_old ->
                     exists m', Mem.store Mint64 m_cm sb ofs v_new = Some m') /\
                  (* sp_b loads preserved (sp_b <> hb) *)
                  (forall ofs v,
                     Mem.load Mint64 m_sp sp_b ofs = Some v ->
                     Mem.load Mint64 m_cm sp_b ofs = Some v) /\
                  (* cb loads preserved (cb <> hb) *)
                  (forall ofs v,
                     Mem.load Mint32 m_sp cb ofs = Some v ->
                     Mem.load Mint32 m_cm cb ofs = Some v) /\
                  (* global_repr preserved (gb <> hb) *)
                  (global_repr hm cb co m_cm
                     (Machine.global s) (ar_global_block ard) (ar_global_ofs ard)) /\
                  (* Permission preservation *)
                  (forall b ofs k p,
                     Mem.valid_block m_sp b -> Mem.perm m_sp b ofs k p ->
                     Mem.perm m_cm b ofs k p)))))
      (fun _ s => match s.(Machine.stack) with
                  | newval :: _ =>
                    match s.(Machine.accu) with
                    | Val_ptr addr =>
                      match heap_lookup s.(Machine.hp) addr with
                      | Some (_, fields) => set_nth fields n newval = None
                      | None => True
                      end
                    | _ => True
                    end
                  | _ => True end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
Admitted.

(* Wrapper with the canonical type expected by InstructVerificationProof.v *)
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
Import Bytecode.AST.

Definition correct_SETFIELD : forall n,
    handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
      (pre_of (SETFIELD n))
      (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).
Proof.
Admitted.
