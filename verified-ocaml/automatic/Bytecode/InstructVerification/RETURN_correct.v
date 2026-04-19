(* RETURN_correct.v -- RETURN handler completeness proof.

   RETURN stacksize:
   - Rocq: handle_RETURN stacksize s =
       let stk = skipn stacksize (stack s) in
       if Nat.ltb 0 (extra_args s) then
         match get_code_ptr_s s (accu s) with
         | Some target_pc =>
           Step (s <|pc := target_pc|> <|stack := stk|> <|env := accu s|>
                   <|extra_args := Nat.sub (extra_args s) 1|>)
         | None => Error "RETURN: accu is not a closure"
         end
       else
         match stk with
         | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
           Step (s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                   <|extra_args := Z.to_nat saved_ea|>)
         | _ => Error "RETURN: malformed return frame"
         end

   C code (f_instr_RETURN):
     Preamble: read pc, advance pc, read sp, read n from code, sp += n
     if extra_args > 0 then
       extra_args -= 1
       pc = code_ptr from accu closure field 0
       env = accu
     else
       pc = cast sp[0] to code_t ptr
       env = sp[1]
       extra_args = sp[2] >> 1
       sp += 3
     return 0

   Both Step branches proved with real preconditions.
   NO AXIOMS, NO Admitted. *)

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

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.sub Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Struct layout                                                       *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _env (co_members co) = Errors.OK (24, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split; [| split; [| split; [| split]]]]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_return : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _accu (co_members co) = Errors.OK (8, Full) /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _env (co_members co) = Errors.OK (24, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

(* sem_cast for tlong -> (tptr (tptr tint)) when value is Vptr *)
Local Lemma sem_cast_long_to_ptptint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr (tptr tint)) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr (tptr tint)) + 0 *)
Local Lemma sem_add_ptptint_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr (tptr tint)) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr (tptr tint)) tint) with (add_case_pi (tptr tint) Signed).
  unfold sem_add_ptr_int.
  change (sizeof (genv_cenv clight_ge) (tptr tint)) with 8%Z.
  f_equal. f_equal.
  unfold ptrofs_of_int.
  change (Ptrofs.of_ints (Int.repr 0)) with Ptrofs.zero.
  rewrite Ptrofs.mul_zero, Ptrofs.add_zero. reflexivity.
Qed.

(* sem_cast for (tptr tint) -> (tptr tint) is identity *)
Local Lemma sem_cast_ptr_tint_to_ptr_tint : forall b ofs m,
  sem_cast (Vptr b ofs) (tptr tint) (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_cast for tlong -> (tptr tint) when value is Vptr (x86-64 cast_case_pointer) *)
Local Lemma sem_cast_long_to_ptr_tint_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tint) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + tint n *)
Local Lemma sem_add_sp_n : forall sp_b sp_ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong)
    (Vint n) tint
    m = Some (Vptr sp_b (Ptrofs.add sp_ofs
                (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 2 *)
Local Lemma sem_add_sp_2 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 2)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 16))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 3 *)
Local Lemma sem_add_sp_3 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 3)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 24))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sem_add for (tptr tint) + 1 = ofs + 4 (code pointer advance) *)
Local Lemma sem_add_ptr_int_1 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tint) (Vint (Int.repr 1)) tint m
    = Some (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tint) tint) with (add_case_pi tint Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* Ogt on tlong vs tint: CompCert promotes tint to tlong (signed),
   then does Int64.cmp Cgt = Int64.lt (rhs) (lhs) *)
Local Lemma sem_gt_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Ogt
    (Vlong n1) tlong (Vint n2) tint m
    = Some (Val.of_bool (Int64.lt (Int64.repr (Int.signed n2)) n1)).
Proof.
  intros. unfold sem_binary_operation, sem_cmp.
  change (classify_cmp tlong tint) with cmp_default. simpl.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed). simpl.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true. simpl.
  reflexivity.
Qed.

(* Ogt extra_args > 0 corresponds to Nat.ltb 0 (extra_args s) *)
Local Lemma return_gt_iff : forall ea,
  Z.of_nat ea <= Int64.max_signed ->
  Int64.lt (Int64.repr (Int.signed (Int.repr 0))) (Int64.repr (Z.of_nat ea))
  = Nat.ltb 0 ea.
Proof.
  intros ea Hea.
  change Int64.max_signed with 9223372036854775807 in Hea.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Int64.lt.
  rewrite (Int64.signed_repr 0).
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807. lia. }
  rewrite Int64.signed_repr.
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807. lia. }
  destruct ea as [| ea'].
  - simpl. reflexivity.
  - change (Nat.ltb 0 (S ea')) with true.
    destruct (zlt 0 (Z.of_nat (S ea'))) as [Hlt | Hlt].
    + reflexivity.
    + exfalso. lia.
Qed.

(* Oshr for tlong >> tint(1) *)
Local Lemma sem_shr_long_int_1 : forall n m,
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m
  = Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros. unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl. reflexivity.
Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof. intros. destruct b; reflexivity. Qed.

(* ================================================================== *)
(* Ptrofs arithmetic                                                   *)
(* ================================================================== *)

Local Lemma ptrofs_max_unsigned_large : (Ptrofs.max_unsigned >= 2^32)%Z.
Proof. vm_compute. discriminate. Qed.

Local Lemma ptrofs_mul_8_of_ints_eq : forall n,
  0 <= n ->
  n < Int.half_modulus ->
  Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed (Int.repr n))
  = Ptrofs.repr (n * 8).
Proof.
  intros n Hnn Hn_bound.
  unfold ptrofs_of_int, Ptrofs.of_ints.
  change Int.half_modulus with 2147483648 in Hn_bound.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647. lia. }
  unfold Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr 8).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  rewrite (Ptrofs.unsigned_repr n).
  2: { pose proof ptrofs_max_unsigned_large. lia. }
  f_equal. lia.
Qed.

Local Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Local Lemma ptrofs_add_zero : forall ofs,
  Ptrofs.add ofs (Ptrofs.repr 0) = ofs.
Proof.
  intros. rewrite Ptrofs.add_zero. reflexivity.
Qed.

Local Lemma stack_repr_skipn : forall n hm cb co m stk sp_b sp_ofs,
  stack_repr hm cb co m stk sp_b sp_ofs ->
  stack_repr hm cb co m (skipn n stk) sp_b
    (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat n * 8))).
Proof.
  induction n as [| n' IH]; intros hm0 cb0 co0 m0 stk0 sp_b0 sp_ofs0 Hsr.
  - simpl. rewrite ptrofs_add_zero. exact Hsr.
  - destruct stk0 as [| v vs].
    + simpl. constructor.
    + simpl skipn. inversion Hsr; subst.
      specialize (IH hm0 cb0 co0 m0 vs sp_b0 (Ptrofs.add sp_ofs0 (Ptrofs.repr 8)) H5).
      replace (Ptrofs.add sp_ofs0 (Ptrofs.repr (Z.of_nat (S n') * 8)))
        with (Ptrofs.add (Ptrofs.add sp_ofs0 (Ptrofs.repr 8)) (Ptrofs.repr (Z.of_nat n' * 8))).
      { exact IH. }
      { rewrite Ptrofs.add_assoc. f_equal.
        rewrite ptrofs_add_repr. f_equal. lia. }
Qed.

(* return_tailcall_pre and return_frame_pre are defined in InstructSpec.v *)

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_RETURN_correct : forall stacksize,
    handler_correct (fun _ => handle_RETURN stacksize) f_instr_RETURN
      (fun _ m s ard =>
         (* Common preamble: code buffer has stacksize at current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat stacksize))) /\
         (* stacksize fits in int32 signed range *)
         Z.of_nat stacksize < Int.half_modulus /\
         (* extra_args fits in Int64 signed range *)
         Z.of_nat (extra_args s) <= Int64.max_signed /\
         (* sp + stacksize * 8 fits in ptrofs *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus) /\
         (* stacksize <= length of stack *)
         (stacksize <= Datatypes.length (Machine.stack s))%nat /\
         (* Then-branch precondition: closure code pointer *)
         (Nat.ltb 0 (extra_args s) = true ->
          forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            return_tailcall_pre m s ard sp_b) /\
         (* Else-branch precondition: return frame *)
         (Nat.ltb 0 (extra_args s) = false ->
          forall sp_b sp_ofs ret_pc saved_env saved_ea rest,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            skipn stacksize (Machine.stack s) =
              Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest ->
            return_frame_pre m s ard sp_b
              (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))
              ret_pc saved_env saved_ea rest))
      (* Error predicates *)
      (fun msg _ => msg = "RETURN: accu is not a closure"%string \/
                    msg = "RETURN: malformed return frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro stacksize.
  intros e le m s.
  unfold handle_RETURN.
  set (stk := skipn stacksize (Machine.stack s)).

  destruct (Nat.ltb 0 (extra_args s)) eqn:Hltb.

  (* ================================================================ *)
  (* Case 1: extra_args > 0  (tail-call)                              *)
  (* ================================================================ *)
  {
    destruct (get_code_ptr_s s (Machine.accu s)) eqn:Hgcp.

    (* Sub-case 1a: get_code_ptr_s = Some z => Step (tail-call) *)
    {
      intros ard Hpre Hstep_pre.

      destruct Hpre as (Hle_s &
        [pc_ptr [Hpc_load Hpc_rel]] &
        [accu_v [Haccu_load Haccu_repr]] &
        [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
        [env_v [Henv_load Henv_repr]] &
        Hextra_load &
        [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
        [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
      subst sp_ptr.

      set (sb := ar_sptr_block ard) in *.
      set (so := ar_sptr_ofs ard) in *.
      set (hm := ar_heap_map ard) in *.
      set (cb := ar_code_base_block ard) in *.
      set (co := ar_code_base_ofs ard) in *.
      destruct Hstep_pre as (Hcode_load & Hslot_bound & Hea_signed & Hsp_fits & Hslot_le_len & Htailcall_pre & _).

      pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
      pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
      pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

      destruct interp_state_co_return as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset Hextra_offset]]]]]].

      unfold pc_rel in Hpc_rel. subst pc_ptr.
      set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

      (* Get closure code pointer info *)
      pose proof (Htailcall_pre eq_refl sp_b sp_ofs Hsp_load) as Htcp.
      unfold return_tailcall_pre in Htcp.
      destruct (Htcp z Hgcp accu_v Haccu_repr)
        as [accu_b [accu_ofs [code_b [code_ofs
            [Haccu_is_ptr [Hcode_ptr_load [Haccu_ne_sb [Haccu_ne_cb
            [Haccu_ne_spb [new_co [Hcode_ofs_eq Hcode_b_eq]]]]]]]]]]].
      clear Htcp Htailcall_pre.
      subst accu_v code_b.

      (* Compute new sp: sp + stacksize *)
      assert (Hsp_fits_concrete : Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus).
      { apply (Hsp_fits sp_b sp_ofs). exact Hsp_load. }

      set (stacksize_int := Int.repr (Z.of_nat stacksize)).
      set (new_sp_ofs := Ptrofs.add sp_ofs
             (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed stacksize_int))).

      assert (Hnew_sp_eq : new_sp_ofs = Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8))).
      { unfold new_sp_ofs, stacksize_int.
        rewrite (ptrofs_mul_8_of_ints_eq (Z.of_nat stacksize) ltac:(lia) Hslot_bound).
        reflexivity. }

      assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs =
                Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8).
      { rewrite Hnew_sp_eq. rewrite ptrofs_add_unsigned; lia. }

      set (new_pc_v := Vptr cb code_ofs).
      set (new_env_v := Vptr accu_b accu_ofs).

      (* Store 1: pc field at (sb, uso+0) <- advanced pc (pc + 1 code slot) *)
      set (advanced_pc := Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4))).
      destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia)
                  advanced_pc)
        as [m1 Hstore1].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

      (* Store 2: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
      assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                 advanced_pc (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
      destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs)
                  Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia)
                  (Vptr sp_b new_sp_ofs))
        as [m2 Hstore2].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.

      (* Store 3: extra_args field at (sb, uso+32) <- extra_args - 1 *)
      assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                   advanced_pc _ Hstore1 Hextra_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
                 (Vptr sp_b new_sp_ofs) _ Hstore2 Hm1). right. lia. }
      set (new_extra := Vlong (Int64.sub (Int64.repr (Z.of_nat (extra_args s))) (Int64.repr 1))).
      destruct (store_succeeds_sb m2 sb so 32 (Vlong (Int64.repr (Z.of_nat (extra_args s))))
                  Hsb_writable_m2 Hextra_load_m2 ltac:(lia) ltac:(lia) new_extra)
        as [m3 Hstore3].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

      (* Store 4: pc field at (sb, uso+0) <- new_pc_v (closure code pointer) *)
      assert (Hpc_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) =
                Some advanced_pc).
      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some advanced_pc).
        { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) advanced_pc Hstore1) as Htmp.
          unfold advanced_pc in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
          exact Htmp. }
        assert (Hpc_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) = Some advanced_pc).
        { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
                   (Vptr sp_b new_sp_ofs) advanced_pc Hstore2 Hpc_m1). left. lia. }
        apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 0)
                 new_extra advanced_pc Hstore3 Hpc_m2). left. lia. }
      destruct (store_succeeds_sb m3 sb so 0 advanced_pc
                  Hsb_writable_m3 Hpc_load_m3 ltac:(lia) ltac:(lia) new_pc_v)
        as [m4 Hstore4].
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4 Hsb_writable_m3) as Hsb_writable_m4.

      (* Store 5: env field at (sb, uso+24) <- new_env_v *)
      assert (Henv_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                   advanced_pc env_v Hstore1 Henv_load). right. lia. }
        assert (Henv_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
        { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
                   (Vptr sp_b new_sp_ofs) env_v Hstore2 Henv_m1). right. lia. }
        assert (Henv_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
        { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
                   new_extra env_v Hstore3 Henv_m2). left. lia. }
        apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                 new_pc_v env_v Hstore4 Henv_m3). right. lia. }
      destruct (store_succeeds_sb m4 sb so 24 env_v
                  Hsb_writable_m4 Henv_load_m4 ltac:(lia) ltac:(lia) new_env_v)
        as [m5 Hstore5].

      (* Intermediate load facts *)
      (* accu in m1 *)
      assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
                 advanced_pc (Vptr accu_b accu_ofs) Hstore1 Haccu_load). right. lia. }

      (* accu in m2 *)
      assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
                 (Vptr sp_b new_sp_ofs) (Vptr accu_b accu_ofs) Hstore2 Haccu_load_m1). left. lia. }

      (* accu in m3 *)
      assert (Haccu_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 8)
                 new_extra (Vptr accu_b accu_ofs) Hstore3 Haccu_load_m2). left. lia. }

      (* extra_args in m2 *)
      assert (Hextra_load_m2' : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { exact Hextra_load_m2. }

      (* extra_args in m3: written *)
      assert (Hextra_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) = Some new_extra).
      { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 32) new_extra Hstore3) as Htmp.
        unfold new_extra in Htmp. simpl Val.load_result in Htmp. exact Htmp. }

      (* code buffer in m1 *)
      assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
                Some (Vint stacksize_int)).
      { erewrite Mem.load_store_other. exact Hcode_load. exact Hstore1.
        left. exact Hcb_ne. }

      (* sp load in m2: written *)
      assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore2) as Htmp.
        simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

      (* sp in m3 *)
      assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
                Some (Vptr sp_b new_sp_ofs)).
      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
                 new_extra (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). left. lia. }

      (* code ptr from closure in m1 *)
      assert (Hcode_ptr_load_m1 : Mem.load Mptr m1 accu_b (Ptrofs.unsigned accu_ofs) =
                Some (Vptr cb code_ofs)).
      { erewrite Mem.load_store_other. exact Hcode_ptr_load. exact Hstore1.
        left. exact Haccu_ne_sb. }

      (* code ptr from closure in m2 *)
      assert (Hcode_ptr_load_m2 : Mem.load Mptr m2 accu_b (Ptrofs.unsigned accu_ofs) =
                Some (Vptr cb code_ofs)).
      { erewrite Mem.load_store_other. exact Hcode_ptr_load_m1. exact Hstore2.
        left. intro Heq; apply Haccu_ne_sb; auto. }

      (* code ptr from closure in m3 *)
      assert (Hcode_ptr_load_m3 : Mem.load Mptr m3 accu_b (Ptrofs.unsigned accu_ofs) =
                Some (Vptr cb code_ofs)).
      { erewrite Mem.load_store_other. exact Hcode_ptr_load_m2. exact Hstore3.
        left. exact Haccu_ne_sb. }

      (* accu in m4 *)
      assert (Haccu_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) =
                Some (Vptr accu_b accu_ofs)).
      { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
                 new_pc_v (Vptr accu_b accu_ofs) Hstore4 Haccu_load_m3). right. lia. }

      (* Witnesses *)
      set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
      set (le2 := PTree.set _t'14 (Vptr sp_b sp_ofs) le1).
      set (le3 := PTree.set _t'15 (Vint stacksize_int) le2).
      set (le4 := PTree.set _t'2 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le3).
      set (le5 := PTree.set _t'13 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le4).
      set (le6 := PTree.set _t'11 (Vptr accu_b accu_ofs) le5).
      set (le7 := PTree.set _t'12 (Vptr cb code_ofs) le6).
      set (le8 := PTree.set _t'10 (Vptr accu_b accu_ofs) le7).
      set (le_final := le8).

      exists le_final. exists m5.
      exists (Out_return (Some (Vint (Int.repr 0), tint))).

      split.

      (* ================================================================ *)
      (* Part 1: exec -- the C body executes                               *)
      (* ================================================================ *)
      {
        (* Decomposed bigstep proof -- split at Ssequence boundaries *)
        (* Body = Ssequence PREAMBLE (Ssequence (Ssequence S6 IF) SRETURN) *)
        apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m2).

        (* PREAMBLE: Ssequence (Ssequence S1 S2) (Ssequence S3 (Ssequence S4 S5)) *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).
          (* S1;S2: read pc, advance pc *)
          { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
            (* S1: Sset _t'1 (s->pc) *)
            rewrite Hle_s; eval_cbn.
            rewrite Hco; eval_cbn.
            rewrite Hpc_offset; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
            rewrite Hpc_load; eval_cbn.
            (* S2: Sassign (s->pc) (_t'1+1) -- rvalue _t'1 resolved first *)
            rewrite PTree.gss; eval_cbn.
            (* lvalue needs _s through PTree.set _t'1 *)
            rewrite PTree.gso by (compute; congruence).
            rewrite Hle_s; eval_cbn.
            rewrite sem_add_ptr_int_1; eval_cbn.
            rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
            rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
            rewrite Mptr_Mint64; eval_cbn.
            fold advanced_pc.
            rewrite Hstore1; eval_cbn.
            reflexivity. }
          (* S3;S4;S5: read sp, read stacksize, sp += stacksize *)
          { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
            unfold le1.
            rewrite PTree.gso by (compute; congruence).
            rewrite Hle_s; eval_cbn.
            rewrite Hco; eval_cbn.
            rewrite Hsp_offset; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            rewrite Hsp_load_m1; eval_cbn.
            rewrite PTree.gso by (compute; congruence).
            rewrite PTree.gss; eval_cbn.
            rewrite Hcode_load_m1; eval_cbn.
            repeat (rewrite PTree.gso by (compute; congruence)).
            rewrite Hle_s; eval_cbn.
            (* Hsp_offset already applied globally; lvalue resolves via eval_cbn *)
            (* rvalue: read _t'14 and _t'15 from le *)
            rewrite PTree.gss; eval_cbn.
            rewrite PTree.gss; eval_cbn.
            fold stacksize_int.
            rewrite (sem_add_sp_n sp_b sp_ofs stacksize_int m1); eval_cbn.
            fold new_sp_ofs.
            rewrite sem_cast_ptr_to_ptr; eval_cbn.
            rewrite Mptr_Mint64; eval_cbn.
            rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
            rewrite Hstore2; eval_cbn.
            reflexivity. } }

        (* Ssequence (Ssequence S6 IF) SRETURN *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le8) (m1 := m5).
          (* Ssequence S6 IF *)
          { apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m2).
            (* S6: read extra_args *)
            { apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
              unfold le3, le2, le1.
              repeat (rewrite PTree.gso by (compute; congruence)).
              rewrite Hle_s; eval_cbn.
              rewrite Hco; eval_cbn.
              rewrite Hextra_offset; eval_cbn.
              rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
              rewrite Hextra_load_m2; eval_cbn.
              reflexivity. }
            (* Sifthenelse: condition true, then branch *)
            { eapply exec_Sifthenelse.
              - (* eval condition: Ogt _t'2 0 *)
                eapply eval_Ebinop.
                + eapply eval_Etempvar. unfold le4. rewrite PTree.gss. reflexivity.
                + eapply eval_Econst_int.
                + exact (sem_gt_long_int (Int64.repr (Z.of_nat (extra_args s)))
                           (Int.repr 0) m2).
              - (* bool_val *)
                rewrite (return_gt_iff (extra_args s) Hea_signed).
                rewrite Hltb. exact (bool_val_of_bool true m2).
              - (* then branch body *)
                simpl.
                (* Then = Ssequence (T1;T2) (Ssequence (T3;T4;T5) (T6;T7)) *)
                apply exec_Sseq_1 with (t1 := E0) (le1 := le5) (m1 := m3).
                (* T1;T2: read extra_args, extra_args -= 1 *)
                { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
                  unfold le4, le3, le2, le1.
                  repeat (rewrite PTree.gso by (compute; congruence)).
                  rewrite Hle_s; eval_cbn.
                  rewrite Hco; eval_cbn.
                  rewrite Hextra_offset; eval_cbn.
                  rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                  rewrite Hextra_load_m2; eval_cbn.
                  repeat (rewrite PTree.gso by (compute; congruence)).
                  rewrite Hle_s; eval_cbn.
                  rewrite PTree.gss; eval_cbn.
                  rewrite (sem_sub_long_int (Int64.repr (Z.of_nat (extra_args s))) m2); eval_cbn.
                  rewrite sem_cast_long_vlong; eval_cbn.
                  fold new_extra.
                  rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                  rewrite Hstore3; eval_cbn.
                  reflexivity. }
                (* Ssequence (T3;T4;T5) (T6;T7) *)
                { apply exec_Sseq_1 with (t1 := E0) (le1 := le7) (m1 := m4).
                  (* T3;T4;T5: read accu, code ptr, store new pc *)
                  { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
                    unfold le5, le4, le3, le2, le1.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Hco; eval_cbn.
                    rewrite Haccu_offset; eval_cbn.
                    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                    rewrite Haccu_load_m3; eval_cbn.
                    rewrite PTree.gss; eval_cbn.
                    rewrite sem_cast_long_to_ptptint_vptr; eval_cbn.
                    rewrite (sem_add_ptptint_0 accu_b accu_ofs m3); eval_cbn.
                    rewrite Mptr_Mint64; eval_cbn.
                    rewrite Mptr_Mint64 in Hcode_ptr_load_m3.
                    rewrite Hcode_ptr_load_m3; eval_cbn.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Hpc_offset; eval_cbn.
                    rewrite PTree.gss; eval_cbn.
                    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
                    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                    rewrite Mptr_Mint64; eval_cbn.
                    fold new_pc_v.
                    rewrite Hstore4; eval_cbn.
                    reflexivity. }
                  (* T6;T7: read accu, store env *)
                  { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
                    unfold le7, le6, le5, le4, le3, le2, le1.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Hco; eval_cbn.
                    rewrite Haccu_offset; eval_cbn.
                    rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).
                    rewrite Haccu_load_m4; eval_cbn.
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Henv_offset; eval_cbn.
                    rewrite PTree.gss; eval_cbn.
                    rewrite (sem_cast_long_vptr accu_b accu_ofs m4); eval_cbn.
                    rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
                    fold new_env_v.
                    rewrite Hstore5; eval_cbn.
                    reflexivity. } } } }
          (* Sreturn 0 *)
          { apply exec_Sreturn_some. eapply eval_Econst_int. } }
      }

      (* ================================================================ *)
      (* Part 2: abs_rel for post-state                                    *)
      (* ================================================================ *)
      {
        set (uso := Ptrofs.unsigned so) in *.
        set (ard' := mk_abs_rel sb so hm cb new_co
                       (ar_global_block ard) (ar_global_ofs ard)
                       (ar_stack_block ard) (ar_stack_base_ofs ard)
                       (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                       (ar_sptr_ofs_bound ard)).
        exists ard'.

        (* Loads in final memory m5 *)

        (* pc at uso+0: written in store4, survived store5 at +24 *)
        assert (Hpc_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
        { assert (Hpc_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
          { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore4) as Htmp.
            unfold new_pc_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
            exact Htmp. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
                   new_env_v new_pc_v Hstore5 Hpc_m4). left. lia. }

        (* accu at uso+8: unaffected by all stores *)
        assert (Haccu_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) =
                  Some (Vptr accu_b accu_ofs)).
        { assert (Haccu_m5 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) =
                    Some (Vptr accu_b accu_ofs)).
          { exact Haccu_load_m4. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 8)
                   new_env_v (Vptr accu_b accu_ofs) Hstore5 Haccu_m5). left. lia. }

        (* sp at uso+16: written in store2, survived stores 3,4,5 *)
        assert (Hsp_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) =
                  Some (Vptr sp_b new_sp_ofs)).
        { assert (Hsp_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
                    Some (Vptr sp_b new_sp_ofs)).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                     new_pc_v (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3). right. lia. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                   new_env_v (Vptr sp_b new_sp_ofs) Hstore5 Hsp_m4). left. lia. }

        (* env at uso+24: written in store5 *)
        assert (Henv_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some new_env_v).
        { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so + 24) new_env_v Hstore5) as Htmp.
          unfold new_env_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
          exact Htmp. }

        (* extra_args at uso+32: written in store3, survived 4,5 *)
        assert (Hextra_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) = Some new_extra).
        { assert (Hextra_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) = Some new_extra).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                     new_pc_v new_extra Hstore4 Hextra_m3). right. lia. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
                   new_env_v new_extra Hstore5 Hextra_m4). right. lia. }

        (* global_data at uso+40 *)
        assert (Hgd_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
        { assert (Hgd_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                     advanced_pc gd_ptr Hstore1 Hgd_load). right. lia. }
          assert (Hgd_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                     (Vptr sp_b new_sp_ofs) gd_ptr Hstore2 Hgd_m1). right. lia. }
          assert (Hgd_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
                     new_extra gd_ptr Hstore3 Hgd_m2). right. lia. }
          assert (Hgd_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                     new_pc_v gd_ptr Hstore4 Hgd_m3). right. lia. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
                   new_env_v gd_ptr Hstore5 Hgd_m4). right. lia. }

        (* trap_sp at uso+48 *)
        assert (Hts_load5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
        { assert (Hts_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                     advanced_pc ts_ptr Hstore1 Hts_load). right. lia. }
          assert (Hts_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                     (Vptr sp_b new_sp_ofs) ts_ptr Hstore2 Hts_m1). right. lia. }
          assert (Hts_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
                     new_extra ts_ptr Hstore3 Hts_m2). right. lia. }
          assert (Hts_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                     new_pc_v ts_ptr Hstore4 Hts_m3). right. lia. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
                   new_env_v ts_ptr Hstore5 Hts_m4). right. lia. }

        (* sb_writable in m5 *)
        assert (Hsb_writable_m5 : Mem.range_perm m5 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
        { intros ofs' Hofs'.
          eapply Mem.perm_store_1. exact Hstore5.
          eapply Mem.perm_store_1. exact Hstore4.
          eapply Mem.perm_store_1. exact Hstore3.
          eapply Mem.perm_store_1. exact Hstore2.
          eapply Mem.perm_store_1. exact Hstore1.
          apply Hsb_writable. exact Hofs'. }

        (* Stack repr for post-state: skipn stacksize (stack s) *)
        assert (Hstack_m5 :
          stack_repr hm cb co m5 stk sp_b new_sp_ofs).
        { unfold stk. rewrite Hnew_sp_eq.
          apply (stack_repr_store_other_block hm cb co m4 m5 _ sp_b _ sb (Ptrofs.unsigned so + 24) new_env_v).
          - apply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b _ sb (Ptrofs.unsigned so + 0) new_pc_v).
            + apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b _ sb (Ptrofs.unsigned so + 32) new_extra).
              * apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b _ sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b _ sb (Ptrofs.unsigned so + 0) advanced_pc).
                  { exact (stack_repr_skipn stacksize hm cb co m (Machine.stack s) sp_b sp_ofs Hstack_repr). }
                  { exact Hstore1. }
                  { intro Heq; apply Hsp_ne_sb; auto. } }
                { exact Hstore2. }
                { intro Heq; apply Hsp_ne_sb; auto. }
              * exact Hstore3.
              * intro Heq; apply Hsp_ne_sb; auto.
            + exact Hstore4.
            + intro Heq; apply Hsp_ne_sb; auto.
          - exact Hstore5.
          - intro Heq; apply Hsp_ne_sb; auto.
        }

        (* le_final ! _s *)
        assert (Hle_final_s : le_final ! _s = Some (Vptr sb so)).
        { subst le_final le8 le7 le6 le5 le4 le3 le2 le1.
          repeat (rewrite PTree.gso by (compute; congruence)).
          exact Hle_s. }

        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

        (* 1. _s is in le' *)
        { exact Hle_final_s. }

        (* 2. pc field *)
        { exists new_pc_v. split.
          - exact Hpc_load5.
          - simpl. unfold pc_rel, new_pc_v. f_equal.
            subst code_ofs. reflexivity. }

        (* 3. accu field *)
        { exists (Vptr accu_b accu_ofs). split.
          - exact Haccu_load5.
          - simpl. eapply val_repr_co_shift. eassumption. }

        (* 4. sp field *)
        { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
          - exact Hsp_load5.
          - reflexivity.
          - simpl stack. eapply stack_repr_co_shift. eassumption.
          - exact Hsp_ne_sb.
          - exact Hsp_ne_gb.
          - exact Hcb_ne_sp.
          - (* sp_ge8 *) rewrite Hnew_sp_unsigned. lia.
          - (* sp_rep *)
            simpl stack. unfold stk.
            rewrite length_skipn.
            rewrite Hnew_sp_unsigned. zify. lia.
          - (* sp_writable *)
            simpl stack. unfold stk.
            rewrite length_skipn.
            rewrite Hnew_sp_unsigned.
            replace (Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 +
                      8 * Z.of_nat (Datatypes.length (Machine.stack s) - stacksize))
              with (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (Datatypes.length (Machine.stack s))).
            2: { zify. lia. }
            intros ofs' Hofs'.
            eapply Mem.perm_store_1. exact Hstore5.
            eapply Mem.perm_store_1. exact Hstore4.
            eapply Mem.perm_store_1. exact Hstore3.
            eapply Mem.perm_store_1. exact Hstore2.
            eapply Mem.perm_store_1. exact Hstore1.
            apply Hsp_writable. exact Hofs'.
          - rewrite Hnew_sp_unsigned.
            apply Z.divide_add_r. exact Hsp_align. exists (Z.of_nat stacksize). simpl. lia. }

        (* 5. env field *)
        { exists new_env_v. split.
          - exact Henv_load5.
          - simpl. eapply val_repr_co_shift. eassumption. }

        (* 6. extra_args field *)
        { simpl.
          unfold new_extra in Hextra_load5.
          assert (Heq : Int64.sub (Int64.repr (Z.of_nat (extra_args s))) (Int64.repr 1) =
                        Int64.repr (Z.of_nat (Nat.sub (extra_args s) 1))).
          { apply Nat.ltb_lt in Hltb.
            destruct (extra_args s) as [| ea'] eqn:Hea_eq.
            - lia.
            - simpl. rewrite Nat.sub_0_r.
              change (Z.pos (Pos.of_succ_nat ea')) with (Z.of_nat (S ea')).
              rewrite <- Hea_eq.
              unfold Int64.sub. f_equal.
              rewrite !Int64.unsigned_repr
                by (change Int64.max_unsigned with 18446744073709551615;
                    change Int64.max_signed with 9223372036854775807 in Hea_signed; lia).
              lia. }
          rewrite Heq in Hextra_load5.
          exact Hextra_load5. }

        (* 7. global_data field *)
        { exists gd_ptr. split; [| split; [| split]].
          - exact Hgd_load5.
          - simpl. exact Hgd_eq.
          - simpl. eapply global_repr_co_shift.
            apply (global_repr_store_other_block hm cb co m4 m5 _
                     (ar_global_block ard) (ar_global_ofs ard)
                     sb (Ptrofs.unsigned so + 24) new_env_v).
            + apply (global_repr_store_other_block hm cb co m3 m4 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (Ptrofs.unsigned so + 0) new_pc_v).
              * apply (global_repr_store_other_block hm cb co m2 m3 _
                         (ar_global_block ard) (ar_global_ofs ard)
                         sb (Ptrofs.unsigned so + 32) new_extra).
                { apply (global_repr_store_other_block hm cb co m1 m2 _
                           (ar_global_block ard) (ar_global_ofs ard)
                           sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                  { apply (global_repr_store_other_block hm cb co m m1 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sb (Ptrofs.unsigned so + 0) advanced_pc).
                    exact Hglobal_repr. exact Hstore1.
                    intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
                  { exact Hstore2. }
                  { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). } }
                { exact Hstore3. }
                { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
              * exact Hstore4.
              * intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
            + exact Hstore5.
            + intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
          - exact Hgb_ne_sb. }

        (* 8. trap_sp field *)
        { exists ts_ptr. split.
          - exact Hts_load5.
          - simpl. exact Htrap_rel. }

        (* 9. sb_writable *)
        { exact Hsb_writable_m5. }
      }
    }

    (* Sub-case 1b: get_code_ptr_s = None => Error *)
    { left. reflexivity. }
  }

  (* ================================================================ *)
  (* Case 2: extra_args = 0  (return)                                  *)
  (* ================================================================ *)
  {
    destruct stk as [| v0 stk0] eqn:Hstk_eq.

    (* Sub-case 2a: stk = [] => Error "malformed return frame" *)
    { right. reflexivity. }

    (* stk = v0 :: stk0 *)
    destruct v0; try (right; reflexivity).

    (* v0 = Val_int z0: need to check deeper *)
    destruct stk0 as [| v1 stk1].
    + (* [Val_int z0] => Error *)
      right. reflexivity.
    + destruct stk1 as [| v2 stk2].
      * (* [Val_int z0; v1] => Error *)
        right. destruct v1; reflexivity.
      * (* [Val_int z0; v1; v2; ...] *)
        destruct v2; try (right; reflexivity).
        (* v2 = Val_int z0 => Step (return) *)
        (* stk = Val_int z0 :: v1 :: Val_int z0 :: stk2 *)
        intros ard Hpre Hstep_pre.

        destruct Hpre as (Hle_s &
          [pc_ptr [Hpc_load Hpc_rel]] &
          [accu_v [Haccu_load Haccu_repr]] &
          [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
          [env_v [Henv_load Henv_repr]] &
          Hextra_load &
          [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
          [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
        subst sp_ptr.

        set (sb := ar_sptr_block ard) in *.
        set (so := ar_sptr_ofs ard) in *.
        set (hm := ar_heap_map ard) in *.
        set (cb := ar_code_base_block ard) in *.
        set (co := ar_code_base_ofs ard) in *.
        destruct Hstep_pre as (Hcode_load & Hslot_bound & Hea_signed & Hsp_fits & Hslot_le_len & _ & Hreturn_pre).

        (* Get the return frame precondition *)
        pose proof (Hreturn_pre eq_refl sp_b sp_ofs z v1 z0 stk2 Hsp_load) as Hrfp.
        specialize (Hrfp eq_refl).
        unfold return_frame_pre in Hrfp.
        assert (Hstk_match : skipn stacksize (Machine.stack s) =
                  Val_int z :: v1 :: Val_int z0 :: stk2).
        { fold stk. exact Hstk_eq. }

        pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
        pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
        pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

        destruct interp_state_co_return as [co_is [Hco [Hpc_offset [Haccu_offset [Hsp_offset [Henv_offset Hextra_offset]]]]]].

        unfold pc_rel in Hpc_rel. subst pc_ptr.
        set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

        assert (Hsp_fits_concrete : Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8 < Ptrofs.modulus).
        { apply (Hsp_fits sp_b sp_ofs). exact Hsp_load. }

        set (stacksize_int := Int.repr (Z.of_nat stacksize)).
        set (new_sp_ofs := Ptrofs.add sp_ofs
               (Ptrofs.mul (Ptrofs.repr 8) (ptrofs_of_int Signed stacksize_int))).

        assert (Hnew_sp_eq : new_sp_ofs = Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8))).
        { unfold new_sp_ofs, stacksize_int.
          rewrite (ptrofs_mul_8_of_ints_eq (Z.of_nat stacksize) ltac:(lia) Hslot_bound).
          reflexivity. }

        assert (Hnew_sp_unsigned : Ptrofs.unsigned new_sp_ofs =
                  Ptrofs.unsigned sp_ofs + Z.of_nat stacksize * 8).
        { rewrite Hnew_sp_eq. rewrite ptrofs_add_unsigned; lia. }

        destruct Hrfp as
          ([ret_pc_b [ret_pc_ofs [Hload_sp0_ret Hpc_rel_ret]]] &
           [env_cv [Hload_sp1_env Henv_repr_ret]] &
           Hload_sp2_ea &
           Hea_nonneg & Hea_max & Hshr_eq &
           Hsp_24_fits & Hrest_fits).

        (* The final sp should be new_sp + 3 (24 bytes) *)
        set (final_sp_ofs := Ptrofs.add new_sp_ofs (Ptrofs.repr 24)).

        assert (Hnsp_24 : Ptrofs.unsigned new_sp_ofs + 24 < Ptrofs.modulus).
        { rewrite Hnew_sp_eq. exact Hsp_24_fits. }

        assert (Hfinal_sp_unsigned : Ptrofs.unsigned final_sp_ofs =
                  Ptrofs.unsigned new_sp_ofs + 24).
        { unfold final_sp_ofs. rewrite ptrofs_add_unsigned; [reflexivity | lia | lia]. }

        (* Store 1: pc field at (sb, uso+0) <- advanced pc *)
        set (advanced_pc := Vptr cb (Ptrofs.add pc_ofs (Ptrofs.repr 4))).
        destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia)
                    advanced_pc)
          as [m1 Hstore1].
        pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

        (* Store 2: sp field at (sb, uso+16) <- Vptr sp_b new_sp_ofs *)
        assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
                  Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                   advanced_pc (Vptr sp_b sp_ofs) Hstore1 Hsp_load). right. lia. }
        destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs)
                    Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia)
                    (Vptr sp_b new_sp_ofs))
          as [m2 Hstore2].
        pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore2 Hsb_writable_m1) as Hsb_writable_m2.

        (* sp load in m2: written *)
        assert (Hsp_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 16) =
                  Some (Vptr sp_b new_sp_ofs)).
        { pose proof (load_after_store_same m1 m2 sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs) Hstore2) as Htmp.
          simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

        (* Store 3: pc field at (sb, uso+0) <- ret_pc code pointer *)
        set (new_pc_v := Vptr ret_pc_b ret_pc_ofs).
        assert (Hpc_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 0) =
                  Some advanced_pc).
        { assert (Hpc_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 0) = Some advanced_pc).
          { pose proof (load_after_store_same m m1 sb (Ptrofs.unsigned so + 0) advanced_pc Hstore1) as Htmp.
            unfold advanced_pc in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
            exact Htmp. }
          apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
                   (Vptr sp_b new_sp_ofs) advanced_pc Hstore2 Hpc_m1). left. lia. }
        destruct (store_succeeds_sb m2 sb so 0 advanced_pc
                    Hsb_writable_m2 Hpc_load_m2 ltac:(lia) ltac:(lia) new_pc_v)
          as [m3 Hstore3].
        pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore3 Hsb_writable_m2) as Hsb_writable_m3.

        (* Store 4: env field at (sb, uso+24) <- env_cv from return frame *)
        assert (Henv_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 24) = Some env_v).
        { assert (Henv_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 24) = Some env_v).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                     advanced_pc env_v Hstore1 Henv_load). right. lia. }
          assert (Henv_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 24) = Some env_v).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
                     (Vptr sp_b new_sp_ofs) env_v Hstore2 Henv_m1). right. lia. }
          apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 24)
                   new_pc_v env_v Hstore3 Henv_m2). right. lia. }
        destruct (store_succeeds_sb m3 sb so 24 env_v
                    Hsb_writable_m3 Henv_load_m3 ltac:(lia) ltac:(lia) env_cv)
          as [m4 Hstore4].
        pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore4 Hsb_writable_m3) as Hsb_writable_m4.

        (* Store 5: extra_args field at (sb, uso+32) <- shr(tagged_ea, 1) *)
        set (new_extra := Vlong (Int64.shr (Int64.repr (z0 * 2 + 1)) (Int64.repr 1))).
        assert (Hextra_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
                    Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                     advanced_pc _ Hstore1 Hextra_load). right. lia. }
          assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
                    Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
                     (Vptr sp_b new_sp_ofs) _ Hstore2 Hm1). right. lia. }
          assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 32) =
                    Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                     new_pc_v _ Hstore3 Hm2). right. lia. }
          apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 32)
                   env_cv _ Hstore4 Hm3). right. lia. }
        destruct (store_succeeds_sb m4 sb so 32 (Vlong (Int64.repr (Z.of_nat (extra_args s))))
                    Hsb_writable_m4 Hextra_load_m4 ltac:(lia) ltac:(lia) new_extra)
          as [m5 Hstore5].
        pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore5 Hsb_writable_m4) as Hsb_writable_m5.

        (* Store 6: sp field at (sb, uso+16) <- Vptr sp_b final_sp_ofs *)
        assert (Hsp_load_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 16) =
                  Some (Vptr sp_b new_sp_ofs)).
        { assert (Hsp_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
                    Some (Vptr sp_b new_sp_ofs)).
          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                     new_pc_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
          assert (Hsp_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
                    Some (Vptr sp_b new_sp_ofs)).
          { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                     env_cv (Vptr sp_b new_sp_ofs) Hstore4 Hsp_m3). left. lia. }
          apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 16)
                   new_extra (Vptr sp_b new_sp_ofs) Hstore5 Hsp_m4). left. lia. }
        destruct (store_succeeds_sb m5 sb so 16 (Vptr sp_b new_sp_ofs)
                    Hsb_writable_m5 Hsp_load_m5 ltac:(lia) ltac:(lia)
                    (Vptr sp_b final_sp_ofs))
          as [m6 Hstore6].

        (* Intermediate load facts for the else branch execution *)

        (* code buffer in m1 *)
        assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
                  Some (Vint stacksize_int)).
        { erewrite Mem.load_store_other. exact Hcode_load. exact Hstore1.
          left. exact Hcb_ne. }

        (* extra_args in m2 *)
        assert (Hextra_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 32) =
                  Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
        { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
                    Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 32)
                     advanced_pc _ Hstore1 Hextra_load). right. lia. }
          apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
                   (Vptr sp_b new_sp_ofs) _ Hstore2 Hm1). right. lia. }

        (* sp[0] ret_pc load in m2: stack data survived stores 1,2 (different block) *)
        assert (Hload_sp0_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs) =
                  Some (Vptr ret_pc_b ret_pc_ofs)).
        { assert (Hm1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned new_sp_ofs) =
                    Some (Vptr ret_pc_b ret_pc_ofs)).
          { erewrite Mem.load_store_other. 2: exact Hstore1.
            { rewrite <- Hnew_sp_eq in Hload_sp0_ret. exact Hload_sp0_ret. }
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm1. exact Hstore2.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        (* sp[1] env load in m2 *)
        assert (Hload_sp1_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs + 8) =
                  Some env_cv).
        { assert (Hm1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned new_sp_ofs + 8) =
                    Some env_cv).
          { erewrite Mem.load_store_other. 2: exact Hstore1.
            { rewrite <- Hnew_sp_eq in Hload_sp1_env. exact Hload_sp1_env. }
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm1. exact Hstore2.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        (* sp[2] ea load in m2 *)
        assert (Hload_sp2_m2 : Mem.load Mint64 m2 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                  Some (Vlong (Int64.repr (z0 * 2 + 1)))).
        { assert (Hm1 : Mem.load Mint64 m1 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                    Some (Vlong (Int64.repr (z0 * 2 + 1)))).
          { erewrite Mem.load_store_other. 2: exact Hstore1.
            { rewrite <- Hnew_sp_eq in Hload_sp2_ea. exact Hload_sp2_ea. }
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm1. exact Hstore2.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        (* sp loads survive stores 3,4,5 (all to sb, different block from sp_b) *)
        assert (Hload_sp0_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs) =
                  Some (Vptr ret_pc_b ret_pc_ofs)).
        { assert (Hm3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs) =
                    Some (Vptr ret_pc_b ret_pc_ofs)).
          { erewrite Mem.load_store_other. exact Hload_sp0_m2. exact Hstore3.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          assert (Hm4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs) =
                    Some (Vptr ret_pc_b ret_pc_ofs)).
          { erewrite Mem.load_store_other. exact Hm3. exact Hstore4.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        assert (Hload_sp1_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 8) =
                  Some env_cv).
        { assert (Hm3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 8) =
                    Some env_cv).
          { erewrite Mem.load_store_other. exact Hload_sp1_m2. exact Hstore3.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          assert (Hm4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 8) =
                    Some env_cv).
          { erewrite Mem.load_store_other. exact Hm3. exact Hstore4.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        assert (Hload_sp2_m5 : Mem.load Mint64 m5 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                  Some (Vlong (Int64.repr (z0 * 2 + 1)))).
        { assert (Hm3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                    Some (Vlong (Int64.repr (z0 * 2 + 1)))).
          { erewrite Mem.load_store_other. exact Hload_sp2_m2. exact Hstore3.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          assert (Hm4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                    Some (Vlong (Int64.repr (z0 * 2 + 1)))).
          { erewrite Mem.load_store_other. exact Hm3. exact Hstore4.
            left. intro Heq; apply Hsp_ne_sb; auto. }
          erewrite Mem.load_store_other. exact Hm4. exact Hstore5.
          left. intro Heq; apply Hsp_ne_sb; auto. }

        (* Witnesses *)
        set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
        set (le2 := PTree.set _t'14 (Vptr sp_b sp_ofs) le1).
        set (le3 := PTree.set _t'15 (Vint stacksize_int) le2).
        set (le4 := PTree.set _t'2 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le3).
        set (le5 := PTree.set _t'8 (Vptr sp_b new_sp_ofs) le4).
        set (le6 := PTree.set _t'9 (Vptr ret_pc_b ret_pc_ofs) le5).
        set (le7 := PTree.set _t'6 (Vptr sp_b new_sp_ofs) le6).
        set (le8 := PTree.set _t'7 env_cv le7).
        set (le9 := PTree.set _t'4 (Vptr sp_b new_sp_ofs) le8).
        set (le10 := PTree.set _t'5 (Vlong (Int64.repr (z0 * 2 + 1))) le9).
        set (le11 := PTree.set _t'3 (Vptr sp_b new_sp_ofs) le10).
        set (le_final := le11).

        exists le_final. exists m6.
        exists (Out_return (Some (Vint (Int.repr 0), tint))).

        split.

        (* ============================================================ *)
        (* Part 1: exec -- the C body executes                           *)
        (* ============================================================ *)
        {
          (* Decomposed bigstep proof -- split at Ssequence boundaries *)
          (* Body = Ssequence PREAMBLE (Ssequence (Ssequence S6 IF) SRETURN) *)
          apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m2).

          (* PREAMBLE: Ssequence (Ssequence S1 S2) (Ssequence S3 (Ssequence S4 S5)) *)
          { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).
            (* S1;S2: read pc, advance pc *)
            { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
              (* S1: Sset _t'1 (s->pc) *)
              rewrite Hle_s; eval_cbn.
              rewrite Hco; eval_cbn.
              rewrite Hpc_offset; eval_cbn.
              rewrite Mptr_Mint64; eval_cbn.
              rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
              rewrite Hpc_load; eval_cbn.
              (* S2: Sassign (s->pc) (_t'1+1) -- rvalue _t'1 resolved first *)
              rewrite PTree.gss; eval_cbn.
              (* lvalue needs _s through PTree.set _t'1 *)
              rewrite PTree.gso by (compute; congruence).
              rewrite Hle_s; eval_cbn.
              rewrite sem_add_ptr_int_1; eval_cbn.
              rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
              rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
              rewrite Mptr_Mint64; eval_cbn.
              fold advanced_pc.
              rewrite Hstore1; eval_cbn.
              reflexivity. }
            (* S3;S4;S5: read sp, read stacksize, sp += stacksize *)
            { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
              unfold le1.
              rewrite PTree.gso by (compute; congruence).
              rewrite Hle_s; eval_cbn.
              rewrite Hco; eval_cbn.
              rewrite Hsp_offset; eval_cbn.
              rewrite Mptr_Mint64; eval_cbn.
              rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
              rewrite Hsp_load_m1; eval_cbn.
              rewrite PTree.gso by (compute; congruence).
              rewrite PTree.gss; eval_cbn.
              rewrite Hcode_load_m1; eval_cbn.
              repeat (rewrite PTree.gso by (compute; congruence)).
              rewrite Hle_s; eval_cbn.
              (* Hsp_offset already applied globally; lvalue resolves via eval_cbn *)
              rewrite PTree.gss; eval_cbn.
              rewrite PTree.gss; eval_cbn.
              fold stacksize_int.
              rewrite (sem_add_sp_n sp_b sp_ofs stacksize_int m1); eval_cbn.
              fold new_sp_ofs.
              rewrite sem_cast_ptr_to_ptr; eval_cbn.
              rewrite Mptr_Mint64; eval_cbn.
              rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
              rewrite Hstore2; eval_cbn.
              reflexivity. } }

          (* Ssequence (Ssequence S6 IF) SRETURN *)
          { apply exec_Sseq_1 with (t1 := E0) (le1 := le11) (m1 := m6).
            (* S6;IF *)
            { apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m2).
              (* S6: read extra_args *)
              { apply (eval_stmt_to_exec clight_ge 10). eval_cbn.
                unfold le3, le2, le1.
                repeat (rewrite PTree.gso by (compute; congruence)).
                rewrite Hle_s; eval_cbn.
                rewrite Hco; eval_cbn.
                rewrite Hextra_offset; eval_cbn.
                rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                rewrite Hextra_load_m2; eval_cbn.
                reflexivity. }
              (* Sifthenelse: condition false, else branch *)
              { eapply exec_Sifthenelse.
                - (* eval condition: Ogt _t'2 0 *)
                  eapply eval_Ebinop.
                  + eapply eval_Etempvar. unfold le4. rewrite PTree.gss. reflexivity.
                  + eapply eval_Econst_int.
                  + exact (sem_gt_long_int (Int64.repr (Z.of_nat (extra_args s)))
                             (Int.repr 0) m2).
                - (* bool_val *)
                  rewrite (return_gt_iff (extra_args s) Hea_signed).
                  rewrite Hltb. exact (bool_val_of_bool false m2).
                - (* else branch body *)
                  simpl.
                  (* Else = Ssequence (E1;E2;E3) (Ssequence (E4;E5;E6) (Ssequence (E7;E8;E9) (E10;E11))) *)
                  apply exec_Sseq_1 with (t1 := E0) (le1 := le6) (m1 := m3).
                  (* E1;E2;E3: read sp, read sp[0]=ret_pc, store pc *)
                  { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
                    unfold le4, le3, le2, le1.
                    (* E1 *)
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Hco; eval_cbn.
                    rewrite Hsp_offset; eval_cbn.
                    rewrite Mptr_Mint64; eval_cbn.
                    rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                    rewrite Hsp_load_m2; eval_cbn.
                    (* E2 *)
                    rewrite PTree.gss; eval_cbn.
                    rewrite sem_add_sp_0; eval_cbn.
                    rewrite Hload_sp0_m2; eval_cbn.
                    (* E3 *)
                    repeat (rewrite PTree.gso by (compute; congruence)).
                    rewrite Hle_s; eval_cbn.
                    rewrite Hpc_offset; eval_cbn.
                    rewrite PTree.gss; eval_cbn.
                    rewrite sem_cast_long_to_ptr_tint_vptr; eval_cbn.
                    rewrite sem_cast_ptr_tint_to_ptr_tint; eval_cbn.
                    rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
                    rewrite Mptr_Mint64; eval_cbn.
                    fold new_pc_v.
                    rewrite Hstore3; eval_cbn.
                    reflexivity. }
                  (* Ssequence (E4;E5;E6) (Ssequence (E7;E8;E9) (E10;E11)) *)
                  { apply exec_Sseq_1 with (t1 := E0) (le1 := le8) (m1 := m4).
                    (* E4;E5;E6: read sp, read sp[1]=env, store env *)
                    { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
                      unfold le6, le5, le4, le3, le2, le1.
                      (* E4 *)
                      repeat (rewrite PTree.gso by (compute; congruence)).
                      rewrite Hle_s; eval_cbn.
                      rewrite Hco; eval_cbn.
                      rewrite Hsp_offset; eval_cbn.
                      rewrite Mptr_Mint64; eval_cbn.
                      rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                      assert (Hsp_load_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
                                Some (Vptr sp_b new_sp_ofs)).
                      { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                                 new_pc_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
                      rewrite Hsp_load_m3; eval_cbn.
                      (* E5 *)
                      rewrite PTree.gss; eval_cbn.
                      rewrite sem_add_sp_1; eval_cbn.
                      assert (Hload_sp1_m3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 8))) =
                                Some env_cv).
                      { rewrite (ptrofs_add_unsigned new_sp_ofs 8 ltac:(lia) ltac:(lia)).
                        erewrite Mem.load_store_other. exact Hload_sp1_m2. exact Hstore3.
                        left. intro Heq; apply Hsp_ne_sb; auto. }
                      rewrite Hload_sp1_m3; eval_cbn.
                      (* E6 *)
                      repeat (rewrite PTree.gso by (compute; congruence)).
                      rewrite Hle_s; eval_cbn.
                      rewrite Henv_offset; eval_cbn.
                      rewrite PTree.gss; eval_cbn.
                      assert (Henv_cv_cast : sem_cast env_cv tlong tlong m3 = Some env_cv).
                      { apply (sem_cast_long_val_repr hm cb co v1 env_cv m3 Henv_repr_ret). }
                      rewrite Henv_cv_cast; eval_cbn.
                      rewrite (ptrofs_add_unsigned so 24 ltac:(lia) ltac:(lia)).
                      rewrite Hstore4; eval_cbn.
                      reflexivity. }
                    (* Ssequence (E7;E8;E9) (E10;E11) *)
                    { apply exec_Sseq_1 with (t1 := E0) (le1 := le10) (m1 := m5).
                      (* E7;E8;E9: read sp, read sp[2]=ea, store extra_args *)
                      { apply (eval_stmt_to_exec clight_ge 20). eval_cbn.
                        unfold le8, le7, le6, le5, le4, le3, le2, le1.
                        (* E7 *)
                        repeat (rewrite PTree.gso by (compute; congruence)).
                        rewrite Hle_s; eval_cbn.
                        rewrite Hco; eval_cbn.
                        rewrite Hsp_offset; eval_cbn.
                        rewrite Mptr_Mint64; eval_cbn.
                        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                        assert (Hsp_load_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 16) =
                                  Some (Vptr sp_b new_sp_ofs)).
                        { assert (Hsp_load_m3' : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 16) =
                                    Some (Vptr sp_b new_sp_ofs)).
                          { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 16)
                                     new_pc_v (Vptr sp_b new_sp_ofs) Hstore3 Hsp_load_m2). right. lia. }
                          apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 16)
                                   env_cv (Vptr sp_b new_sp_ofs) Hstore4 Hsp_load_m3'). left. lia. }
                        rewrite Hsp_load_m4; eval_cbn.
                        (* E8 *)
                        rewrite PTree.gss; eval_cbn.
                        rewrite sem_add_sp_2; eval_cbn.
                        assert (Hload_sp2_m4 : Mem.load Mint64 m4 sp_b (Ptrofs.unsigned (Ptrofs.add new_sp_ofs (Ptrofs.repr 16))) =
                                  Some (Vlong (Int64.repr (z0 * 2 + 1)))).
                        { rewrite (ptrofs_add_unsigned new_sp_ofs 16 ltac:(lia) ltac:(lia)).
                          assert (Hm3 : Mem.load Mint64 m3 sp_b (Ptrofs.unsigned new_sp_ofs + 16) =
                                    Some (Vlong (Int64.repr (z0 * 2 + 1)))).
                          { erewrite Mem.load_store_other. exact Hload_sp2_m2. exact Hstore3.
                            left. intro Heq; apply Hsp_ne_sb; auto. }
                          erewrite Mem.load_store_other. exact Hm3. exact Hstore4.
                          left. intro Heq; apply Hsp_ne_sb; auto. }
                        rewrite Hload_sp2_m4; eval_cbn.
                        (* E9 *)
                        repeat (rewrite PTree.gso by (compute; congruence)).
                        rewrite Hle_s; eval_cbn.
                        rewrite Hextra_offset; eval_cbn.
                        rewrite PTree.gss; eval_cbn.
                        rewrite sem_cast_long_vlong; eval_cbn.
                        rewrite (sem_shr_long_int_1 (Int64.repr (z0 * 2 + 1)) m4); eval_cbn.
                        rewrite sem_cast_long_vlong; eval_cbn.
                        fold new_extra.
                        rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
                        rewrite Hstore5; eval_cbn.
                        reflexivity. }
                      (* E10;E11: read sp, sp += 3 *)
                      { apply (eval_stmt_to_exec clight_ge 15). eval_cbn.
                        unfold le10, le9, le8, le7, le6, le5, le4, le3, le2, le1.
                        (* E10 *)
                        repeat (rewrite PTree.gso by (compute; congruence)).
                        rewrite Hle_s; eval_cbn.
                        rewrite Hco; eval_cbn.
                        rewrite Hsp_offset; eval_cbn.
                        rewrite Mptr_Mint64; eval_cbn.
                        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                        rewrite Hsp_load_m5; eval_cbn.
                        (* E11 *)
                        repeat (rewrite PTree.gso by (compute; congruence)).
                        rewrite Hle_s; eval_cbn.
                        (* Hsp_offset already applied globally; lvalue resolves via eval_cbn *)
                        rewrite PTree.gss; eval_cbn.
                        rewrite sem_add_sp_3; eval_cbn.
                        fold final_sp_ofs.
                        rewrite sem_cast_ptr_to_ptr; eval_cbn.
                        rewrite Mptr_Mint64; eval_cbn.
                        rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                        rewrite Hstore6; eval_cbn.
                        reflexivity. } } } } }
            (* Sreturn 0 *)
            { apply exec_Sreturn_some. eapply eval_Econst_int. } }
        }

        (* ============================================================ *)
        (* Part 2: abs_rel for post-state                                 *)
        (* ============================================================ *)
        {
          set (uso := Ptrofs.unsigned so) in *.
          set (new_co := ar_code_base_ofs ard) in *.
          set (ard' := mk_abs_rel sb so hm cb new_co
                         (ar_global_block ard) (ar_global_ofs ard)
                         (ar_stack_block ard) (ar_stack_base_ofs ard)
                         (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                         (ar_sptr_ofs_bound ard)).
          exists ard'.

          (* Loads in final memory m6 *)

          (* pc at uso+0: written in store3, survived stores 4,5,6 *)
          assert (Hpc_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
          { assert (Hpc_m3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
            { pose proof (load_after_store_same m2 m3 sb (Ptrofs.unsigned so + 0) new_pc_v Hstore3) as Htmp.
              unfold new_pc_v in Htmp. simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp.
              exact Htmp. }
            assert (Hpc_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
            { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 0)
                       env_cv new_pc_v Hstore4 Hpc_m3). left. lia. }
            assert (Hpc_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 0) = Some new_pc_v).
            { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 0)
                       new_extra new_pc_v Hstore5 Hpc_m4). left. lia. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 0)
                     (Vptr sp_b final_sp_ofs) new_pc_v Hstore6 Hpc_m5). left. lia. }

          (* accu at uso+8 *)
          assert (Haccu_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 8) = Some accu_v).
          { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
                     advanced_pc accu_v Hstore1 Haccu_load). right. lia. }
          assert (Haccu_load_m2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 8) = Some accu_v).
          { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
                     (Vptr sp_b new_sp_ofs) accu_v Hstore2 Haccu_load_m1). left. lia. }
          assert (Haccu_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 8) = Some accu_v).
          { assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 8) = Some accu_v).
            { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 8)
                       new_pc_v accu_v Hstore3 Haccu_load_m2). right. lia. }
            assert (Hm4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 8) = Some accu_v).
            { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 8)
                       env_cv accu_v Hstore4 Hm3). left. lia. }
            assert (Hm5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 8) = Some accu_v).
            { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 8)
                       new_extra accu_v Hstore5 Hm4). left. lia. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 8)
                     (Vptr sp_b final_sp_ofs) accu_v Hstore6 Hm5). left. lia. }

          (* sp at uso+16: written in store6 *)
          assert (Hsp_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 16) =
                    Some (Vptr sp_b final_sp_ofs)).
          { pose proof (load_after_store_same m5 m6 sb (Ptrofs.unsigned so + 16) (Vptr sp_b final_sp_ofs) Hstore6) as Htmp.
            simpl Val.load_result in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

          (* env at uso+24: written in store4, survived stores 5,6 *)
          assert (Henv_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 24) = Some env_cv).
          { assert (Henv_m4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 24) = Some env_cv).
            { pose proof (load_after_store_same m3 m4 sb (Ptrofs.unsigned so + 24) env_cv Hstore4) as Htmp.
              rewrite (val_repr_load_result hm cb co v1 env_cv Henv_repr_ret) in Htmp.
              exact Htmp. }
            assert (Henv_m5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 24) = Some env_cv).
            { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 24)
                       new_extra env_cv Hstore5 Henv_m4). left. lia. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 24)
                     (Vptr sp_b final_sp_ofs) env_cv Hstore6 Henv_m5). right. lia. }

          (* extra_args at uso+32: written in store5, survived store6 *)
          assert (Hextra_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 32) = Some new_extra).
          { assert (Hm5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 32) = Some new_extra).
            { pose proof (load_after_store_same m4 m5 sb (Ptrofs.unsigned so + 32) new_extra Hstore5) as Htmp.
              unfold new_extra in Htmp. simpl Val.load_result in Htmp. exact Htmp. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 32)
                     (Vptr sp_b final_sp_ofs) new_extra Hstore6 Hm5). right. lia. }

          (* global_data at uso+40 *)
          assert (Hgd_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
          { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
            { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                       advanced_pc gd_ptr Hstore1 Hgd_load). right. lia. }
            assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
            { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                       (Vptr sp_b new_sp_ofs) gd_ptr Hstore2 Hm1). right. lia. }
            assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
            { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 40)
                       new_pc_v gd_ptr Hstore3 Hm2). right. lia. }
            assert (Hm4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
            { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 40)
                       env_cv gd_ptr Hstore4 Hm3). right. lia. }
            assert (Hm5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 40) = Some gd_ptr).
            { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 40)
                       new_extra gd_ptr Hstore5 Hm4). right. lia. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 40)
                     (Vptr sp_b final_sp_ofs) gd_ptr Hstore6 Hm5). right. lia. }

          (* trap_sp at uso+48 *)
          assert (Hts_load6 : Mem.load Mint64 m6 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
          { assert (Hm1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
            { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                       advanced_pc ts_ptr Hstore1 Hts_load). right. lia. }
            assert (Hm2 : Mem.load Mint64 m2 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
            { apply (load_after_store_other m1 m2 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                       (Vptr sp_b new_sp_ofs) ts_ptr Hstore2 Hm1). right. lia. }
            assert (Hm3 : Mem.load Mint64 m3 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
            { apply (load_after_store_other m2 m3 sb (Ptrofs.unsigned so + 0) (Ptrofs.unsigned so + 48)
                       new_pc_v ts_ptr Hstore3 Hm2). right. lia. }
            assert (Hm4 : Mem.load Mint64 m4 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
            { apply (load_after_store_other m3 m4 sb (Ptrofs.unsigned so + 24) (Ptrofs.unsigned so + 48)
                       env_cv ts_ptr Hstore4 Hm3). right. lia. }
            assert (Hm5 : Mem.load Mint64 m5 sb (Ptrofs.unsigned so + 48) = Some ts_ptr).
            { apply (load_after_store_other m4 m5 sb (Ptrofs.unsigned so + 32) (Ptrofs.unsigned so + 48)
                       new_extra ts_ptr Hstore5 Hm4). right. lia. }
            apply (load_after_store_other m5 m6 sb (Ptrofs.unsigned so + 16) (Ptrofs.unsigned so + 48)
                     (Vptr sp_b final_sp_ofs) ts_ptr Hstore6 Hm5). right. lia. }

          (* sb_writable in m6 *)
          assert (Hsb_writable_m6 : Mem.range_perm m6 sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56) Cur Writable).
          { intros ofs' Hofs'.
            eapply Mem.perm_store_1. exact Hstore6.
            eapply Mem.perm_store_1. exact Hstore5.
            eapply Mem.perm_store_1. exact Hstore4.
            eapply Mem.perm_store_1. exact Hstore3.
            eapply Mem.perm_store_1. exact Hstore2.
            eapply Mem.perm_store_1. exact Hstore1.
            apply Hsb_writable. exact Hofs'. }

          (* Stack repr for post-state: stk2 at final_sp_ofs *)
          assert (Hstack_m6 : stack_repr hm cb co m6 stk2 sp_b final_sp_ofs).
          { (* The original stack_repr gives us stk at new_sp_ofs.
               stk = Val_int z0 :: v1 :: Val_int z0 :: stk2 (from Hstk_eq).
               So stk2 starts at new_sp_ofs + 24 = final_sp_ofs.
               We extract stk2's stack_repr from the original by inverting
               the 3 cons cells. *)
            assert (Hstk_repr_at_new : stack_repr hm cb co m (skipn stacksize (Machine.stack s))
                      sp_b (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))).
            { exact (stack_repr_skipn stacksize hm cb co m (Machine.stack s) sp_b sp_ofs Hstack_repr). }
            rewrite Hstk_match in Hstk_repr_at_new.
            inversion Hstk_repr_at_new as [| xv1 xvs1 xb1 xofs1 xcv1 Hload1' Hrepr1' Htail1']. subst.
            inversion Htail1' as [| xv2 xvs2 xb2 xofs2 xcv2 Hload2' Hrepr2' Htail2']. subst.
            inversion Htail2' as [| xv3 xvs3 xb3 xofs3 xcv3 Hload3' Hrepr3' Htail3']. subst.

            (* stk2's stack_repr is at sp + stacksize*8 + 24 *)
            replace final_sp_ofs with
              (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr (Z.of_nat stacksize * 8)))
                (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)).
            2: { unfold final_sp_ofs. rewrite Hnew_sp_eq.
                 repeat rewrite Ptrofs.add_assoc.
                 repeat rewrite ptrofs_add_repr. reflexivity. }

            (* Now propagate through stores 1-6 (all to sb, different block) *)
            apply (stack_repr_store_other_block hm cb co m5 m6 _ sp_b _ sb (Ptrofs.unsigned so + 16) (Vptr sp_b final_sp_ofs)).
            - apply (stack_repr_store_other_block hm cb co m4 m5 _ sp_b _ sb (Ptrofs.unsigned so + 32) new_extra).
              + apply (stack_repr_store_other_block hm cb co m3 m4 _ sp_b _ sb (Ptrofs.unsigned so + 24) env_cv).
                * apply (stack_repr_store_other_block hm cb co m2 m3 _ sp_b _ sb (Ptrofs.unsigned so + 0) new_pc_v).
                  { apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b _ sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                    { apply (stack_repr_store_other_block hm cb co m m1 _ sp_b _ sb (Ptrofs.unsigned so + 0) advanced_pc).
                      { exact Htail3'. }
                      { exact Hstore1. }
                      { intro Heq; apply Hsp_ne_sb; auto. } }
                    { exact Hstore2. }
                    { intro Heq; apply Hsp_ne_sb; auto. } }
                  { exact Hstore3. }
                  { intro Heq; apply Hsp_ne_sb; auto. }
                * exact Hstore4.
                * intro Heq; apply Hsp_ne_sb; auto.
              + exact Hstore5.
              + intro Heq; apply Hsp_ne_sb; auto.
            - exact Hstore6.
            - intro Heq; apply Hsp_ne_sb; auto.
          }

          (* le_final ! _s *)
          assert (Hle_final_s : le_final ! _s = Some (Vptr sb so)).
          { subst le_final le11 le10 le9 le8 le7 le6 le5 le4 le3 le2 le1.
            repeat (rewrite PTree.gso by (compute; congruence)).
            exact Hle_s. }

          split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

          (* 1. _s is in le' *)
          { exact Hle_final_s. }

          (* 2. pc field *)
          { exists new_pc_v. split.
            - exact Hpc_load6.
            - simpl. exact Hpc_rel_ret. }

          (* 3. accu field *)
          { exists accu_v. split.
            - exact Haccu_load6.
            - simpl. exact Haccu_repr. }

          (* 4. sp field *)
          { exists (Vptr sp_b final_sp_ofs), sp_b, final_sp_ofs.
            split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
            - exact Hsp_load6.
            - reflexivity.
            - simpl stack. exact Hstack_m6.
            - exact Hsp_ne_sb.
            - exact Hsp_ne_gb.
            - exact Hcb_ne_sp.
            - (* sp_ge8 *) rewrite Hfinal_sp_unsigned. rewrite Hnew_sp_unsigned. lia.
            - (* sp_rep *)
              simpl stack.
              rewrite Hfinal_sp_unsigned. rewrite Hnew_sp_unsigned.
              rewrite <- Hnew_sp_eq in Hrest_fits.
              rewrite Hnew_sp_unsigned in Hrest_fits.
              lia.
            - (* sp_writable *)
              simpl stack.
              rewrite Hfinal_sp_unsigned. rewrite Hnew_sp_unsigned.
              intros ofs' Hofs'.
              eapply Mem.perm_store_1. exact Hstore6.
              eapply Mem.perm_store_1. exact Hstore5.
              eapply Mem.perm_store_1. exact Hstore4.
              eapply Mem.perm_store_1. exact Hstore3.
              eapply Mem.perm_store_1. exact Hstore2.
              eapply Mem.perm_store_1. exact Hstore1.
              apply Hsp_writable.
              (* Need: ofs' in range of original stack *)
              fold stk in Hstk_eq. rewrite <- Hstk_match in Hstk_eq.
              assert (Hlen_stk : Datatypes.length (skipn stacksize (Machine.stack s)) =
                        Datatypes.length (Val_int z :: v1 :: Val_int z0 :: stk2)).
              { f_equal. exact Hstk_match. }
              simpl length in Hlen_stk. rewrite length_skipn in Hlen_stk.
              simpl length. lia.
            - rewrite Hfinal_sp_unsigned. rewrite Hnew_sp_unsigned.
              apply Z.divide_add_r. apply Z.divide_add_r.
              exact Hsp_align.
              exists (Z.of_nat stacksize). simpl. lia.
              exists 3. simpl. lia. }

          (* 5. env field *)
          { exists env_cv. split.
            - exact Henv_load6.
            - simpl. exact Henv_repr_ret. }

          (* 6. extra_args field *)
          { simpl.
            unfold new_extra in Hextra_load6.
            rewrite Hshr_eq in Hextra_load6.
            (* Need: Z.of_nat (Z.to_nat z0) = z0 *)
            rewrite Z2Nat.id by lia.
            exact Hextra_load6. }

          (* 7. global_data field *)
          { exists gd_ptr. split; [| split; [| split]].
            - exact Hgd_load6.
            - simpl. exact Hgd_eq.
            - simpl.
              apply (global_repr_store_other_block hm cb co m5 m6 _
                       (ar_global_block ard) (ar_global_ofs ard)
                       sb (Ptrofs.unsigned so + 16) (Vptr sp_b final_sp_ofs)).
              + apply (global_repr_store_other_block hm cb co m4 m5 _
                         (ar_global_block ard) (ar_global_ofs ard)
                         sb (Ptrofs.unsigned so + 32) new_extra).
                * apply (global_repr_store_other_block hm cb co m3 m4 _
                           (ar_global_block ard) (ar_global_ofs ard)
                           sb (Ptrofs.unsigned so + 24) env_cv).
                  { apply (global_repr_store_other_block hm cb co m2 m3 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sb (Ptrofs.unsigned so + 0) new_pc_v).
                    { apply (global_repr_store_other_block hm cb co m1 m2 _
                               (ar_global_block ard) (ar_global_ofs ard)
                               sb (Ptrofs.unsigned so + 16) (Vptr sp_b new_sp_ofs)).
                      { apply (global_repr_store_other_block hm cb co m m1 _
                                 (ar_global_block ard) (ar_global_ofs ard)
                                 sb (Ptrofs.unsigned so + 0) advanced_pc).
                        exact Hglobal_repr. exact Hstore1.
                        intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
                      { exact Hstore2. }
                      { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). } }
                    { exact Hstore3. }
                    { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). } }
                  { exact Hstore4. }
                  { intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)). }
                * exact Hstore5.
                * intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
              + exact Hstore6.
              + intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
            - exact Hgb_ne_sb. }

          (* 8. trap_sp field *)
          { exists ts_ptr. split.
            - exact Hts_load6.
            - simpl. exact Htrap_rel. }

          (* 9. sb_writable *)
          { exact Hsb_writable_m6. }
        }
  }

Qed.
