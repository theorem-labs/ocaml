(* GRAB_correct.v -- GRAB handler completeness proof.

   GRAB required:
   - Rocq: handle_GRAB required pc' s =
       if Nat.leb required (extra_args s) then
         Step (s <|pc := pc'|> <|extra_args := Nat.sub (extra_args s) required|>)
       else
         ... (build partial application closure and return to caller)

   C code (f_instr_GRAB, "then" branch only -- extra_args >= required):
     _t'1 = s->pc;             // read pc pointer
     s->pc = _t'1 + 1;         // advance pc past argument
     _required = *_t'1;        // read required from code buffer
     _t'3 = s->extra_args;     // read extra_args
     if (_t'3 >= _required)    // Oge: tlong >= tint
       _t'17 = s->extra_args;
       s->extra_args = _t'17 - _required;   // extra_args -= required
     else
       ... (complex closure building -- requires separate precondition)
     return 0;

   The "then" branch stores: pc field at offset +0, extra_args at offset +32.

   The "else" branch involves heap_alloc calls and loops, and is handled
   by a False precondition (to be proved separately or with stronger
   infrastructure).

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
(* Struct layout: _pc at 0, _extra_args at 32                          *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset ce _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_grab : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _pc (co_members co) = Errors.OK (0, Full) /\
  field_offset (genv_cenv clight_ge) _extra_args (co_members co) = Errors.OK (32, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

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

(* Oge on tlong vs tint: CompCert promotes tint to tlong (signed),
   then does Int64.cmp Cge = negb (Int64.lt ...) *)
Local Lemma sem_ge_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Oge
    (Vlong n1) tlong (Vint n2) tint m
    = Some (Val.of_bool (negb (Int64.lt n1 (Int64.repr (Int.signed n2))))).
Proof.
  intros. unfold sem_binary_operation, sem_cmp.
  change (classify_cmp tlong tint) with cmp_default. simpl.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed). simpl.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true. simpl.
  reflexivity.
Qed.

Local Lemma bool_val_of_bool : forall b m,
  bool_val (Val.of_bool b) tint m = Some b.
Proof.
  intros [] m; simpl; reflexivity.
Qed.

(* Osub on tlong - tint: CompCert promotes tint to tlong (signed), then subtracts *)
Local Lemma sem_sub_long_int : forall n1 n2 m,
  sem_binary_operation (genv_cenv clight_ge) Osub
    (Vlong n1) tlong (Vint n2) tint m
    = Some (Vlong (Int64.sub n1 (Int64.repr (Int.signed n2)))).
Proof.
  intros. unfold sem_binary_operation, sem_sub.
  change (classify_sub tlong tint) with sub_default.
  unfold sem_binarith.
  change (classify_binarith tlong tint) with (bin_case_l Signed). simpl.
  unfold sem_cast. simpl classify_cast. rewrite ptr64_true. simpl.
  reflexivity.
Qed.

Local Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof. intros. apply sem_cast_long_vlong. Qed.

Local Lemma load_result_vptr : forall b ofs,
  Val.load_result Mint64 (Vptr b ofs) = Vptr b ofs.
Proof. intros. simpl. rewrite ptr64_true. reflexivity. Qed.

Local Lemma load_result_vlong : forall n,
  Val.load_result Mint64 (Vlong n) = Vlong n.
Proof. intros. reflexivity. Qed.

(* pc_rel with shifted code base *)
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
(* Arithmetic: relating Nat.leb, Z, and Int64 comparison               *)
(* ================================================================== *)

(* When required fits in int32 signed range, and extra_args fits in int64
   unsigned range as a nat, the Oge comparison matches Nat.leb. *)
Local Lemma grab_ge_iff : forall ea req,
  0 <= Z.of_nat req <= Int.max_signed ->
  Z.of_nat ea <= Int64.max_signed ->
  negb (Int64.lt (Int64.repr (Z.of_nat ea))
                  (Int64.repr (Int.signed (Int.repr (Z.of_nat req)))))
  = Nat.leb req ea.
Proof.
  intros ea req Hreq Hea.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647 in Hreq |- *. lia. }
  unfold Int64.lt.
  rewrite Int64.signed_repr.
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807 in Hea |- *. lia. }
  rewrite Int64.signed_repr.
  2: { change Int64.min_signed with (-9223372036854775808).
       change Int64.max_signed with 9223372036854775807.
       change Int.max_signed with 2147483647 in Hreq. lia. }
  destruct (Z.lt_ge_cases (Z.of_nat ea) (Z.of_nat req)) as [Hlt | Hge].
  - rewrite zlt_true by lia.
    simpl negb.
    symmetry. apply Nat.leb_gt. lia.
  - rewrite zlt_false by lia.
    simpl negb.
    symmetry. apply Nat.leb_le. lia.
Qed.

(* Arithmetic: extra_args - required as Int64 *)
Local Lemma grab_sub_ea : forall ea req,
  0 <= Z.of_nat req <= Int.max_signed ->
  Z.of_nat ea <= Int64.max_unsigned ->
  (req <= ea)%nat ->
  Int64.sub (Int64.repr (Z.of_nat ea))
            (Int64.repr (Int.signed (Int.repr (Z.of_nat req))))
  = Int64.repr (Z.of_nat (ea - req)).
Proof.
  intros ea req Hreq Hea Hle.
  rewrite Int.signed_repr.
  2: { change Int.min_signed with (-2147483648).
       change Int.max_signed with 2147483647 in Hreq |- *. lia. }
  unfold Int64.sub.
  f_equal.
  rewrite (Int64.unsigned_repr (Z.of_nat ea)).
  2: { change Int64.max_unsigned with 18446744073709551615. split; [lia | exact Hea]. }
  rewrite (Int64.unsigned_repr (Z.of_nat req)).
  2: { change Int64.max_unsigned with 18446744073709551615.
       change Int.max_signed with 2147483647 in Hreq. split; lia. }
  rewrite Nat2Z.inj_sub by lia. reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

#[warnings="-not-a-closed-proof"]
Theorem verify_GRAB_correct : forall required,
    handler_correct (handle_GRAB required) f_instr_GRAB
      (fun _ m s ard =>
         (* The code buffer contains Int.repr required at the current PC *)
         Mem.load Mint32 m (ar_code_base_block ard)
           (Ptrofs.unsigned (Ptrofs.add (ar_code_base_ofs ard)
              (Ptrofs.repr (Machine.pc s * sizeof_code_t))))
         = Some (Vint (Int.repr (Z.of_nat required))) /\
         (* required fits in int32 signed range *)
         0 <= Z.of_nat required <= Int.max_signed /\
         (* extra_args fits in int64 ranges *)
         Z.of_nat (extra_args s) <= Int64.max_signed /\
         Z.of_nat (extra_args s) <= Int64.max_unsigned /\
         (* Nat.leb holds (we prove the then-branch) *)
         Nat.leb required (extra_args s) = true)
      (fun msg s =>
         msg = "GRAB: malformed return frame"%string /\
         Nat.leb required (extra_args s) = false /\
         match skipn (S (extra_args s)) (Machine.stack s) with
         | Val_int _ :: _ :: Val_int _ :: _ => False
         | _ => True
         end)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intro required.
  intros e le m s.
  unfold handler_correct, handle_GRAB.

  (* Simplify Nat.leb in the match *)
  destruct (Nat.leb required (extra_args s)) eqn:Hleb.

  (* ================================================================ *)
  (* Case: extra_args >= required => Step                              *)
  (* ================================================================ *)
  {
    intros ard Hpre Hstep_pre.
    unfold abs_rel_with_ard in Hpre.

    set (sb := ar_sptr_block ard) in *.
    set (so := ar_sptr_ofs ard) in *.
    set (hm := ar_heap_map ard) in *.
    set (cb := ar_code_base_block ard) in *.
    set (co := ar_code_base_ofs ard) in *.

    destruct Hpre as (Hle_s &
      [pc_ptr [Hpc_load Hpc_rel]] &
      [accu_v [Haccu_load Haccu_repr]] &
      [sp_ptr [sp_b [sp_ofs [Hsp_load [Hsp_eq [Hstack_repr [Hsp_ne_sb [Hsp_ne_gb [Hcb_ne_sp [Hsp_ge8 [Hsp_rep [Hsp_writable Hsp_align]]]]]]]]]]]] &
      [env_v [Henv_load Henv_repr]] &
      Hextra_load &
      [gd_ptr [Hgd_load [Hgd_eq [Hglobal_repr Hgb_ne_sb]]]] &
      [ts_ptr [Hts_load Htrap_rel]] & Hsb_writable).
    subst sp_ptr.

    destruct Hstep_pre as (Hcode_load & Hreq_range & Hea_signed & Hea_unsigned & Hleb_eq).
    (* Hleb_eq is redundant with Hleb, but confirms the precondition *)

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
    pose proof (ar_code_ne_sptr ard) as Hcb_ne. fold sb cb in Hcb_ne.

    (* Composite environment *)
    destruct interp_state_co_grab as [co_is [Hco [Hpc_offset Hextra_offset]]].

    (* pc_ptr is a concrete Vptr *)
    unfold pc_rel in Hpc_rel. subst pc_ptr.
    set (pc_ofs := Ptrofs.add co (Ptrofs.repr (Machine.pc s * sizeof_code_t))) in *.

    (* New PC after advancement *)
    set (new_pc_ofs := Ptrofs.add pc_ofs (Ptrofs.repr 4)).
    set (new_pc_v := Vptr cb new_pc_ofs).

    (* Nat.leb -> le *)
    apply Nat.leb_le in Hleb as Hle_nat.

    (* Store 1: pc field at (sb, uso+0) <- new_pc_v *)
    assert (Hpc_load_uso : Mem.load Mint64 m sb (Ptrofs.unsigned so) =
              Some (Vptr cb pc_ofs)).
    { replace (Ptrofs.unsigned so) with (Ptrofs.unsigned so + 0)%Z by lia.
      exact Hpc_load. }

    destruct (store_succeeds_sb m sb so 0 (Vptr cb pc_ofs) Hsb_writable Hpc_load ltac:(lia) ltac:(lia) new_pc_v)
      as [m1 Hstore_pc].
    pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_pc Hsb_writable) as Hsb_writable_m1.

    (* Code load survives store_pc (different block) *)
    assert (Hcode_load_m1 : Mem.load Mint32 m1 cb (Ptrofs.unsigned pc_ofs) =
              Some (Vint (Int.repr (Z.of_nat required)))).
    { erewrite Mem.load_store_other.
      - exact Hcode_load.
      - exact Hstore_pc.
      - left. exact Hcb_ne. }

    (* extra_args field in m1: unaffected by store at offset 0 *)
    assert (Hextra_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 32) =
              Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
    { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 0)
               (Ptrofs.unsigned so + 32) new_pc_v
               (Vlong (Int64.repr (Z.of_nat (extra_args s))))
               Hstore_pc Hextra_load).
      right. lia. }

    (* New extra_args value *)
    set (new_ea := Nat.sub (extra_args s) required).
    set (new_ea_v := Vlong (Int64.sub (Int64.repr (Z.of_nat (extra_args s)))
                                       (Int64.repr (Int.signed (Int.repr (Z.of_nat required)))))).

    (* Store 2: extra_args field at (sb, uso+32) <- new_ea_v *)
    destruct (store_succeeds_sb m1 sb so 32
                (Vlong (Int64.repr (Z.of_nat (extra_args s))))
                Hsb_writable_m1 Hextra_load_m1 ltac:(lia) ltac:(lia) new_ea_v)
      as [m2 Hstore_ea].

    (* Witnesses *)
    set (le' := PTree.set _t'17 (Vlong (Int64.repr (Z.of_nat (extra_args s))))
               (PTree.set _t'3 (Vlong (Int64.repr (Z.of_nat (extra_args s))))
               (PTree.set _required (Vint (Int.repr (Z.of_nat required)))
               (PTree.set _t'1 (Vptr cb pc_ofs) le)))).
    exists le'. exists m2.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: manual bigstep construction                             *)
    (* ============================================================== *)
    {
      (* Intermediate local envs *)
      set (le1 := PTree.set _t'1 (Vptr cb pc_ofs) le).
      set (le2 := PTree.set _required (Vint (Int.repr (Z.of_nat required))) le1).
      set (le3 := PTree.set _t'3 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le2).

      (* S1: Sset _t'1 (s->pc) *)
      assert (Hexec_S1 : exec_stmt function_entry1 clight_ge e le m
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint)))
          E0 le1 m Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        rewrite Hpc_load; eval_cbn.
        reflexivity. }

      (* S2: Sassign (s->pc) (_t'1 + 1) *)
      assert (Hexec_S2 : exec_stmt function_entry1 clight_ge e le1 m
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _pc (tptr tint))
            (Ebinop Oadd (Etempvar _t'1 (tptr tint))
              (Econst_int (Int.repr 1) tint) (tptr tint)))
          E0 le1 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hpc_offset; eval_cbn.
        rewrite Mptr_Mint64; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_add_pc_1 cb pc_ofs m); eval_cbn.
        rewrite (sem_cast_ptr_tint_to_ptr_tint cb new_pc_ofs); eval_cbn.
        rewrite (ptrofs_add_unsigned so 0 ltac:(lia) ltac:(lia)).
        fold new_pc_v. rewrite Hstore_pc; eval_cbn.
        reflexivity. }

      (* S3: Sset _required (deref _t'1) *)
      assert (Hexec_S3 : exec_stmt function_entry1 clight_ge e le1 m1
          (Sset _required (Ederef (Etempvar _t'1 (tptr tint)) tint))
          E0 le2 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le1. rewrite PTree.gss; eval_cbn.
        rewrite Hcode_load_m1; eval_cbn.
        reflexivity. }

      (* S4: Sset _t'3 (s->extra_args) *)
      assert (Hexec_S4 : exec_stmt function_entry1 clight_ge e le2 m1
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _extra_args tlong))
          E0 le3 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le2, le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hextra_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
        rewrite Hextra_load_m1; eval_cbn.
        reflexivity. }

      (* S6: (then branch) Sset _t'17 (s->extra_args) *)
      set (le4 := PTree.set _t'17 (Vlong (Int64.repr (Z.of_nat (extra_args s)))) le3).
      assert (Hexec_S6 : exec_stmt function_entry1 clight_ge e le3 m1
          (Sset _t'17
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _extra_args tlong))
          E0 le4 m1 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le3, le2, le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hextra_offset; eval_cbn.
        rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
        rewrite Hextra_load_m1; eval_cbn.
        reflexivity. }

      (* S7: Sassign (s->extra_args) (_t'17 - _required) *)
      assert (Hexec_S7 : exec_stmt function_entry1 clight_ge e le4 m1
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _interp_state noattr)))
                (Tstruct _interp_state noattr)) _extra_args tlong)
            (Ebinop Osub (Etempvar _t'17 tlong) (Etempvar _required tint)
              tlong))
          E0 le4 m2 Out_normal).
      { apply (eval_stmt_to_exec clight_ge 10).
        eval_cbn.
        unfold le4, le3, le2, le1.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite Hle_s; eval_cbn.
        rewrite Hco; eval_cbn.
        rewrite Hextra_offset; eval_cbn.
        rewrite PTree.gss; eval_cbn.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gss; eval_cbn.
        rewrite (sem_sub_long_int (Int64.repr (Z.of_nat (extra_args s)))
                                   (Int.repr (Z.of_nat required)) m1); eval_cbn.
        rewrite (sem_cast_long_to_long _ m1); eval_cbn.
        rewrite (ptrofs_add_unsigned so 32 ltac:(lia) ltac:(lia)).
        fold new_ea_v.
        rewrite Hstore_ea; eval_cbn.
        reflexivity. }

      (* le' must equal le4 *)
      assert (Hle'_eq : le' = le4).
      { subst le' le4 le3 le2 le1. reflexivity. }
      rewrite Hle'_eq.

      (* Compose: outer Ssequence = (preamble ; Sifthenelse) ; Sreturn *)
      apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m2).

      (* Inner: preamble (S1-S3) ; (S4 ; Sifthenelse) *)
      { apply exec_Sseq_1 with (t1 := E0) (le1 := le2) (m1 := m1).

        (* Preamble: (S1 ; S2) ; S3 *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m1).
          (* S1 ; S2 *)
          { apply exec_Sseq_1 with (t1 := E0) (le1 := le1) (m1 := m).
            - exact Hexec_S1.
            - exact Hexec_S2. }
          (* S3 *)
          { exact Hexec_S3. } }

        (* S4 ; Sifthenelse *)
        { apply exec_Sseq_1 with (t1 := E0) (le1 := le3) (m1 := m1).
          (* S4 *)
          { exact Hexec_S4. }

          (* Sifthenelse *)
          { assert (Hle3_t3 : le3 ! _t'3 = Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
            { unfold le3. rewrite PTree.gss. reflexivity. }
            assert (Hle3_req : le3 ! _required = Some (Vint (Int.repr (Z.of_nat required)))).
            { unfold le3. rewrite PTree.gso by (compute; congruence).
              unfold le2. rewrite PTree.gss. reflexivity. }
            eapply exec_Sifthenelse.
            - (* eval condition: Oge _t'3 _required *)
              eapply eval_Ebinop.
              + eapply eval_Etempvar. exact Hle3_t3.
              + eapply eval_Etempvar. exact Hle3_req.
              + exact (sem_ge_long_int (Int64.repr (Z.of_nat (extra_args s)))
                                        (Int.repr (Z.of_nat required)) m1).
            - (* bool_val *)
              rewrite (grab_ge_iff (extra_args s) required Hreq_range Hea_signed).
              rewrite Hleb. exact (bool_val_of_bool true m1).
            - (* Execute then branch: b = true => s1 *)
              simpl.
              (* Then branch: Ssequence S6 S7 *)
              apply exec_Sseq_1 with (t1 := E0) (le1 := le4) (m1 := m1).
              + exact Hexec_S6.
              + exact Hexec_S7. } } }

      (* S8: Sreturn 0 *)
      { apply exec_Sreturn_some. eapply eval_Econst_int. }
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      set (new_co := Ptrofs.add co (Ptrofs.repr sizeof_code_t)).
      set (ard' := mk_abs_rel sb so hm cb new_co
                     (ar_global_block ard) (ar_global_ofs ard)
                     (ar_stack_block ard) (ar_stack_base_ofs ard)
                     (ar_code_ne_sptr ard) (ar_code_ne_global ard) (ar_global_ne_sptr ard)
                     (ar_sptr_ofs_bound ard)).
      exists ard'.

      set (uso := Ptrofs.unsigned so) in *.
      pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore_ea Hsb_writable_m1) as Hsb_writable_m2.

      (* Thread loads through stores *)

      (* pc at uso+0: written by store_pc in m1, unaffected by store_ea *)
      assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some new_pc_v).
      { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some new_pc_v).
        { pose proof (load_after_store_same m m1 sb (uso + 0) new_pc_v Hstore_pc) as Htmp.
          unfold new_pc_v in Htmp |- *. rewrite load_result_vptr in Htmp. exact Htmp. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 0)
                 new_ea_v new_pc_v Hstore_ea Hpc_m1).
        left. lia. }

      (* accu at uso+8: unaffected by both stores *)
      assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some accu_v).
      { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some accu_v).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 8)
                   new_pc_v accu_v Hstore_pc Haccu_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 8)
                 new_ea_v accu_v Hstore_ea Haccu_m1).
        left. lia. }

      (* sp at uso+16: unaffected by both stores *)
      assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { assert (Hsp_m1 : Mem.load Mint64 m1 sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 16)
                   new_pc_v (Vptr sp_b sp_ofs) Hstore_pc Hsp_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 16)
                 new_ea_v (Vptr sp_b sp_ofs) Hstore_ea Hsp_m1).
        left. lia. }

      (* env at uso+24: unaffected by both stores *)
      assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
      { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 24)
                   new_pc_v env_v Hstore_pc Henv_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 24)
                 new_ea_v env_v Hstore_ea Henv_m1).
        left. lia. }

      (* extra_args at uso+32: written by store_ea *)
      assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) = Some new_ea_v).
      { pose proof (load_after_store_same m1 m2 sb (uso + 32) new_ea_v Hstore_ea) as Htmp.
        unfold new_ea_v in Htmp |- *. rewrite load_result_vlong in Htmp. exact Htmp. }

      (* global_data at uso+40: unaffected *)
      assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
      { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 40)
                   new_pc_v gd_ptr Hstore_pc Hgd_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 40)
                 new_ea_v gd_ptr Hstore_ea Hgd_m1).
        right. lia. }

      (* trap_sp at uso+48: unaffected *)
      assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some ts_ptr).
      { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some ts_ptr).
        { apply (load_after_store_other m m1 sb (uso + 0) (uso + 48)
                   new_pc_v ts_ptr Hstore_pc Hts_load). right. lia. }
        apply (load_after_store_other m1 m2 sb (uso + 32) (uso + 48)
                 new_ea_v ts_ptr Hstore_ea Hts_m1).
        right. lia. }

      (* stack_repr survives: stores are on sb, stack is on sp_b <> sb *)
      assert (Hsb_ne_sp : sb <> sp_b) by (exact (not_eq_sym Hsp_ne_sb)).
      assert (Hstack_repr2 : stack_repr hm cb co m2 (Machine.stack s) sp_b sp_ofs).
      { eapply stack_repr_store_other_block.
        - eapply stack_repr_store_other_block.
          + exact Hstack_repr.
          + exact Hstore_pc.
          + exact Hsb_ne_sp.
        - exact Hstore_ea.
        - exact Hsb_ne_sp. }

      (* global_repr survives: stores on sb, global on gb <> sb *)
      assert (Hsb_ne_gb : sb <> ar_global_block ard) by (exact (not_eq_sym Hgb_ne_sb)).
      assert (Hglobal_repr2 : global_repr hm cb co m2 (Machine.global s)
                (ar_global_block ard) (ar_global_ofs ard)).
      { eapply global_repr_store_other_block.
        - eapply global_repr_store_other_block.
          + exact Hglobal_repr.
          + exact Hstore_pc.
          + exact Hsb_ne_gb.
        - exact Hstore_ea.
        - exact Hsb_ne_gb. }

      (* sp_writable survives *)
      assert (Hsp_writable2 : Mem.range_perm m2 sp_b 0
                (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length (Machine.stack s)))
                Cur Writable).
      { intros ofs' Hofs'.
        eapply Mem.perm_store_1. exact Hstore_ea.
        eapply Mem.perm_store_1. exact Hstore_pc.
        apply Hsp_writable. exact Hofs'. }

      (* The new extra_args value matches *)
      assert (Hnew_ea_eq : new_ea_v = Vlong (Int64.repr (Z.of_nat new_ea))).
      { unfold new_ea_v, new_ea.
        f_equal.
        apply grab_sub_ea; assumption. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- updated to new_pc_v *)
      { exists new_pc_v. split.
        - exact Hpc_load2.
        - simpl. subst new_pc_v new_pc_ofs.
          apply pc_rel_shift. }

      (* 3. accu field -- unchanged *)
      { exists accu_v. split.
        - exact Haccu_load2.
        - simpl. eapply val_repr_co_shift. eassumption. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        simpl.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load2.
        - reflexivity.
        - eapply stack_repr_co_shift. eassumption.
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - exact Hsp_writable2.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load2.
        - simpl. eapply val_repr_co_shift. eassumption. }

      (* 6. extra_args field -- updated *)
      { simpl. rewrite Hnew_ea_eq in Hextra_load2. exact Hextra_load2. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load2.
        - simpl. exact Hgd_eq.
        - simpl. eapply global_repr_co_shift. eassumption.
        - simpl. exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load2.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable *)
      { exact Hsb_writable_m2. }
    }
  }

  (* ================================================================ *)
  (* Case: extra_args < required => else branch                        *)
  (*   The handler builds a closure and matches the return frame.      *)
  (*   Error cases: return frame is malformed (not Val_int::_::Val_int::_). *)
  (*   Step case: precondition requires Nat.leb = true, contradicts Hleb. *)
  (* ================================================================ *)
  {
    (* The else branch of handle_GRAB pattern-matches on skipn.
       We destruct the stack to expose the match result.
       Error cases: prove the precise error predicate (msg, Hleb, stack shape).
       Step case: precondition has Nat.leb = true, contradicting Hleb. *)
    destruct (Machine.stack s) as [| sv0 stl0].
    - (* stack = [] => skipn returns [] => Error "GRAB: malformed return frame" *)
      simpl. exact (conj eq_refl (conj eq_refl I)).
    - (* stack = sv0 :: stl0 *)
      simpl.
      destruct (skipn (extra_args s) stl0) as [| v1 rest1].
      + (* skipn = [] *)
        simpl. exact (conj eq_refl (conj eq_refl I)).
      + destruct rest1 as [| v2 rest2].
        * (* skipn = [v1] => match gives Error for any v1 *)
          destruct v1; simpl; exact (conj eq_refl (conj eq_refl I)).
        * (* rest_stack = v1 :: v2 :: rest2 *)
          destruct v1 as [z1 | | |];
            try (simpl; exact (conj eq_refl (conj eq_refl I))).
          (* v1 = Val_int z1 *)
          destruct rest2 as [| v3 rest3].
          -- (* [Val_int z1; v2] => Error *)
             simpl. exact (conj eq_refl (conj eq_refl I)).
          -- destruct v3 as [z3 | | |];
               try (simpl; exact (conj eq_refl (conj eq_refl I))).
             (* v3 = Val_int z3 => Step, use contradiction *)
             intros ard Hpre Hstep_pre.
             destruct Hstep_pre as (_ & _ & _ & _ & Hleb_eq).
             discriminate Hleb_eq.
  }
Qed.
