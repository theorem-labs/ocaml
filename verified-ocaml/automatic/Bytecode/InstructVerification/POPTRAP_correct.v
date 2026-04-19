(* POPTRAP_correct.v -- POPTRAP handler completeness proof.

   POPTRAP: pops the 4-element trap frame from the stack, restoring
   trap_sp from the encoded trap link at sp[1].

   C code (f_instr_POPTRAP):
     _t'2 = s->sp;                         // read sp
     _t'3 = s->sp;                         // read sp again
     _t'4 = *(cast (_t'3, tptr tlong) + 1);  // read sp[1] (trap link)
     s->trap_sp = _t'2 + (_t'4 >> 1);      // trap_sp = sp + (link >> 1)
     _t'1 = s->sp;                         // read sp
     s->sp = _t'1 + 4;                     // sp += 4 (pop 4 values)
     return 0;

   Rocq:
     handle_POPTRAP pc' s =
       match s.(stack) with
       | _ :: Val_int prev_tsp :: _ :: _ :: rest =>
         Step (s <|pc := pc'|> <|stack := rest|> <|trap_sp := Z.to_nat prev_tsp|>)
       | _ => Error "POPTRAP: malformed trap frame"
       end

   Two stores on the struct block:
     Store 1: trap_sp field (sb, uso+48) <- new trap_sp ptr
     Store 2: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs

   NO AXIOMS. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat Lia.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine Bytecode.Interpret.
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
(* Struct layout lemmas                                                *)
(* ================================================================== *)

Local Definition ce : composite_env :=
  let (ce, _) := build_composite_env' composites Logic.I in ce.

Local Lemma ce_offsets : exists co,
  ce ! _interp_state = Some co /\
  field_offset ce _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset ce _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  eexists. split; [| split]; reflexivity.
Qed.

Local Lemma cenv_is_ce : genv_cenv clight_ge = ce.
Proof. reflexivity. Qed.

Lemma interp_state_co_sp_trapsp : exists co,
  (genv_cenv clight_ge) ! _interp_state = Some co /\
  field_offset (genv_cenv clight_ge) _sp (co_members co) = Errors.OK (16, Full) /\
  field_offset (genv_cenv clight_ge) _trap_sp (co_members co) = Errors.OK (48, Full).
Proof.
  rewrite cenv_is_ce. exact ce_offsets.
Qed.

(* ================================================================== *)
(* Semantic helpers                                                    *)
(* ================================================================== *)

Lemma sem_add_sp_4 : forall sp_b sp_ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr sp_b sp_ofs) (tptr tlong) (Vint (Int.repr 4)) tint m
    = Some (Vptr sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tint) with (add_case_pi tlong Signed).
  unfold sem_add_ptr_int. reflexivity.
Qed.

(* sp + (long): pointer arithmetic on (tptr tlong) + tlong.
   sizeof(tlong) = 8, so sp + n = sp + n * 8 bytes.
   CompCert classifies (tptr tlong) + tlong as add_case_pl tlong. *)
Lemma sem_add_ptr_tlong : forall b ofs n m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong)
    (Vlong n) tlong m
  = Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 n)))).
Proof.
  intros. unfold sem_binary_operation, sem_add.
  change (classify_add (tptr tlong) tlong) with (add_case_pl tlong).
  unfold sem_add_ptr_long. reflexivity.
Qed.

Lemma sem_shr_long_int_1 : forall n m,
  Int.ltu (Int.repr 1) Int64.iwordsize' = true ->
  sem_binary_operation (genv_cenv clight_ge) Oshr
    (Vlong n) tlong (Vint (Int.repr 1)) tint m =
    Some (Vlong (Int64.shr n (Int64.repr 1))).
Proof.
  intros n m _.
  unfold sem_binary_operation, sem_shr, sem_shift.
  change (classify_shift tlong tint) with (shift_case_li Signed).
  simpl.
  change (Int.ltu (Int.repr 1) Int64.iwordsize') with true.
  reflexivity.
Qed.

Lemma iwordsize_ltu_1 : Int.ltu (Int.repr 1) Int64.iwordsize' = true.
Proof. reflexivity. Qed.

(* cast from tlong to tlong is identity for Vlong *)
Lemma sem_cast_long_to_long : forall n m,
  sem_cast (Vlong n) tlong tlong m = Some (Vlong n).
Proof.
  intros. unfold sem_cast. simpl classify_cast.
  rewrite ptr64_true. reflexivity.
Qed.

(* stack_repr for skipn 4 *)
Lemma ptrofs_add_repr : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  intros. rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add;
    apply Ptrofs.eqm_sym;
    apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma stack_repr_skip4 : forall hm cb co m v0 v1 v2 v3 rest sp_b sp_ofs,
  stack_repr hm cb co m (v0 :: v1 :: v2 :: v3 :: rest) sp_b sp_ofs ->
  stack_repr hm cb co m rest sp_b (Ptrofs.add sp_ofs (Ptrofs.repr 32)).
Proof.
  intros hm cb co m v0 v1 v2 v3 rest sp_b sp_ofs Hsr.
  inversion Hsr as [| ? ? ? ? cv0 Hload0 Hvr0 Hsr1]. subst.
  inversion Hsr1 as [| ? ? ? ? cv1 Hload1 Hvr1 Hsr2]. subst.
  inversion Hsr2 as [| ? ? ? ? cv2 Hload2 Hvr2 Hsr3]. subst.
  inversion Hsr3 as [| ? ? ? ? cv3 Hload3 Hvr3 Hsr4]. subst.
  replace (Ptrofs.add sp_ofs (Ptrofs.repr 32))
    with (Ptrofs.add (Ptrofs.add (Ptrofs.add (Ptrofs.add sp_ofs (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)) (Ptrofs.repr 8)).
  - exact Hsr4.
  - rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 8) (Ptrofs.repr 8)) with (Ptrofs.repr 16)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 16) (Ptrofs.repr 8)) with (Ptrofs.repr 24)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    rewrite Ptrofs.add_assoc.
    replace (Ptrofs.add (Ptrofs.repr 24) (Ptrofs.repr 8)) with (Ptrofs.repr 32)
      by (rewrite ptrofs_add_repr; f_equal; lia).
    reflexivity.
Qed.

(* ================================================================== *)
(* Main theorem                                                        *)
(* ================================================================== *)

Theorem verify_POPTRAP_correct :
    handler_correct (handle_POPTRAP) f_instr_POPTRAP
      (fun _ m s ard =>
         (* Stack has at least 4 elements with trap link at position 1 *)
         exists v0 prev_tsp v2 v3 rest,
           Machine.stack s = v0 :: Val_int prev_tsp :: v2 :: v3 :: rest /\
         (* The C-encoded trap link sp[1] is Vlong(prev_tsp*2+1) *)
         (* which when shifted right by 1 gives prev_tsp.
            The C code computes trap_sp = sp + (sp[1] >> 1).
            We need the arithmetic to work out. *)
         (* sp[1] load succeeds and equals the encoded prev_tsp *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
              = Some (Vlong (Int64.repr (prev_tsp * 2 + 1)))) /\
         (* The shift-right arithmetic identity *)
         Int64.shr (Int64.repr (prev_tsp * 2 + 1)) (Int64.repr 1) =
           Int64.repr prev_tsp /\
         (* The ptrofs arithmetic: sp + prev_tsp*8 fits *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus) /\
         (* trap_sp_rel for the new trap_sp value *)
         (forall sp_b sp_ofs,
            Mem.load Mint64 m (ar_sptr_block ard)
              (Ptrofs.unsigned (ar_sptr_ofs ard) + 16) = Some (Vptr sp_b sp_ofs) ->
            trap_sp_rel
              (Vptr sp_b (Ptrofs.add sp_ofs
                 (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr prev_tsp)))))
              (ar_stack_block ard) (ar_stack_base_ofs ard)
              (Z.to_nat prev_tsp)))
      (fun msg _ => msg = "POPTRAP: malformed trap frame"%string)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct, handle_POPTRAP. simpl.

  (* Case split on stack shape *)
  destruct (Machine.stack s) as [| v0 stk1] eqn:Hstk.
  - (* stack = [] -- Error case *)
    reflexivity.
  - destruct stk1 as [| v1 stk2].
    + (* stack = [v0] -- Error *)
      reflexivity.
    + destruct v1 as [z1 | | |].
      * (* v1 = Val_int z1 *)
        destruct stk2 as [| v2 stk3].
        -- (* stack = [v0; Val_int z1] -- Error *)
           reflexivity.
        -- destruct stk3 as [| v3 rest].
           ++ (* stack = [v0; Val_int z1; v2] -- Error *)
              reflexivity.
           ++ (* stack = v0 :: Val_int z1 :: v2 :: v3 :: rest -- Step case! *)
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

              destruct Hstep_pre as (v0_ & prev_tsp & v2_ & v3_ & rest_ & Hstk_eq &
                Hsp1_load & Hshr_eq & Hrest_rep & Htrap_rel_new).

              (* Stack equation: the quantified stack must match the destructed pattern *)
              injection Hstk_eq as Heq0 Htsp_eq Heq2 Heq3 Heqrest.
              subst v0_ v2_ v3_ rest_ prev_tsp.

              (* Structural invariants *)
              pose proof (sptr_ofs_representable ard) as Hso_bound. fold so in Hso_bound.
              pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].
              pose proof (global_block_ne_sptr ard) as Hgb_ne. fold sb in Hgb_ne.

              (* sp[1] load *)
              assert (Hsp1 : Mem.load Mint64 m sp_b (Ptrofs.unsigned (Ptrofs.add sp_ofs (Ptrofs.repr 8)))
                             = Some (Vlong (Int64.repr (z1 * 2 + 1)))).
              { apply (Hsp1_load sp_b sp_ofs). exact Hsp_load. }

              (* rest representability *)
              rewrite Hstk in Hsp_rep. simpl length in Hsp_rep.
              assert (Hrest_fits : Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest) < Ptrofs.modulus).
              { apply (Hrest_rep sp_b sp_ofs). exact Hsp_load. }

              (* new trap_sp value *)
              set (new_trap_ptr :=
                Vptr sp_b (Ptrofs.add sp_ofs
                  (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr z1))))).
              assert (Htrap_new : trap_sp_rel new_trap_ptr
                        (ar_stack_block ard) (ar_stack_base_ofs ard) (Z.to_nat z1)).
              { apply (Htrap_rel_new sp_b sp_ofs). exact Hsp_load. }

              (* Composite environment *)
              destruct interp_state_co_sp_trapsp as [co_is [Hco [Hsp_offset Htrap_offset]]].

              (* New sp offset *)
              set (new_sp_ofs := Ptrofs.add sp_ofs (Ptrofs.repr 32)).

              (* ============================================================ *)
              (* Store 1: trap_sp field (sb, uso+48) <- new_trap_ptr          *)
              (* ============================================================ *)
              destruct (store_succeeds_sb m sb so 48 ts_ptr Hsb_writable Hts_load ltac:(lia) ltac:(lia) new_trap_ptr) as [m1 Hstore1].
              pose proof (sb_writable_after_store _ _ _ _ _ _ _ _ Hstore1 Hsb_writable) as Hsb_writable_m1.

              (* ============================================================ *)
              (* Store 2: sp field (sb, uso+16) <- Vptr sp_b new_sp_ofs       *)
              (* ============================================================ *)
              assert (Hsp_load_m1 : Mem.load Mint64 m1 sb (Ptrofs.unsigned so + 16) =
                        Some (Vptr sp_b sp_ofs)).
              { apply (load_after_store_other m m1 sb (Ptrofs.unsigned so + 48)
                         (Ptrofs.unsigned so + 16) new_trap_ptr (Vptr sp_b sp_ofs)
                         Hstore1 Hsp_load). left. lia. }
              destruct (store_succeeds_sb m1 sb so 16 (Vptr sp_b sp_ofs) Hsb_writable_m1 Hsp_load_m1 ltac:(lia) ltac:(lia) (Vptr sp_b new_sp_ofs)) as [m2 Hstore2].

              (* Witnesses *)
              set (le' := PTree.set _t'1 (Vptr sp_b sp_ofs)
                          (PTree.set _t'4 (Vlong (Int64.repr (z1 * 2 + 1)))
                          (PTree.set _t'3 (Vptr sp_b sp_ofs)
                          (PTree.set _t'2 (Vptr sp_b sp_ofs) le)))).
              exists le'. exists m2.
              exists (Out_return (Some (Vint (Int.repr 0), tint))).

              split.

              (* ============================================================ *)
              (* Part 1: exec via computational evaluator                      *)
              (* ============================================================ *)
              {
                apply (eval_stmt_to_exec clight_ge 15).
                eval_cbn.

                (* S1: Sset _t'2 (s->sp) -- read sp pointer *)
                rewrite Hle_s; eval_cbn.
                rewrite Hco; eval_cbn.
                rewrite Hsp_offset; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                rewrite Hsp_load; eval_cbn.

                (* S2: Sset _t'3 (s->sp) -- read sp again.
                   After S1's rewrite Hco, the composite lookup is resolved
                   and cbn can see through. We just need field_offset. *)
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_s; eval_cbn.
                try rewrite Hco; eval_cbn.
                try rewrite Hsp_offset; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                rewrite Hsp_load; eval_cbn.

                (* S3: Sset _t'4 (deref (cast _t'3 + 1)) -- read sp[1] *)
                rewrite PTree.gss; eval_cbn.
                rewrite sem_cast_ptr_to_ptr; eval_cbn.
                rewrite sem_add_sp_1; eval_cbn.
                rewrite Hsp1; eval_cbn.

                (* S4: Sassign (s->trap_sp) (_t'2 + (cast _t'4 >> 1)) *)
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_s; eval_cbn.
                try rewrite Hco; eval_cbn.
                try rewrite Htrap_offset; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                (* Rvalue: _t'2 + (cast _t'4 >> 1) *)
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gss; eval_cbn.
                rewrite PTree.gss; eval_cbn.
                rewrite sem_cast_long_to_long; eval_cbn.
                rewrite (sem_shr_long_int_1 _ m iwordsize_ltu_1); eval_cbn.
                rewrite Hshr_eq; eval_cbn.
                rewrite (sem_add_ptr_tlong sp_b sp_ofs (Int64.repr z1) m); eval_cbn.
                rewrite sem_cast_ptr_to_ptr; eval_cbn.
                rewrite (ptrofs_add_unsigned so 48 ltac:(lia) ltac:(lia)).
                fold new_trap_ptr.
                rewrite Hstore1; eval_cbn.

                (* S5: Sset _t'1 (s->sp) -- read sp again *)
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_s; eval_cbn.
                try rewrite Hco; eval_cbn.
                try rewrite Hsp_offset; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                (* sp field in m1: survived store at offset 48 *)
                rewrite Hsp_load_m1; eval_cbn.

                (* S6: Sassign (s->sp) (_t'1 + 4) *)
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite PTree.gso by (compute; congruence).
                rewrite Hle_s; eval_cbn.
                try rewrite Hco; eval_cbn.
                try rewrite Hsp_offset; eval_cbn.
                rewrite Mptr_Mint64; eval_cbn.
                rewrite PTree.gss; eval_cbn.
                rewrite sem_add_sp_4; eval_cbn.
                rewrite sem_cast_ptr_to_ptr; eval_cbn.
                rewrite (ptrofs_add_unsigned so 16 ltac:(lia) ltac:(lia)).
                fold new_sp_ofs.
                rewrite Hstore2; eval_cbn.

                (* S7: Sreturn 0 *)
                subst le'. reflexivity.
              }

              (* ============================================================ *)
              (* Part 2: abs_rel for post-state                                *)
              (* ============================================================ *)
              {
                exists ard.
                set (uso := Ptrofs.unsigned so) in *.

                (* Field loads through both stores *)

                (* pc: uso+0, unaffected by store1 at 48, unaffected by store2 at 16 *)
                assert (Hpc_load2 : Mem.load Mint64 m2 sb (uso + 0) = Some pc_ptr).
                { assert (Hpc_m1 : Mem.load Mint64 m1 sb (uso + 0) = Some pc_ptr).
                  { apply (load_after_store_other m m1 sb (uso + 48) (uso + 0)
                             new_trap_ptr pc_ptr Hstore1 Hpc_load). left. lia. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 0)
                           (Vptr sp_b new_sp_ofs) pc_ptr Hstore2 Hpc_m1). left. lia. }

                (* accu: uso+8 *)
                assert (Haccu_load2 : Mem.load Mint64 m2 sb (uso + 8) = Some accu_v).
                { assert (Haccu_m1 : Mem.load Mint64 m1 sb (uso + 8) = Some accu_v).
                  { apply (load_after_store_other m m1 sb (uso + 48) (uso + 8)
                             new_trap_ptr accu_v Hstore1 Haccu_load). left. lia. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 8)
                           (Vptr sp_b new_sp_ofs) accu_v Hstore2 Haccu_m1). left. lia. }

                (* sp: uso+16, written by store2 *)
                assert (Hsp_load2 : Mem.load Mint64 m2 sb (uso + 16) =
                          Some (Vptr sp_b new_sp_ofs)).
                { pose proof (load_after_store_same m1 m2 sb (uso + 16)
                                (Vptr sp_b new_sp_ofs) Hstore2) as Htmp.
                  simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }

                (* env: uso+24 *)
                assert (Henv_load2 : Mem.load Mint64 m2 sb (uso + 24) = Some env_v).
                { assert (Henv_m1 : Mem.load Mint64 m1 sb (uso + 24) = Some env_v).
                  { apply (load_after_store_other m m1 sb (uso + 48) (uso + 24)
                             new_trap_ptr env_v Hstore1 Henv_load). left. lia. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 24)
                           (Vptr sp_b new_sp_ofs) env_v Hstore2 Henv_m1). right. lia. }

                (* extra_args: uso+32 *)
                assert (Hextra_load2 : Mem.load Mint64 m2 sb (uso + 32) =
                          Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
                { assert (Hextra_m1 : Mem.load Mint64 m1 sb (uso + 32) =
                            Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
                  { apply (load_after_store_other m m1 sb (uso + 48) (uso + 32)
                             new_trap_ptr _ Hstore1 Hextra_load). left. lia. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 32)
                           (Vptr sp_b new_sp_ofs) _ Hstore2 Hextra_m1). right. lia. }

                (* global_data: uso+40 *)
                assert (Hgd_load2 : Mem.load Mint64 m2 sb (uso + 40) = Some gd_ptr).
                { assert (Hgd_m1 : Mem.load Mint64 m1 sb (uso + 40) = Some gd_ptr).
                  { apply (load_after_store_other m m1 sb (uso + 48) (uso + 40)
                             new_trap_ptr gd_ptr Hstore1 Hgd_load). left. lia. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 40)
                           (Vptr sp_b new_sp_ofs) gd_ptr Hstore2 Hgd_m1). right. lia. }

                (* trap_sp: uso+48, written by store1, preserved by store2 at 16 *)
                assert (Hts_load2 : Mem.load Mint64 m2 sb (uso + 48) = Some new_trap_ptr).
                { assert (Hts_m1 : Mem.load Mint64 m1 sb (uso + 48) = Some new_trap_ptr).
                  { pose proof (load_after_store_same m m1 sb (uso + 48)
                                  new_trap_ptr Hstore1) as Htmp.
                    unfold new_trap_ptr in Htmp |- *.
                    simpl in Htmp. rewrite ptr64_true in Htmp. exact Htmp. }
                  apply (load_after_store_other m1 m2 sb (uso + 16) (uso + 48)
                           (Vptr sp_b new_sp_ofs) new_trap_ptr Hstore2 Hts_m1).
                  right. lia. }

                split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

                (* 1. le' ! _s *)
                { subst le'.
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  rewrite PTree.gso by (compute; congruence).
                  exact Hle_s. }

                (* 2. pc field -- unchanged *)
                { exists pc_ptr. split.
                  - exact Hpc_load2.
                  - simpl. exact Hpc_rel. }

                (* 3. accu field -- unchanged *)
                { exists accu_v. split.
                  - exact Haccu_load2.
                  - simpl. exact Haccu_repr. }

                (* 4. sp field -- updated to new_sp_ofs; stack is rest *)
                { exists (Vptr sp_b new_sp_ofs), sp_b, new_sp_ofs.
                  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
                  - exact Hsp_load2.
                  - reflexivity.
                  - simpl.
                    (* stack_repr for rest at new_sp_ofs = sp_ofs + 32 *)
                    assert (Hstack_m1 : stack_repr hm cb co m1 (v0 :: Val_int z1 :: v2 :: v3 :: rest) sp_b sp_ofs).
                    { rewrite <- Hstk.
                      apply (stack_repr_store_other_block hm cb co m m1 _ sp_b sp_ofs sb
                               (uso + 48) new_trap_ptr Hstack_repr Hstore1).
                      intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
                    assert (Hstack_m2 : stack_repr hm cb co m2 (v0 :: Val_int z1 :: v2 :: v3 :: rest) sp_b sp_ofs).
                    { apply (stack_repr_store_other_block hm cb co m1 m2 _ sp_b sp_ofs sb
                               (uso + 16) (Vptr sp_b new_sp_ofs) Hstack_m1 Hstore2).
                      intro Heq; exact (Hsp_ne_sb (eq_sym Heq)). }
                    exact (stack_repr_skip4 hm cb co m2 v0 (Val_int z1) v2 v3 rest sp_b sp_ofs Hstack_m2).
                  - exact Hsp_ne_sb.
                  - exact Hsp_ne_gb.
                  - exact Hcb_ne_sp.
                  - (* sp_ge8: new_sp_ofs = sp_ofs + 32 >= 8 *)
                    unfold new_sp_ofs.
                    rewrite (ptrofs_add_unsigned sp_ofs 32 ltac:(lia) ltac:(lia)).
                    lia.
                  - (* sp_rep *)
                    simpl.
                    unfold new_sp_ofs.
                    rewrite (ptrofs_add_unsigned sp_ofs 32 ltac:(lia) ltac:(lia)).
                    exact Hrest_fits.
                  - (* sp_writable *)
                    simpl.
                    unfold new_sp_ofs.
                    rewrite (ptrofs_add_unsigned sp_ofs 32 ltac:(lia) ltac:(lia)).
                    assert (Hwritable_old : Mem.range_perm m sp_b 0
                              (Ptrofs.unsigned sp_ofs + 32 + 8 * Z.of_nat (length rest)) Cur Writable).
                    { intros ofs' Hofs'.
                      rewrite Hstk in Hsp_writable. simpl length in Hsp_writable.
                      apply Hsp_writable. rewrite !Nat2Z.inj_succ. lia. }
                    intros ofs' Hofs'.
                    eapply Mem.perm_store_1. exact Hstore2.
                    eapply Mem.perm_store_1. exact Hstore1.
                    apply Hwritable_old. assumption.
                  - (* sp_align *)
                    unfold new_sp_ofs.
                    rewrite (ptrofs_add_unsigned sp_ofs 32 ltac:(lia) ltac:(lia)).
                    simpl. apply Z.divide_add_r. exact Hsp_align. exists 4; lia. }

                (* 5. env field -- unchanged *)
                { exists env_v. split.
                  - exact Henv_load2.
                  - simpl. exact Henv_repr. }

                (* 6. extra_args field -- unchanged *)
                { simpl. exact Hextra_load2. }

                (* 7. global_data field -- unchanged *)
                { exists gd_ptr. split; [| split; [| split]].
                  - exact Hgd_load2.
                  - simpl. exact Hgd_eq.
                  - simpl.
                    apply (global_repr_store_other_block hm cb co m1 m2 _
                             (ar_global_block ard) (ar_global_ofs ard)
                             sb (uso + 16) (Vptr sp_b new_sp_ofs)).
                    + apply (global_repr_store_other_block hm cb co m m1 _
                               (ar_global_block ard) (ar_global_ofs ard)
                               sb (uso + 48) new_trap_ptr
                               Hglobal_repr Hstore1).
                      intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
                    + exact Hstore2.
                    + intro Heq2; exact (Hgb_ne (eq_sym Heq2)).
                  - exact Hgb_ne_sb. }

                (* 8. trap_sp field -- updated *)
                { exists new_trap_ptr. split.
                  - exact Hts_load2.
                  - simpl. exact Htrap_new. }

                (* 9. sb_writable *)
                { intros ofs' Hofs'.
                  eapply Mem.perm_store_1. exact Hstore2.
                  eapply Mem.perm_store_1. exact Hstore1.
                  apply Hsb_writable. exact Hofs'. }
              }
      * (* v1 = Val_ptr -- Error *)
        reflexivity.
      * (* v1 = Val_closure -- Error *)
        reflexivity.
      * (* v1 = Val_block -- Error *)
        reflexivity.
Qed.
