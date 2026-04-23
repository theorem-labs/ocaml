(* GETFIELD0_correct.v -- GETFIELD0 correctness proof.

   GETFIELD0: accu = Field(accu, 0), i.e., load the first field from
   the heap block pointed to by accu.

   Rocq handler (Interpret.v):
     handle_GETFIELD 0 pc' s =
       match field_or_heap s s.(accu) 0 with
       | Some v => Step (s <|pc:=pc'|> <|accu:=v|>)
       | None => Error "GETFIELD: access failed"
       end

   C handler (instruct_handlers.v, f_instr_GETFIELD0):
     t1 = s->accu;
     t2 = deref((long ptr)t1 + 0);   // deref accu as pointer, field 0
     s->accu = t2;
     return 0;

   KEY CHALLENGE — heap model gap:
   The C handler dereferences accu as a pointer: Mem.load Mint64 m b ofs.
   The Rocq handler uses field_or_heap, which looks up the heap map.
   Connecting these requires a heap invariant relating the Rocq heap
   (hp : PositiveMap of (tag, fields)) to C memory (Mem.load at the
   blocks/offsets tracked by ar_heap_map).

   abs_rel does NOT include a heap invariant — it only relates the
   struct fields (pc, accu, sp, env, extra_args, global_data, trap_sp),
   the stack region, and the global data array.  It does not assert
   anything about the contents of heap-allocated blocks in C memory.

   APPROACH:
   - Error case: fully proved (trivial — handler returns Error iff
     field_or_heap returns None, which is exactly the error predicate).
   - Step case: proved using handler_correct_v1 with a heap
     precondition (heap_field_loadable) that asserts:
       When field_or_heap s (accu s) 0 = Some v, there exists a C value
       cv such that:
       (a) accu_v is Vptr b ofs (the accu is a pointer in C)
       (b) Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv
       (c) val_repr hm cb co v cv
     This is exactly the missing link between field_or_heap and Mem.load.

   TO UPGRADE to plain handler_correct_v1 (no precondition), add to abs_rel:
     forall addr b ofs tag fields,
       hm addr = Some (b, ofs) ->
       heap_lookup (hp s) addr = Some (tag, fields) ->
       forall i v, nth_error fields i = Some v ->
       exists cv, Mem.load Mint64 m b (Ptrofs.unsigned ofs + Z.of_nat i * 8)
                    = Some cv /\ val_repr hm cb co v cv
   plus the constraint that val_repr values that are Vptr always have
   their first argument derivable from hm.  With this invariant in
   abs_rel, the heap_field_loadable precondition would be derivable
   and handler_correct_v1 would imply handler_correct_v1.

   No Axioms, no Admitted, no vm_compute on Ptrofs. *)

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
From OCamlInterp.Automatic Require Import Bytecode.Interpret.InstructSpecHelpers.
From OCamlInterp.Automatic Require Import Bytecode.StepToBigstep.
From OCamlInterp.Automatic Require Import Bytecode.HandlerLemmas.

Local Notation ge := clight_ge.

Local Ltac eval_cbn :=
  cbn -[clight_ge genv_cenv Mptr
        sem_binary_operation sem_cast
        Mem.load Mem.store
        Ptrofs.unsigned Ptrofs.add Ptrofs.repr Ptrofs.mul
        ptrofs_of_int
        field_offset
        PTree.get PTree.set].

(* ================================================================== *)
(* Semantic lemma: cast tlong -> (tptr tlong) for Vptr                 *)
(* ================================================================== *)

Lemma sem_cast_long_to_ptr_vptr : forall b ofs m,
  sem_cast (Vptr b ofs) tlong (tptr tlong) m = Some (Vptr b ofs).
Proof.
  intros. unfold sem_cast. simpl classify_cast. reflexivity.
Qed.

(* sem_add for (tptr tlong) + 0 -- reuses sem_add_sp_0 pattern *)
Lemma sem_add_ptr_long_0 : forall b ofs m,
  sem_binary_operation (genv_cenv clight_ge) Oadd
    (Vptr b ofs) (tptr tlong) (Vint (Int.repr 0)) tint m
    = Some (Vptr b ofs).
Proof. exact sem_add_sp_0. Qed.

(* ================================================================== *)
(* Heap field precondition                                             *)
(* ================================================================== *)

(* Local copy matching the generic heap_field_loadable 0 from InstructSpec.
   Uses Ptrofs.add ofs (Ptrofs.repr 0) instead of bare ofs, so the
   theorem type is definitionally equal to the Module Type entry. *)
Local Definition heap_field_loadable_0
    (_ : Clight.env) (m : mem) (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  forall v,
    field_or_heap s s.(Machine.accu) 0 = Some v ->
    forall accu_v,
      val_repr hm cb co s.(Machine.accu) accu_v ->
      exists b ofs cv,
        accu_v = Vptr b ofs /\
        Mem.load Mint64 m b (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat 0 * 8)))) = Some cv /\
        val_repr hm cb co v cv.

(* ================================================================== *)
(* Main theorem: GETFIELD0 with heap precondition                      *)
(* ================================================================== *)

Theorem verify_GETFIELD0_with_pre :
    handler_correct_v1 (handle_GETFIELD 0) f_instr_GETFIELD0
      (heap_field_loadable 0)
      (fun _ s => field_or_heap s s.(Machine.accu) 0 = None)
      (fun _ => False) (fun _ _ _ => False).
Proof.
  intros e le m s.
  unfold handler_correct_v1, handle_GETFIELD.
  destruct (field_or_heap s s.(Machine.accu) 0) as [v|] eqn:Hfoh.

  (* ================================================================ *)
  (* Case 1: field_or_heap = Some v => Step                            *)
  (* ================================================================ *)
  2: { (* Case 2: field_or_heap = None => Error *)
    reflexivity.
  }
  {
    intros ard Hpre Hhfl.

    (* Unpack abs_rel_with_ard *)
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

    (* Structural invariants *)
    pose proof (sptr_ofs_representable ard) as Hso_bound.
    fold so in Hso_bound.
    pose proof (Ptrofs.unsigned_range so) as [Hso_pos _].

    (* Use heap precondition to get the field value in C memory *)
    unfold heap_field_loadable in Hhfl.
    destruct (Hhfl v Hfoh accu_v Haccu_repr)
      as [b [ofs [cv [Haccu_is_ptr [Hfield_load Hfield_repr]]]]].
    (* Bridge: Ptrofs.add ofs (Ptrofs.repr 0) -> ofs
       (Z.of_nat 0 * 8 reduces to 0 after unfold) *)
    rewrite Ptrofs.add_zero in Hfield_load.
    subst accu_v.

    (* Composite environment facts *)
    destruct interp_state_co as [co_is [Hco [Hsp_offset Haccu_offset]]].

    (* Accu store must succeed *)
    destruct (store_succeeds_sb m sb so 8 (Vptr b ofs) Hsb_writable Haccu_load ltac:(lia) ltac:(lia) cv) as [m' Hstore].

    (* Witnesses *)
    set (le' := PTree.set _t'2 cv (PTree.set _t'1 (Vptr b ofs) le)).
    exists le'. exists m'.
    exists (Out_return (Some (Vint (Int.repr 0), tint))).

    split.

    (* ============================================================== *)
    (* Part 1: exec via computational evaluator                        *)
    (*                                                                  *)
    (* The C body executes:                                             *)
    (*   t1 = s->accu                  (load accu from struct)         *)
    (*   t2 = deref(cast(t1) + 0)     (cast to ptr, deref field 0)    *)
    (*   s->accu = t2                  (store result back)             *)
    (*   return 0                                                      *)
    (* ============================================================== *)
    {
      apply (eval_stmt_to_exec clight_ge 10).

      (* --- Initial reduction --- *)
      eval_cbn.

      (* === Sset _t'1 (s->accu) === *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      rewrite Hco; eval_cbn.                                         (* composite lookup *)
      rewrite Haccu_offset; eval_cbn.                                (* field_offset _accu *)
      (* eval_cbn resolves access_mode tlong = By_value Mint64 *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Haccu_load; eval_cbn.                                  (* accu load *)

      (* === Sset _t'2 : deref (cast(_t'1) + 0) === *)
      rewrite PTree.gss; eval_cbn.                                   (* le1 ! _t'1 *)
      (* Cast: tlong -> (tptr tlong) for Vptr *)
      rewrite sem_cast_long_to_ptr_vptr; eval_cbn.                   (* sem_cast *)
      (* Add: ptr + 0 *)
      rewrite (sem_add_ptr_long_0 b ofs m); eval_cbn.               (* sem_add *)
      (* Deref: load field 0 from heap block *)
      rewrite Hfield_load; eval_cbn.                                 (* field load *)

      (* === Sassign (s->accu = _t'2) === *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'2 *)
      rewrite PTree.gso by (compute; congruence).                    (* le2 ! _s: skip _t'1 *)
      rewrite Hle_s; eval_cbn.                                       (* le ! _s *)
      (* eval_cbn resolves the struct deref and field_offset for write *)

      (* === Sassign rvalue + sem_cast + store === *)
      rewrite PTree.gss; eval_cbn.                                   (* le2 ! _t'2 *)
      rewrite (sem_cast_long_val_repr _ _ _ _ _ _ Hfield_repr); eval_cbn. (* sem_cast *)
      rewrite (ptrofs_add_unsigned so 8 ltac:(lia) ltac:(lia)).      (* accu ptrofs *)
      rewrite Hstore; eval_cbn.                                      (* accu store *)

      (* === Sreturn 0 -- reduces automatically === *)
      subst le'. reflexivity.
    }

    (* ============================================================== *)
    (* Part 2: abs_rel for post-state                                  *)
    (* ============================================================== *)
    {
      exists ard.
      set (uso := Ptrofs.unsigned so) in *.

      assert (Hpc_load' : Mem.load Mint64 m' sb (uso + 0) = Some pc_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 0) cv pc_ptr
                 Hstore Hpc_load). left. lia. }

      assert (Hsp_load' : Mem.load Mint64 m' sb (uso + 16) = Some (Vptr sp_b sp_ofs)).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 16) cv (Vptr sp_b sp_ofs)
                 Hstore Hsp_load). right. lia. }

      assert (Henv_load' : Mem.load Mint64 m' sb (uso + 24) = Some env_v).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 24) cv env_v
                 Hstore Henv_load). right. lia. }

      assert (Hextra_load' : Mem.load Mint64 m' sb (uso + 32) =
                Some (Vlong (Int64.repr (Z.of_nat (extra_args s))))).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 32) cv _
                 Hstore Hextra_load). right. lia. }

      assert (Hgd_load' : Mem.load Mint64 m' sb (uso + 40) = Some gd_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 40) cv gd_ptr
                 Hstore Hgd_load). right. lia. }

      assert (Hts_load' : Mem.load Mint64 m' sb (uso + 48) = Some ts_ptr).
      { apply (load_after_store_other m m' sb (uso + 8) (uso + 48) cv ts_ptr
                 Hstore Hts_load). right. lia. }

      assert (Haccu_load' : Mem.load Mint64 m' sb (uso + 8) = Some cv).
      { pose proof (load_after_store_same m m' sb (uso + 8) cv Hstore) as Htmp.
        rewrite (val_repr_load_result hm cb co v cv Hfield_repr) in Htmp.
        exact Htmp. }

      split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].

      (* 1. _s is in le' *)
      { subst le'.
        rewrite PTree.gso by (compute; congruence).
        rewrite PTree.gso by (compute; congruence).
        exact Hle_s. }

      (* 2. pc field -- unchanged *)
      { exists pc_ptr. split.
        - exact Hpc_load'.
        - simpl. exact Hpc_rel. }

      (* 3. accu field -- updated to field value *)
      { exists cv. split.
        - exact Haccu_load'.
        - simpl. exact Hfield_repr. }

      (* 4. sp field -- unchanged *)
      { exists (Vptr sp_b sp_ofs), sp_b, sp_ofs.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
        - exact Hsp_load'.
        - reflexivity.
        - simpl.
          apply (stack_repr_store_other_block hm cb co m m' _ sp_b sp_ofs sb (uso + 8) cv
                   Hstack_repr Hstore).
          intro Heq; exact (Hsp_ne_sb (eq_sym Heq)).
        - exact Hsp_ne_sb.
        - exact Hsp_ne_gb.
        - exact Hcb_ne_sp.
        - exact Hsp_ge8.
        - exact Hsp_rep.
        - intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsp_writable. exact Hofs'.
        - exact Hsp_align. }

      (* 5. env field -- unchanged *)
      { exists env_v. split.
        - exact Henv_load'.
        - simpl. exact Henv_repr. }

      (* 6. extra_args field -- unchanged *)
      { simpl. exact Hextra_load'. }

      (* 7. global_data field -- unchanged *)
      { exists gd_ptr. split; [| split; [| split]].
        - exact Hgd_load'.
        - simpl. exact Hgd_eq.
        - simpl.
          apply (global_repr_store_other_block hm cb co m m' _ _ _ sb (uso + 8) cv
                   Hglobal_repr Hstore).
          intro Heq2; exact (global_block_ne_sptr ard (eq_sym Heq2)).
        - exact Hgb_ne_sb. }

      (* 8. trap_sp field -- unchanged *)
      { exists ts_ptr. split.
        - exact Hts_load'.
        - simpl. exact Htrap_rel. }

      (* 9. sb_writable -- permission preserved *)
      { intros ofs' Hofs'. eapply Mem.perm_store_1. exact Hstore. apply Hsb_writable. exact Hofs'. }
    }
  }
Qed.
