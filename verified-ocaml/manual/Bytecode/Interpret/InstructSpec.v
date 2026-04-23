(* InstructSpec.v — Specification relating Clight instruction handlers
   (from clightgen) to Rocq handle_X functions (from Interpret.v).

   Architecture:
   - instruct_handlers.v provides the Clight AST (f_instr_X definitions)
   - Interpret.v provides the Rocq handlers (handle_X definitions)
   - This file defines abs_rel (C state <-> Rocq state) and declares
     per-handler correctness theorems as a Module Type.
   - A future Module : InstructSpec fills each theorem with a proof. *)

From Stdlib Require Import ZArith List Strings.String PeanoNat.
Import ListNotations.
From compcert Require Import Coqlib Integers Floats Ctypes Cop
  Clight Clightdefs Globalenvs Maps Memory Memdata Events Values.
From compcert Require Import ClightBigstep.
From compcert Require Import AST.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual Require Import Utils.Value.
From OCamlInterp.Manual Require Import Bytecode.Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Helpers HandleInstrSpec.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual Require Import Bytecode.Generated.instruct_handlers.

Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(* External function ident not produced by clightgen (caml_modify is a
   runtime helper referenced by SETFIELD / SETVECTITEM specs but not
   directly called from the extracted handler C code). *)
Import Clightdefs.ClightNotations.
Local Open Scope clight_scope.
Definition _caml_modify : ident := $"caml_modify".
Local Close Scope clight_scope.

(* ================================================================== *)
(* Clight environment                                                  *)
(* ================================================================== *)

Definition clight_ge : Clight.genv :=
  {| genv_genv := Globalenvs.Genv.globalenv prog;
     genv_cenv := prog_comp_env prog |}.

(* sizeof(code_t) = 4 bytes (int32_t in the C source) *)
Definition sizeof_code_t : Z := 4.

(* ================================================================== *)
(* Abstraction relation                                                *)
(* ================================================================== *)

Record abs_rel_data := mk_abs_rel {
  ar_sptr_block : block;
  ar_sptr_ofs   : ptrofs;
  ar_heap_map   : nat -> option (block * ptrofs);
  (* Code base pointer: C pc = code_base + rocq_pc * sizeof_code_t *)
  ar_code_base_block : block;
  ar_code_base_ofs   : ptrofs;
  (* Global data array base *)
  ar_global_block : block;
  ar_global_ofs   : ptrofs;
  (* Stack base (bottom) for trap_sp computation *)
  ar_stack_block    : block;
  ar_stack_base_ofs : ptrofs;
  (* Block separation: code block is distinct from struct, global blocks *)
  ar_code_ne_sptr   : ar_code_base_block <> ar_sptr_block;
  ar_code_ne_global : ar_code_base_block <> ar_global_block;
  (* Global block is distinct from struct pointer block *)
  ar_global_ne_sptr : ar_global_block <> ar_sptr_block;
  (* Struct pointer offset representability *)
  ar_sptr_ofs_bound : Ptrofs.unsigned ar_sptr_ofs + 56 < Ptrofs.modulus;
}.

(* val_repr: a Rocq value corresponds to a CompCert value.
   Parameters: hm = heap map, cb = code base block, co = code base offset.
   The vr_code_ptr constructor enables Val_int (bytecode PC) to be
   represented as Vptr in the code section — needed for return addresses
   and handler PCs stored on the stack. *)
Inductive val_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs)
    : Value.value -> val -> Prop :=
  | vr_int : forall z,
      val_repr hm cb co (Val_int z) (Vlong (Int64.repr (z * 2 + 1)))
  | vr_ptr : forall addr b ofs,
      hm addr = Some (b, ofs) ->
      val_repr hm cb co (Val_ptr addr) (Vptr b ofs)
  | vr_closure : forall addr offset b ofs delta,
      hm addr = Some (b, ofs) ->
      delta = Ptrofs.repr (Z.of_nat offset * 8) ->
      val_repr hm cb co (Val_closure addr offset) (Vptr b (Ptrofs.add ofs delta))
  | vr_block_atom : forall tag,
      val_repr hm cb co (Val_block tag nil)
        (Vlong (Int64.repr (Z.of_nat tag * 1024)))
  | vr_code_ptr : forall pc co_val,
      val_repr hm cb co (Val_int pc)
        (Vptr cb (Ptrofs.add co_val (Ptrofs.repr (pc * sizeof_code_t)))).

(* stack_repr: Rocq stack (list value) corresponds to a C stack region *)
Inductive stack_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | sr_nil : forall b ofs,
      stack_repr hm cb co m nil b ofs
  | sr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm cb co v cv ->
      stack_repr hm cb co m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      stack_repr hm cb co m (v :: vs) b ofs.

(* global_repr: Rocq global array corresponds to C memory region *)
Inductive global_repr (hm : nat -> option (block * ptrofs))
    (cb : block) (co : ptrofs) (m : mem)
    : list Value.value -> block -> ptrofs -> Prop :=
  | gr_nil : forall b ofs,
      global_repr hm cb co m nil b ofs
  | gr_cons : forall v vs b ofs cv,
      Mem.load Mint64 m b (Ptrofs.unsigned ofs) = Some cv ->
      val_repr hm cb co v cv ->
      global_repr hm cb co m vs b (Ptrofs.add ofs (Ptrofs.repr 8)) ->
      global_repr hm cb co m (v :: vs) b ofs.

(* pc_rel: C pc pointer encodes Rocq program counter *)
Definition pc_rel (pc_ptr : val)
    (code_base_b : block) (code_base_ofs : ptrofs) (rocq_pc : Z) : Prop :=
  pc_ptr = Vptr code_base_b
    (Ptrofs.add code_base_ofs (Ptrofs.repr (rocq_pc * sizeof_code_t))).

(* trap_sp_rel: C trap_sp pointer corresponds to Rocq trap_sp *)
Definition trap_sp_rel (ts_ptr : val)
    (sp_b : block) (sp_base_ofs : ptrofs) (rocq_trap_sp : nat) : Prop :=
  match rocq_trap_sp with
  | O => True
  | S _ =>
      ts_ptr = Vptr sp_b
        (Ptrofs.sub sp_base_ofs (Ptrofs.repr (Z.of_nat rocq_trap_sp * 8)))
  end.

(* abs_rel_with_ard: exposes the abs_rel_data witness so that
   preconditions can refer to specific fields (code base, etc.). *)
Definition abs_rel_with_ard (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) (ard : abs_rel_data) : Prop :=
  let sb := ar_sptr_block ard in
  let so := ar_sptr_ofs ard in
  let hm := ar_heap_map ard in
  let cb := ar_code_base_block ard in
  let co := ar_code_base_ofs ard in
  let gb := ar_global_block ard in
  let go := ar_global_ofs ard in
  let stk_b := ar_stack_block ard in
  let stk_base := ar_stack_base_ofs ard in

  le ! _s = Some (Vptr sb so) /\

  (exists pc_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 0) = Some pc_ptr /\
    pc_rel pc_ptr cb co s.(pc)) /\

  (exists accu_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 8) = Some accu_v /\
    val_repr hm cb co s.(accu) accu_v) /\

  (exists sp_ptr sp_b sp_ofs,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 16) = Some sp_ptr /\
    sp_ptr = Vptr sp_b sp_ofs /\
    stack_repr hm cb co m s.(stack) sp_b sp_ofs /\
    sp_b <> sb /\ sp_b <> gb /\ cb <> sp_b /\
    Ptrofs.unsigned sp_ofs >= 8 /\
    Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)) < Ptrofs.modulus /\
    Mem.range_perm m sp_b 0
      (Ptrofs.unsigned sp_ofs + 8 * Z.of_nat (length s.(stack)))
      Cur Writable /\
    (align_chunk Mint64 | Ptrofs.unsigned sp_ofs)) /\

  (exists env_v,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 24) = Some env_v /\
    val_repr hm cb co s.(Machine.env) env_v) /\

  Mem.load Mint64 m sb (Ptrofs.unsigned so + 32) =
    Some (Vlong (Int64.repr (Z.of_nat s.(extra_args)))) /\

  (exists gd_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 40) = Some gd_ptr /\
    gd_ptr = Vptr gb go /\
    global_repr hm cb co m s.(global) gb go /\
    gb <> sb) /\

  (exists ts_ptr,
    Mem.load Mint64 m sb (Ptrofs.unsigned so + 48) = Some ts_ptr /\
    trap_sp_rel ts_ptr stk_b stk_base s.(trap_sp)) /\

  Mem.range_perm m sb (Ptrofs.unsigned so) (Ptrofs.unsigned so + 56)
    Cur Writable.

(* abs_rel: the inter-instruction invariant (postcondition).
   C pc = code_base + s.(pc) * sizeof(code_t). *)
Definition abs_rel (e : Clight.env) (le : temp_env) (m : mem)
    (s : Machine.state) : Prop :=
  exists (ard : abs_rel_data), abs_rel_with_ard e le m s ard.

(* ================================================================== *)
(* Uniform completeness statement                                      *)
(* ================================================================== *)

(* handler_correct: unified correctness statement for instruction handlers.
   Takes a handler function, a Clight function, and a step precondition.
   The step precondition receives the Clight environment, memory, machine
   state, and abs_rel_data witness.  Use (fun _ _ _ _ => True) for
   handlers with no precondition.
   The Step case: abs_rel_with_ard on the pre-state AND step_pre imply
   the C body executes and abs_rel holds on the post-state.
   The Error / Halt / CCall_request cases are per-handler predicates. *)
Definition handler_correct
    (handler : Z -> state -> step_result)
    (f : function)
    (step_pre : Clight.env -> mem -> state -> abs_rel_data -> Prop)
    (P_error : string -> state -> Prop)
    (P_halt : value -> Prop)
    (P_ccall : nat -> list value -> state -> Prop) : Prop :=
  forall e le m s,
    match handler s.(pc) s with
    | Step s' =>
        forall ard,
        abs_rel_with_ard e le m s ard ->
        step_pre e m s ard ->
        exists le' m' out,
          exec_stmt function_entry1 clight_ge e le m f.(fn_body) E0 le' m' out /\
          abs_rel e le' m' s'
    | Error msg => P_error msg s
    | Halt v => P_halt v
    | CCall_request nargs args s' => P_ccall nargs args s'
    end.

(* ================================================================== *)
(* Per-instruction spec dispatch functions                              *)
(*                                                                      *)
(* Six definitions mapping each instruction to the corresponding        *)
(* argument of [handler_correct]:                                       *)
(*   instr_wfb   — bool well-formedness guard on operands               *)
(*   clight_of   — Clight function                                      *)
(*   pre_of      — step precondition (inner, without WF conjunction)    *)
(*   P_error_of  — tautological: handler s.(pc) s = Error msg           *)
(*   P_halt_of   — wfb /\ (STOP -> True | _ -> False)                   *)
(*   P_ccall_of  — wfb /\ (C_CALL -> True | _ -> False)                 *)
(*                                                                      *)
(* The bridge lemma [handler_correct_of_parameters] proves:             *)
(*   forall i, handler_correct (handle_instr i) (clight_of i)          *)
(*     (pre_of i) (P_error_of i) (P_halt_of i) (P_ccall_of i)          *)
(* ================================================================== *)

(* handler_correct_absorb_wfb removed — no longer needed after uniformizing
   InstructVerificationFineGrainedSpec parameters to use dispatch functions directly. *)

Definition instr_wfb (i : instruction) : bool :=
  match i with
  | ACC n => (Z.of_nat n <? Int.half_modulus)%Z
  | PUSH => true
  | PUSHACC n => match n with 1%nat|2%nat|3%nat|4%nat|5%nat|6%nat|7%nat => true | _ => false end
  | POP n => (Z.of_nat n <? Int.half_modulus)%Z
  | ASSIGN _ => true
  | ENVACC n => (Z.of_nat n <? Int.half_modulus)%Z
  | PUSHENVACC _ => true
  | PUSH_RETADDR _ => true
  | APPLY _ => true
  | APPLY1 => true | APPLY2 => true | APPLY3 => true
  | APPTERM _ _ => true
  | APPTERM1 _ => true | APPTERM2 _ => true | APPTERM3 _ => true
  | RETURN _ => true
  | RESTART => true
  | GRAB _ => true
  | CLOSURE nvars code_ofs =>
      ((0 <=? Z.of_nat (2 + nvars)) && (Z.of_nat (2 + nvars) <=? Int.max_signed) &&
       (Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
  | CLOSUREREC nf nv co =>
      match nf, nv, co with
      | 1%nat, 0%nat, (code_ofs :: nil)%list =>
          ((Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
      | _, _, _ => false
      end
  | OFFSETCLOSURE _ => true | PUSHOFFSETCLOSURE _ => true
  | GETGLOBAL n => ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | PUSHGETGLOBAL n => ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | GETGLOBALFIELD _ _ => true | PUSHGETGLOBALFIELD _ _ => true
  | SETGLOBAL _ => true
  | ATOM t => (Z.of_nat t <=? 2097151)%Z
  | PUSHATOM t => (Z.of_nat t <=? 2097151)%Z
  | MAKEBLOCK _ size => (1 <=? size)%nat
  | MAKEBLOCK1 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEBLOCK2 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEBLOCK3 t => ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z
  | MAKEFLOATBLOCK n => (1 <=? n)%nat
  | GETFIELD n => ((Int.min_signed <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z
  | GETFLOATFIELD _ => true
  | SETFIELD _ => true | SETFLOATFIELD _ => true
  | VECTLENGTH => true | GETVECTITEM => true | SETVECTITEM => true
  | GETBYTESCHAR => true | SETBYTESCHAR => true | GETSTRINGCHAR => true
  | BRANCH _ => true | BRANCHIF _ => true | BRANCHIFNOT _ => true
  | SWITCH _ _ _ _ => true
  | BOOLNOT => true
  | PUSHTRAP _ => true | POPTRAP => true
  | RAISE => true | RERAISE => true | RAISE_NOTRACE => true
  | CHECK_SIGNALS => true
  | C_CALL _ _ => true
  | CONSTINT n => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | PUSHCONSTINT _ => true
  | NEGINT => true | ADDINT => true | SUBINT => true
  | MULINT => true | DIVINT => true | MODINT => true
  | ANDINT => true | ORINT => true | XORINT => true
  | LSLINT => true | LSRINT => true | ASRINT => true
  | EQ => true | NEQ => true
  | LTINT => true | LEINT => true | GTINT => true | GEINT => true
  | OFFSETINT ofs => ((Int.min_signed <=? ofs * 2) && (ofs * 2 <=? Int.max_signed))%Z
  | OFFSETREF _ => true
  | ISINT => true
  | GETMETHOD => true | GETPUBMET _ => true | GETDYNMET => true
  | BEQ n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BNEQ n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BLTINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BLEINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BGTINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BGEINT n _ => ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | ULTINT => true | UGEINT => true
  | BULTINT n _ => ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | BUGEINT n _ => ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z
  | STOP => true
  end.

Definition clight_of (i : instruction) : function :=
  match i with
  | ACC _ => f_instr_ACC
  | PUSH => f_instr_PUSH
  | PUSHACC n =>
      match n with
      | 1%nat => f_instr_PUSHACC1 | 2%nat => f_instr_PUSHACC2
      | 3%nat => f_instr_PUSHACC3 | 4%nat => f_instr_PUSHACC4
      | 5%nat => f_instr_PUSHACC5 | 6%nat => f_instr_PUSHACC6
      | 7%nat => f_instr_PUSHACC7 | _ => f_instr_PUSHACC1
      end
  | POP _ => f_instr_POP
  | ASSIGN _ => f_instr_ASSIGN
  | ENVACC _ => f_instr_ENVACC
  | PUSHENVACC _ => f_instr_PUSHENVACC
  | PUSH_RETADDR _ => f_instr_PUSH_RETADDR
  | APPLY _ => f_instr_APPLY
  | APPLY1 => f_instr_APPLY1
  | APPLY2 => f_instr_APPLY2
  | APPLY3 => f_instr_APPLY3
  | APPTERM _ _ => f_instr_APPTERM
  | APPTERM1 _ => f_instr_APPTERM1
  | APPTERM2 _ => f_instr_APPTERM2
  | APPTERM3 _ => f_instr_APPTERM3
  | RETURN _ => f_instr_RETURN
  | RESTART => f_instr_RESTART
  | GRAB _ => f_instr_GRAB
  | CLOSURE _ _ => f_instr_CLOSURE
  | CLOSUREREC _ _ _ => f_instr_CLOSUREREC
  | OFFSETCLOSURE _ => f_instr_OFFSETCLOSURE
  | PUSHOFFSETCLOSURE _ => f_instr_PUSHOFFSETCLOSURE
  | GETGLOBAL _ => f_instr_GETGLOBAL
  | PUSHGETGLOBAL _ => f_instr_PUSHGETGLOBAL
  | GETGLOBALFIELD _ _ => f_instr_GETGLOBALFIELD
  | PUSHGETGLOBALFIELD _ _ => f_instr_PUSHGETGLOBALFIELD
  | SETGLOBAL _ => f_instr_SETGLOBAL
  | ATOM _ => f_instr_ATOM
  | PUSHATOM _ => f_instr_PUSHATOM
  | MAKEBLOCK _ _ => f_instr_MAKEBLOCK
  | MAKEBLOCK1 _ => f_instr_MAKEBLOCK1
  | MAKEBLOCK2 _ => f_instr_MAKEBLOCK2
  | MAKEBLOCK3 _ => f_instr_MAKEBLOCK3
  | MAKEFLOATBLOCK _ => f_instr_MAKEFLOATBLOCK
  | GETFIELD _ => f_instr_GETFIELD
  | GETFLOATFIELD _ => f_instr_GETFLOATFIELD
  | SETFIELD _ => f_instr_SETFIELD
  | SETFLOATFIELD _ => f_instr_SETFLOATFIELD
  | VECTLENGTH => f_instr_VECTLENGTH
  | GETVECTITEM => f_instr_GETVECTITEM
  | SETVECTITEM => f_instr_SETVECTITEM
  | GETBYTESCHAR => f_instr_GETBYTESCHAR
  | SETBYTESCHAR => f_instr_SETBYTESCHAR
  | GETSTRINGCHAR => f_instr_GETSTRINGCHAR
  | BRANCH _ => f_instr_BRANCH
  | BRANCHIF _ => f_instr_BRANCHIF
  | BRANCHIFNOT _ => f_instr_BRANCHIFNOT
  | SWITCH _ _ _ _ => f_instr_SWITCH
  | BOOLNOT => f_instr_BOOLNOT
  | PUSHTRAP _ => f_instr_PUSHTRAP
  | POPTRAP => f_instr_POPTRAP
  | RAISE => f_instr_RAISE
  | RERAISE => f_instr_RERAISE
  | RAISE_NOTRACE => f_instr_RAISE_NOTRACE
  | CHECK_SIGNALS => f_instr_CHECK_SIGNALS
  | C_CALL _ _ => f_instr_C_CALLN
  | CONSTINT _ => f_instr_CONSTINT
  | PUSHCONSTINT _ => f_instr_PUSHCONSTINT
  | NEGINT => f_instr_NEGINT
  | ADDINT => f_instr_ADDINT
  | SUBINT => f_instr_SUBINT
  | MULINT => f_instr_MULINT
  | DIVINT => f_instr_DIVINT
  | MODINT => f_instr_MODINT
  | ANDINT => f_instr_ANDINT
  | ORINT => f_instr_ORINT
  | XORINT => f_instr_XORINT
  | LSLINT => f_instr_LSLINT
  | LSRINT => f_instr_LSRINT
  | ASRINT => f_instr_ASRINT
  | EQ => f_instr_EQ
  | NEQ => f_instr_NEQ
  | LTINT => f_instr_LTINT
  | LEINT => f_instr_LEINT
  | GTINT => f_instr_GTINT
  | GEINT => f_instr_GEINT
  | OFFSETINT _ => f_instr_OFFSETINT
  | OFFSETREF _ => f_instr_OFFSETREF
  | ISINT => f_instr_ISINT
  | GETMETHOD => f_instr_GETMETHOD
  | GETPUBMET _ => f_instr_GETPUBMET
  | GETDYNMET => f_instr_GETDYNMET
  | BEQ _ _ => f_instr_BEQ
  | BNEQ _ _ => f_instr_BNEQ
  | BLTINT _ _ => f_instr_BLTINT
  | BLEINT _ _ => f_instr_BLEINT
  | BGTINT _ _ => f_instr_BGTINT
  | BGEINT _ _ => f_instr_BGEINT
  | ULTINT => f_instr_ULTINT
  | UGEINT => f_instr_UGEINT
  | BULTINT _ _ => f_instr_BULTINT
  | BUGEINT _ _ => f_instr_BUGEINT
  | STOP => f_instr_STOP
  end.

(* Helper: compute the error message that do_raise would produce, without
   calling do_raise itself.  Returns [Some msg] when a raise would error
   (no trap frame or malformed trap frame) and [None] when it would succeed. *)
Definition error_message_of_raise (s : state) : option string :=
  if Nat.eqb s.(trap_sp) 0 then Some "unhandled exception"
  else
    let k := Nat.sub (length s.(stack)) s.(trap_sp) in
    let frame_top := skipn k s.(stack) in
    match frame_top with
    | Val_int _ :: Val_int _ :: _ :: Val_int _ :: _ => None
    | _ => Some "RAISE: malformed trap frame"
    end.

(* Helper: scan method table for GETPUBMET/GETDYNMET *)
Fixpoint scan_method_table (tag : value) (remaining : list value)
    (not_found_msg : string) : option string :=
  match remaining with
  | [] => Some not_found_msg
  | _ :: [] => Some not_found_msg
  | _ :: tag_val :: rest =>
    if value_eqb tag_val tag then None
    else scan_method_table tag rest not_found_msg
  end.

(* Computable error message for a given instruction and state.
   Returns [Some msg] when the instruction errors with [msg],
   and [None] when it does not error. *)
Definition error_message_of (i : instruction) (s : state) : option string :=
  match i with
  (* ACC: malformed operand or stack underflow *)
  | ACC n =>
    if (Z.of_nat n <? Int.half_modulus)%Z then
      match nth_error s.(stack) n with
      | Some _ => None
      | None => Some "ACC: stack underflow"
      end
    else Some "ACC: malformed operand"
  (* PUSH: never errors *)
  | PUSH => None
  (* PUSHACC: malformed operand or stack underflow *)
  | PUSHACC n =>
    match n with
    | 1%nat|2%nat|3%nat|4%nat|5%nat|6%nat|7%nat =>
      match nth_error (s.(accu) :: s.(stack)) n with
      | Some _ => None
      | None => Some "PUSHACC: stack underflow"
      end
    | _ => Some "PUSHACC: malformed operand"
    end
  (* POP: malformed operand *)
  | POP n =>
    if (Z.of_nat n <? Int.half_modulus)%Z then None
    else Some "POP: malformed operand"
  (* ASSIGN: stack underflow *)
  | ASSIGN n =>
    match set_nth s.(stack) n s.(accu) with
    | Some _ => None
    | None => Some "ASSIGN: stack underflow"
    end
  (* ENVACC: malformed operand or env access out of bounds *)
  | ENVACC n =>
    if (Z.of_nat n <? Int.half_modulus)%Z then
      match field_or_heap s s.(env) n with
      | Some _ => None
      | None => Some "ENVACC: env access out of bounds"
      end
    else Some "ENVACC: malformed operand"
  (* PUSHENVACC: env access out of bounds *)
  | PUSHENVACC n =>
    match field_or_heap s s.(env) n with
    | Some _ => None
    | None => Some "PUSHENVACC: env access out of bounds"
    end
  (* PUSH_RETADDR: never errors *)
  | PUSH_RETADDR _ => None
  (* APPLY: accu is not a closure *)
  | APPLY n =>
    match get_code_ptr_s s s.(accu) with
    | Some _ => None
    | None => Some "APPLY: accu is not a closure"
    end
  (* APPLY1: stack underflow or accu not a closure *)
  | APPLY1 =>
    match s.(stack) with
    | _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPLY1: accu is not a closure"
      end
    | _ => Some "APPLY1: stack underflow"
    end
  (* APPLY2: stack underflow or accu not a closure *)
  | APPLY2 =>
    match s.(stack) with
    | _ :: _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPLY2: accu is not a closure"
      end
    | _ => Some "APPLY2: stack underflow"
    end
  (* APPLY3: stack underflow or accu not a closure *)
  | APPLY3 =>
    match s.(stack) with
    | _ :: _ :: _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPLY3: accu is not a closure"
      end
    | _ => Some "APPLY3: stack underflow"
    end
  (* APPTERM: accu not a closure *)
  | APPTERM _ _ =>
    match get_code_ptr_s s s.(accu) with
    | Some _ => None
    | None => Some "APPTERM: accu is not a closure"
    end
  (* APPTERM1: stack underflow or accu not a closure *)
  | APPTERM1 slotsize =>
    match s.(stack) with
    | _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPTERM1: accu is not a closure"
      end
    | _ => Some "APPTERM1: stack underflow"
    end
  (* APPTERM2: stack underflow or accu not a closure *)
  | APPTERM2 slotsize =>
    match s.(stack) with
    | _ :: _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPTERM2: accu is not a closure"
      end
    | _ => Some "APPTERM2: stack underflow"
    end
  (* APPTERM3: stack underflow or accu not a closure *)
  | APPTERM3 slotsize =>
    match s.(stack) with
    | _ :: _ :: _ :: _ =>
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "APPTERM3: accu is not a closure"
      end
    | _ => Some "APPTERM3: stack underflow"
    end
  (* RETURN: various error conditions *)
  | RETURN stacksize =>
    let stk := skipn stacksize s.(stack) in
    if Nat.ltb 0 s.(extra_args) then
      match get_code_ptr_s s s.(accu) with
      | Some _ => None
      | None => Some "RETURN: accu is not a closure"
      end
    else
      match stk with
      | Val_int _ :: _ :: Val_int _ :: _ => None
      | _ => Some "RETURN: malformed return frame"
      end
  (* RESTART: various error conditions *)
  | RESTART =>
    match s.(env) with
    | Val_closure addr ofs =>
      match heap_lookup s.(hp) addr with
      | Some (t, all_fields) =>
        if Nat.eqb t Closure_tag then
          let fields := skipn ofs all_fields in
          match nth_error fields 2 with
          | Some _ => None
          | None => Some "RESTART: malformed closure"
          end
        else Some "RESTART: env is not a closure"
      | None => Some "RESTART: dangling pointer"
      end
    | Val_block t fields =>
      if Nat.eqb t Closure_tag then
        match nth_error fields 2 with
        | Some _ => None
        | None => Some "RESTART: malformed closure"
        end
      else Some "RESTART: env is not a closure"
    | _ => Some "RESTART: env is not a block"
    end
  (* GRAB: malformed return frame *)
  | GRAB required =>
    if Nat.leb required s.(extra_args) then None
    else
      let num_args := S s.(extra_args) in
      let rest_stack := skipn num_args s.(stack) in
      match rest_stack with
      | Val_int _ :: _ :: Val_int _ :: _ => None
      | _ => Some "GRAB: malformed return frame"
      end
  (* CLOSURE: malformed operand *)
  | CLOSURE nvars code_ofs =>
    if ((0 <=? Z.of_nat (2 + nvars)) && (Z.of_nat (2 + nvars) <=? Int.max_signed) &&
        (Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z then None
    else Some "CLOSURE: malformed operand"
  (* CLOSUREREC: malformed operand or no code offsets *)
  | CLOSUREREC nf nv code_offsets =>
    let wf :=
      match nf, nv, code_offsets with
      | 1%nat, 0%nat, (code_ofs :: nil)%list =>
          ((Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
      | _, _, _ => false
      end in
    if wf then
      match code_offsets with
      | [] => Some "CLOSUREREC: no code offsets"
      | _ => None
      end
    else Some "CLOSUREREC: malformed operand"
  (* OFFSETCLOSURE: errors when env is invalid *)
  | OFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure _ _ => None
    | Val_block _ _ =>
      if Z.eqb ofs 0 then None
      else Some "OFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Some "OFFSETCLOSURE: invalid env"
    end
  (* PUSHOFFSETCLOSURE: errors when env is invalid *)
  | PUSHOFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure _ _ => None
    | Val_block _ _ =>
      if Z.eqb ofs 0 then None
      else Some "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Some "PUSHOFFSETCLOSURE: invalid env"
    end
  (* GETGLOBAL: malformed operand or index out of bounds *)
  | GETGLOBAL n =>
    if ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
      match nth_error s.(global) n with
      | Some _ => None
      | None => Some "GETGLOBAL: index out of bounds"
      end
    else Some "GETGLOBAL: malformed operand"
  (* PUSHGETGLOBAL: malformed operand or index out of bounds *)
  | PUSHGETGLOBAL n =>
    if ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
      match nth_error s.(global) n with
      | Some _ => None
      | None => Some "PUSHGETGLOBAL: index out of bounds"
      end
    else Some "PUSHGETGLOBAL: malformed operand"
  (* GETGLOBALFIELD: index out of bounds or field access failed *)
  | GETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some _ => None
      | None => Some "GETGLOBALFIELD: field access failed"
      end
    | None => Some "GETGLOBALFIELD: index out of bounds"
    end
  (* PUSHGETGLOBALFIELD: index out of bounds or field access failed *)
  | PUSHGETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some _ => None
      | None => Some "PUSHGETGLOBALFIELD: field access failed"
      end
    | None => Some "PUSHGETGLOBALFIELD: index out of bounds"
    end
  (* SETGLOBAL: never errors *)
  | SETGLOBAL _ => None
  (* ATOM: malformed operand *)
  | ATOM t =>
    if (Z.of_nat t <=? 2097151)%Z then None
    else Some "ATOM: malformed operand"
  (* PUSHATOM: malformed operand *)
  | PUSHATOM t =>
    if (Z.of_nat t <=? 2097151)%Z then None
    else Some "PUSHATOM: malformed operand"
  (* MAKEBLOCK: malformed operand *)
  | MAKEBLOCK _ size =>
    if (1 <=? size)%nat then None
    else Some "MAKEBLOCK: malformed operand"
  (* MAKEBLOCK1: malformed operand *)
  | MAKEBLOCK1 t =>
    if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then None
    else Some "MAKEBLOCK1: malformed operand"
  (* MAKEBLOCK2: malformed operand or stack underflow *)
  | MAKEBLOCK2 t =>
    if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then
      match s.(stack) with
      | _ :: _ => None
      | _ => Some "MAKEBLOCK2: stack underflow"
      end
    else Some "MAKEBLOCK2: malformed operand"
  (* MAKEBLOCK3: malformed operand or stack underflow *)
  | MAKEBLOCK3 t =>
    if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then
      match s.(stack) with
      | _ :: _ :: _ => None
      | _ => Some "MAKEBLOCK3: stack underflow"
      end
    else Some "MAKEBLOCK3: malformed operand"
  (* MAKEFLOATBLOCK: malformed operand *)
  | MAKEFLOATBLOCK n =>
    if (1 <=? n)%nat then None
    else Some "MAKEFLOATBLOCK: malformed operand"
  (* GETFIELD: malformed operand or access failed *)
  | GETFIELD n =>
    if ((Int.min_signed <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
      match field_or_heap s s.(accu) n with
      | Some _ => None
      | None => Some "GETFIELD: access failed"
      end
    else Some "GETFIELD: malformed operand"
  (* GETFLOATFIELD: access failed *)
  | GETFLOATFIELD n =>
    match field_or_heap s s.(accu) n with
    | Some _ => None
    | None => Some "GETFLOATFIELD: access failed"
    end
  (* SETFIELD: various error cases *)
  | SETFIELD n =>
    match s.(stack) with
    | newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields n newval with
          | Some _ => None
          | None => Some "SETFIELD: index out of bounds"
          end
        | None => Some "SETFIELD: dangling pointer"
        end
      | _ => Some "SETFIELD: not a mutable block"
      end
    | _ => Some "SETFIELD: stack underflow"
    end
  (* SETFLOATFIELD: various error cases *)
  | SETFLOATFIELD n =>
    match s.(stack) with
    | newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields n newval with
          | Some _ => None
          | None => Some "SETFLOATFIELD: index out of bounds"
          end
        | None => Some "SETFLOATFIELD: dangling pointer"
        end
      | _ => Some "SETFLOATFIELD: not a heap float array"
      end
    | _ => Some "SETFLOATFIELD: stack underflow"
    end
  (* VECTLENGTH: not a block *)
  | VECTLENGTH =>
    match size_or_heap s s.(accu) with
    | Some _ => None
    | None => Some "VECTLENGTH: not a block"
    end
  (* GETVECTITEM: index out of bounds or stack underflow *)
  | GETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: _ =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some _ => None
      | None => Some "GETVECTITEM: index out of bounds"
      end
    | _ => Some "GETVECTITEM: bad index or stack underflow"
    end
  (* SETVECTITEM: various error cases *)
  | SETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: newval :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields (Z.to_nat idx) newval with
          | Some _ => None
          | None => Some "SETVECTITEM: index out of bounds"
          end
        | None => Some "SETVECTITEM: dangling pointer"
        end
      | _ => Some "SETVECTITEM: not a heap block"
      end
    | _ => Some "SETVECTITEM: stack underflow"
    end
  (* GETBYTESCHAR/GETSTRINGCHAR: index/stack issues *)
  | GETBYTESCHAR | GETSTRINGCHAR =>
    match s.(stack) with
    | Val_int idx :: _ =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some (Val_int _) => None
      | _ => Some "GETSTRINGCHAR: index out of bounds or not a char"
      end
    | _ => Some "GETSTRINGCHAR: stack underflow"
    end
  (* SETBYTESCHAR: various error cases *)
  | SETBYTESCHAR =>
    match s.(stack) with
    | Val_int idx :: Val_int newchar :: _ =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields (Z.to_nat idx) (Val_int newchar) with
          | Some _ => None
          | None => Some "SETBYTESCHAR: index out of bounds"
          end
        | None => Some "SETBYTESCHAR: dangling pointer"
        end
      | _ => Some "SETBYTESCHAR: not a heap bytes"
      end
    | _ => Some "SETBYTESCHAR: stack underflow"
    end
  (* BRANCH: never errors *)
  | BRANCH _ => None
  (* BRANCHIF: never errors *)
  | BRANCHIF _ => None
  (* BRANCHIFNOT: never errors *)
  | BRANCHIFNOT _ => None
  (* SWITCH: various error cases *)
  | SWITCH _nc _nb const_targets block_targets =>
    match s.(accu) with
    | Val_int n =>
      match nth_error const_targets (Z.to_nat n) with
      | Some _ => None
      | None => Some "SWITCH: constant index out of range"
      end
    | Val_block t _ =>
      match nth_error block_targets t with
      | Some _ => None
      | None => Some "SWITCH: block tag out of range"
      end
    | Val_ptr _ | Val_closure _ _ =>
      match tag_or_heap s s.(accu) with
      | Some t =>
        match nth_error block_targets t with
        | Some _ => None
        | None => Some "SWITCH: block tag out of range"
        end
      | None => Some "SWITCH: dangling pointer"
      end
    end
  (* BOOLNOT: never errors *)
  | BOOLNOT => None
  (* PUSHTRAP: never errors *)
  | PUSHTRAP _ => None
  (* POPTRAP: malformed trap frame *)
  | POPTRAP =>
    match s.(stack) with
    | _ :: Val_int _ :: _ :: _ :: _ => None
    | _ => Some "POPTRAP: malformed trap frame"
    end
  (* RAISE/RERAISE/RAISE_NOTRACE: error when no trap frame or malformed *)
  | RAISE | RERAISE | RAISE_NOTRACE =>
    error_message_of_raise s
  (* CHECK_SIGNALS: never errors *)
  | CHECK_SIGNALS => None
  (* C_CALL: never errors (returns CCall_request) *)
  | C_CALL _ _ => None
  (* CONSTINT: malformed operand *)
  | CONSTINT n =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then None
    else Some "CONSTINT: malformed operand"
  (* PUSHCONSTINT: never errors *)
  | PUSHCONSTINT _ => None
  (* NEGINT: not an integer *)
  | NEGINT =>
    match s.(accu) with
    | Val_int _ => None
    | _ => Some "NEGINT: not an integer"
    end
  (* ADDINT: type error or stack underflow *)
  | ADDINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "ADDINT: type error or stack underflow"
    end
  (* SUBINT: type error or stack underflow *)
  | SUBINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "SUBINT: type error or stack underflow"
    end
  (* MULINT: type error or stack underflow *)
  | MULINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "MULINT: type error or stack underflow"
    end
  (* DIVINT: type error, stack underflow, or division-by-zero raise *)
  | DIVINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int b :: _ =>
      if Z.eqb b 0 then error_message_of_raise s
      else None
    | _, _ => Some "DIVINT: type error or stack underflow"
    end
  (* MODINT: type error, stack underflow, or division-by-zero raise *)
  | MODINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int b :: _ =>
      if Z.eqb b 0 then error_message_of_raise s
      else None
    | _, _ => Some "MODINT: type error or stack underflow"
    end
  (* ANDINT: type error or stack underflow *)
  | ANDINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "ANDINT: type error or stack underflow"
    end
  (* ORINT: type error or stack underflow *)
  | ORINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "ORINT: type error or stack underflow"
    end
  (* XORINT: type error or stack underflow *)
  | XORINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "XORINT: type error or stack underflow"
    end
  (* LSLINT: type error or stack underflow *)
  | LSLINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "LSLINT: type error or stack underflow"
    end
  (* LSRINT: type error or stack underflow *)
  | LSRINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "LSRINT: type error or stack underflow"
    end
  (* ASRINT: type error or stack underflow *)
  | ASRINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "ASRINT: type error or stack underflow"
    end
  (* EQ: stack underflow *)
  | EQ =>
    match s.(stack) with
    | _ :: _ => None
    | _ => Some "EQ: stack underflow"
    end
  (* NEQ: stack underflow *)
  | NEQ =>
    match s.(stack) with
    | _ :: _ => None
    | _ => Some "NEQ: stack underflow"
    end
  (* LTINT: type error or stack underflow *)
  | LTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "LTINT: type error or stack underflow"
    end
  (* LEINT: type error or stack underflow *)
  | LEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "LEINT: type error or stack underflow"
    end
  (* GTINT: type error or stack underflow *)
  | GTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "GTINT: type error or stack underflow"
    end
  (* GEINT: type error or stack underflow *)
  | GEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "GEINT: type error or stack underflow"
    end
  (* OFFSETINT: malformed operand or not an integer *)
  | OFFSETINT ofs =>
    if ((Int.min_signed <=? ofs * 2) && (ofs * 2 <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "OFFSETINT: not an integer"
      end
    else Some "OFFSETINT: malformed operand"
  (* OFFSETREF: not a ref *)
  | OFFSETREF _ =>
    match s.(accu) with
    | Val_ptr addr =>
      match heap_lookup s.(hp) addr with
      | Some (_, Val_int _ :: _) => None
      | _ => Some "OFFSETREF: not a ref"
      end
    | _ => Some "OFFSETREF: not a ref"
    end
  (* ISINT: never errors *)
  | ISINT => None
  (* GETMETHOD: various error cases *)
  | GETMETHOD =>
    match s.(stack) with
    | obj :: _ =>
      match field_or_heap s obj 0 with
      | Some class_tbl =>
        match s.(accu) with
        | Val_int n =>
          match field_or_heap s class_tbl (Z.to_nat n) with
          | Some _ => None
          | None => Some "GETMETHOD: method not found"
          end
        | _ => Some "GETMETHOD: not an integer index"
        end
      | None => Some "GETMETHOD: no class table"
      end
    | _ => Some "GETMETHOD: stack underflow"
    end
  (* GETPUBMET: errors when method not found or no class table *)
  | GETPUBMET tag =>
    match field_or_heap s s.(accu) 0 with
    | Some class_tbl =>
      let fields :=
        match class_tbl with
        | Val_block _ fs => fs
        | Val_ptr addr => match heap_lookup s.(hp) addr with Some (_, fs) => fs | None => [] end
        | _ => []
        end
      in
      scan_method_table (Val_int tag) (skipn 2 fields) "GETPUBMET: method not found"
    | None => Some "GETPUBMET: no class table"
    end
  (* GETDYNMET: errors when method not found, no class table, or stack underflow *)
  | GETDYNMET =>
    match s.(stack) with
    | obj :: _ =>
      let tag := s.(accu) in
      match field_or_heap s obj 0 with
      | Some class_tbl =>
        let fields :=
          match class_tbl with
          | Val_block _ fs => fs
          | Val_ptr addr => match heap_lookup s.(hp) addr with Some (_, fs) => fs | None => [] end
          | _ => []
          end
        in
        scan_method_table tag (skipn 2 fields) "GETDYNMET: method not found"
      | None => Some "GETDYNMET: no class table"
      end
    | _ => Some "GETDYNMET: stack underflow"
    end
  (* BEQ: malformed operand *)
  | BEQ n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then None
    else Some "BEQ: malformed operand"
  (* BNEQ: malformed operand *)
  | BNEQ n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then None
    else Some "BNEQ: malformed operand"
  (* BLTINT: malformed operand or not an integer *)
  | BLTINT n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BLTINT: not an integer"
      end
    else Some "BLTINT: malformed operand"
  (* BLEINT: malformed operand or not an integer *)
  | BLEINT n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BLEINT: not an integer"
      end
    else Some "BLEINT: malformed operand"
  (* BGTINT: malformed operand or not an integer *)
  | BGTINT n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BGTINT: not an integer"
      end
    else Some "BGTINT: malformed operand"
  (* BGEINT: malformed operand or not an integer *)
  | BGEINT n _ =>
    if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BGEINT: not an integer"
      end
    else Some "BGEINT: malformed operand"
  (* ULTINT: type error or stack underflow *)
  | ULTINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "ULTINT: type error or stack underflow"
    end
  (* UGEINT: type error or stack underflow *)
  | UGEINT =>
    match s.(accu), s.(stack) with
    | Val_int _, Val_int _ :: _ => None
    | _, _ => Some "UGEINT: type error or stack underflow"
    end
  (* BULTINT: malformed operand or not an integer *)
  | BULTINT n _ =>
    if ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BULTINT: not an integer"
      end
    else Some "BULTINT: malformed operand"
  (* BUGEINT: malformed operand or not an integer *)
  | BUGEINT n _ =>
    if ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
      match s.(accu) with
      | Val_int _ => None
      | _ => Some "BUGEINT: not an integer"
      end
    else Some "BUGEINT: malformed operand"
  (* STOP: never errors (returns Halt) *)
  | STOP => None
  end.

(* Weakest-precondition style: the precondition for instruction i says
   "under abs_rel, the Clight body of clight_of(i) can execute to some
   post-state satisfying abs_rel."  This is uniform across all instructions,
   keeping the trusted computing base minimal. *)
Definition pre_of (i : instruction) : Clight.env -> mem -> state -> abs_rel_data -> Prop :=
  fun e m s ard =>
    forall le, abs_rel_with_ard e le m s ard ->
    exists le' m' out s'',
      exec_stmt function_entry1 clight_ge e le m (fn_body (clight_of i)) E0 le' m' out /\
      abs_rel e le' m' s''.

Definition P_error_of (i : instruction) (msg : string) (s : state) : Prop :=
  error_message_of i s = Some msg.

Definition P_halt_of (i : instruction) (v : value) : Prop :=
  instr_wfb i = true /\ match i with STOP => True | _ => False end.

Definition P_ccall_of (i : instruction) (n : nat) (args : list value) (s : state) : Prop :=
  instr_wfb i = true /\ match i with C_CALL _ _ => True | _ => False end.

(* ================================================================== *)
(* Module Type                                                         *)
(*                                                                      *)
(* pre_of is a uniform weakest-precondition: the Clight body can       *)
(* execute under abs_rel.  P_error_of, P_halt_of, P_ccall_of are      *)
(* per-instruction dispatch functions constraining error/halt/ccall    *)
(* outcomes.                                                            *)
(*                                                                      *)
(* Each entry: handler_correct handler c_func pre err halt ccall       *)
(* 94 uniform parameters (one per AST constructor).                     *)
(* ================================================================== *)

Module Type InstructVerificationFineGrainedSpec (Import HI : HandleInstrSpec).

  Parameter correct_ACC : forall n,
    handler_correct (handle_instr (ACC n)) (clight_of (ACC n))
      (pre_of (ACC n))
      (P_error_of (ACC n)) (P_halt_of (ACC n)) (P_ccall_of (ACC n)).

  Parameter correct_PUSH :
    handler_correct (handle_instr PUSH) (clight_of PUSH)
      (pre_of PUSH)
      (P_error_of PUSH) (P_halt_of PUSH) (P_ccall_of PUSH).

  Parameter correct_PUSHACC : forall n,
    handler_correct (handle_instr (PUSHACC n)) (clight_of (PUSHACC n))
      (pre_of (PUSHACC n))
      (P_error_of (PUSHACC n)) (P_halt_of (PUSHACC n)) (P_ccall_of (PUSHACC n)).

  Parameter correct_POP : forall n,
    handler_correct (handle_instr (POP n)) (clight_of (POP n))
      (pre_of (POP n))
      (P_error_of (POP n)) (P_halt_of (POP n)) (P_ccall_of (POP n)).

  Parameter correct_ASSIGN : forall n,
    handler_correct (handle_instr (ASSIGN n)) (clight_of (ASSIGN n))
      (pre_of (ASSIGN n))
      (P_error_of (ASSIGN n)) (P_halt_of (ASSIGN n)) (P_ccall_of (ASSIGN n)).

  Parameter correct_ENVACC : forall n,
    handler_correct (handle_instr (ENVACC n)) (clight_of (ENVACC n))
      (pre_of (ENVACC n))
      (P_error_of (ENVACC n)) (P_halt_of (ENVACC n)) (P_ccall_of (ENVACC n)).

  Parameter correct_PUSHENVACC : forall n,
    handler_correct (handle_instr (PUSHENVACC n)) (clight_of (PUSHENVACC n))
      (pre_of (PUSHENVACC n))
      (P_error_of (PUSHENVACC n)) (P_halt_of (PUSHENVACC n)) (P_ccall_of (PUSHENVACC n)).

  Parameter correct_PUSH_RETADDR : forall z,
    handler_correct (handle_instr (PUSH_RETADDR z)) (clight_of (PUSH_RETADDR z))
      (pre_of (PUSH_RETADDR z))
      (P_error_of (PUSH_RETADDR z)) (P_halt_of (PUSH_RETADDR z)) (P_ccall_of (PUSH_RETADDR z)).

  Parameter correct_APPLY : forall n,
    handler_correct (handle_instr (APPLY n)) (clight_of (APPLY n))
      (pre_of (APPLY n))
      (P_error_of (APPLY n)) (P_halt_of (APPLY n)) (P_ccall_of (APPLY n)).

  Parameter correct_APPLY1 :
    handler_correct (handle_instr APPLY1) (clight_of APPLY1)
      (pre_of APPLY1)
      (P_error_of APPLY1) (P_halt_of APPLY1) (P_ccall_of APPLY1).

  Parameter correct_APPLY2 :
    handler_correct (handle_instr APPLY2) (clight_of APPLY2)
      (pre_of APPLY2)
      (P_error_of APPLY2) (P_halt_of APPLY2) (P_ccall_of APPLY2).

  Parameter correct_APPLY3 :
    handler_correct (handle_instr APPLY3) (clight_of APPLY3)
      (pre_of APPLY3)
      (P_error_of APPLY3) (P_halt_of APPLY3) (P_ccall_of APPLY3).

  Parameter correct_APPTERM : forall nargs slotsize,
    handler_correct (handle_instr (APPTERM nargs slotsize)) (clight_of (APPTERM nargs slotsize))
      (pre_of (APPTERM nargs slotsize))
      (P_error_of (APPTERM nargs slotsize)) (P_halt_of (APPTERM nargs slotsize)) (P_ccall_of (APPTERM nargs slotsize)).

  Parameter correct_APPTERM1 : forall n,
    handler_correct (handle_instr (APPTERM1 n)) (clight_of (APPTERM1 n))
      (pre_of (APPTERM1 n))
      (P_error_of (APPTERM1 n)) (P_halt_of (APPTERM1 n)) (P_ccall_of (APPTERM1 n)).

  Parameter correct_APPTERM2 : forall n,
    handler_correct (handle_instr (APPTERM2 n)) (clight_of (APPTERM2 n))
      (pre_of (APPTERM2 n))
      (P_error_of (APPTERM2 n)) (P_halt_of (APPTERM2 n)) (P_ccall_of (APPTERM2 n)).

  Parameter correct_APPTERM3 : forall n,
    handler_correct (handle_instr (APPTERM3 n)) (clight_of (APPTERM3 n))
      (pre_of (APPTERM3 n))
      (P_error_of (APPTERM3 n)) (P_halt_of (APPTERM3 n)) (P_ccall_of (APPTERM3 n)).

  Parameter correct_RETURN : forall n,
    handler_correct (handle_instr (RETURN n)) (clight_of (RETURN n))
      (pre_of (RETURN n))
      (P_error_of (RETURN n)) (P_halt_of (RETURN n)) (P_ccall_of (RETURN n)).

  Parameter correct_RESTART :
    handler_correct (handle_instr RESTART) (clight_of RESTART)
      (pre_of RESTART)
      (P_error_of RESTART) (P_halt_of RESTART) (P_ccall_of RESTART).

  Parameter correct_GRAB : forall n,
    handler_correct (handle_instr (GRAB n)) (clight_of (GRAB n))
      (pre_of (GRAB n))
      (P_error_of (GRAB n)) (P_halt_of (GRAB n)) (P_ccall_of (GRAB n)).

  Parameter correct_CLOSURE : forall n z,
    handler_correct (handle_instr (CLOSURE n z)) (clight_of (CLOSURE n z))
      (pre_of (CLOSURE n z))
      (P_error_of (CLOSURE n z)) (P_halt_of (CLOSURE n z)) (P_ccall_of (CLOSURE n z)).

  Parameter correct_CLOSUREREC : forall n1 n2 l,
    handler_correct (handle_instr (CLOSUREREC n1 n2 l)) (clight_of (CLOSUREREC n1 n2 l))
      (pre_of (CLOSUREREC n1 n2 l))
      (P_error_of (CLOSUREREC n1 n2 l)) (P_halt_of (CLOSUREREC n1 n2 l)) (P_ccall_of (CLOSUREREC n1 n2 l)).

  Parameter correct_OFFSETCLOSURE : forall z,
    handler_correct (handle_instr (OFFSETCLOSURE z)) (clight_of (OFFSETCLOSURE z))
      (pre_of (OFFSETCLOSURE z))
      (P_error_of (OFFSETCLOSURE z)) (P_halt_of (OFFSETCLOSURE z)) (P_ccall_of (OFFSETCLOSURE z)).

  Parameter correct_PUSHOFFSETCLOSURE : forall z,
    handler_correct (handle_instr (PUSHOFFSETCLOSURE z)) (clight_of (PUSHOFFSETCLOSURE z))
      (pre_of (PUSHOFFSETCLOSURE z))
      (P_error_of (PUSHOFFSETCLOSURE z)) (P_halt_of (PUSHOFFSETCLOSURE z)) (P_ccall_of (PUSHOFFSETCLOSURE z)).

  Parameter correct_GETGLOBAL : forall n,
    handler_correct (handle_instr (GETGLOBAL n)) (clight_of (GETGLOBAL n))
      (pre_of (GETGLOBAL n))
      (P_error_of (GETGLOBAL n)) (P_halt_of (GETGLOBAL n)) (P_ccall_of (GETGLOBAL n)).

  Parameter correct_PUSHGETGLOBAL : forall n,
    handler_correct (handle_instr (PUSHGETGLOBAL n)) (clight_of (PUSHGETGLOBAL n))
      (pre_of (PUSHGETGLOBAL n))
      (P_error_of (PUSHGETGLOBAL n)) (P_halt_of (PUSHGETGLOBAL n)) (P_ccall_of (PUSHGETGLOBAL n)).

  Parameter correct_GETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (GETGLOBALFIELD n1 n2)) (clight_of (GETGLOBALFIELD n1 n2))
      (pre_of (GETGLOBALFIELD n1 n2))
      (P_error_of (GETGLOBALFIELD n1 n2)) (P_halt_of (GETGLOBALFIELD n1 n2)) (P_ccall_of (GETGLOBALFIELD n1 n2)).

  Parameter correct_PUSHGETGLOBALFIELD : forall n1 n2,
    handler_correct (handle_instr (PUSHGETGLOBALFIELD n1 n2)) (clight_of (PUSHGETGLOBALFIELD n1 n2))
      (pre_of (PUSHGETGLOBALFIELD n1 n2))
      (P_error_of (PUSHGETGLOBALFIELD n1 n2)) (P_halt_of (PUSHGETGLOBALFIELD n1 n2)) (P_ccall_of (PUSHGETGLOBALFIELD n1 n2)).

  Parameter correct_SETGLOBAL : forall n,
    handler_correct (handle_instr (SETGLOBAL n)) (clight_of (SETGLOBAL n))
      (pre_of (SETGLOBAL n))
      (P_error_of (SETGLOBAL n)) (P_halt_of (SETGLOBAL n)) (P_ccall_of (SETGLOBAL n)).

  Parameter correct_ATOM : forall n,
    handler_correct (handle_instr (ATOM n)) (clight_of (ATOM n))
      (pre_of (ATOM n))
      (P_error_of (ATOM n)) (P_halt_of (ATOM n)) (P_ccall_of (ATOM n)).

  Parameter correct_PUSHATOM : forall n,
    handler_correct (handle_instr (PUSHATOM n)) (clight_of (PUSHATOM n))
      (pre_of (PUSHATOM n))
      (P_error_of (PUSHATOM n)) (P_halt_of (PUSHATOM n)) (P_ccall_of (PUSHATOM n)).

  Parameter correct_MAKEBLOCK : forall n1 n2,
    handler_correct (handle_instr (MAKEBLOCK n1 n2)) (clight_of (MAKEBLOCK n1 n2))
      (pre_of (MAKEBLOCK n1 n2))
      (P_error_of (MAKEBLOCK n1 n2)) (P_halt_of (MAKEBLOCK n1 n2)) (P_ccall_of (MAKEBLOCK n1 n2)).

  Parameter correct_MAKEBLOCK1 : forall n,
    handler_correct (handle_instr (MAKEBLOCK1 n)) (clight_of (MAKEBLOCK1 n))
      (pre_of (MAKEBLOCK1 n))
      (P_error_of (MAKEBLOCK1 n)) (P_halt_of (MAKEBLOCK1 n)) (P_ccall_of (MAKEBLOCK1 n)).

  Parameter correct_MAKEBLOCK2 : forall n,
    handler_correct (handle_instr (MAKEBLOCK2 n)) (clight_of (MAKEBLOCK2 n))
      (pre_of (MAKEBLOCK2 n))
      (P_error_of (MAKEBLOCK2 n)) (P_halt_of (MAKEBLOCK2 n)) (P_ccall_of (MAKEBLOCK2 n)).

  Parameter correct_MAKEBLOCK3 : forall n,
    handler_correct (handle_instr (MAKEBLOCK3 n)) (clight_of (MAKEBLOCK3 n))
      (pre_of (MAKEBLOCK3 n))
      (P_error_of (MAKEBLOCK3 n)) (P_halt_of (MAKEBLOCK3 n)) (P_ccall_of (MAKEBLOCK3 n)).

  Parameter correct_MAKEFLOATBLOCK : forall n,
    handler_correct (handle_instr (MAKEFLOATBLOCK n)) (clight_of (MAKEFLOATBLOCK n))
      (pre_of (MAKEFLOATBLOCK n))
      (P_error_of (MAKEFLOATBLOCK n)) (P_halt_of (MAKEFLOATBLOCK n)) (P_ccall_of (MAKEFLOATBLOCK n)).

  Parameter correct_GETFIELD : forall n,
    handler_correct (handle_instr (GETFIELD n)) (clight_of (GETFIELD n))
      (pre_of (GETFIELD n))
      (P_error_of (GETFIELD n)) (P_halt_of (GETFIELD n)) (P_ccall_of (GETFIELD n)).

  Parameter correct_GETFLOATFIELD : forall n,
    handler_correct (handle_instr (GETFLOATFIELD n)) (clight_of (GETFLOATFIELD n))
      (pre_of (GETFLOATFIELD n))
      (P_error_of (GETFLOATFIELD n)) (P_halt_of (GETFLOATFIELD n)) (P_ccall_of (GETFLOATFIELD n)).

  Parameter correct_SETFIELD : forall n,
    handler_correct (handle_instr (SETFIELD n)) (clight_of (SETFIELD n))
      (pre_of (SETFIELD n))
      (P_error_of (SETFIELD n)) (P_halt_of (SETFIELD n)) (P_ccall_of (SETFIELD n)).

  Parameter correct_SETFLOATFIELD : forall n,
    handler_correct (handle_instr (SETFLOATFIELD n)) (clight_of (SETFLOATFIELD n))
      (pre_of (SETFLOATFIELD n))
      (P_error_of (SETFLOATFIELD n)) (P_halt_of (SETFLOATFIELD n)) (P_ccall_of (SETFLOATFIELD n)).

  Parameter correct_VECTLENGTH :
    handler_correct (handle_instr VECTLENGTH) (clight_of VECTLENGTH)
      (pre_of VECTLENGTH)
      (P_error_of VECTLENGTH) (P_halt_of VECTLENGTH) (P_ccall_of VECTLENGTH).

  Parameter correct_GETVECTITEM :
    handler_correct (handle_instr GETVECTITEM) (clight_of GETVECTITEM)
      (pre_of GETVECTITEM)
      (P_error_of GETVECTITEM) (P_halt_of GETVECTITEM) (P_ccall_of GETVECTITEM).

  Parameter correct_SETVECTITEM :
    handler_correct (handle_instr SETVECTITEM) (clight_of SETVECTITEM)
      (pre_of SETVECTITEM)
      (P_error_of SETVECTITEM) (P_halt_of SETVECTITEM) (P_ccall_of SETVECTITEM).

  Parameter correct_GETBYTESCHAR :
    handler_correct (handle_instr GETBYTESCHAR) (clight_of GETBYTESCHAR)
      (pre_of GETBYTESCHAR)
      (P_error_of GETBYTESCHAR) (P_halt_of GETBYTESCHAR) (P_ccall_of GETBYTESCHAR).

  Parameter correct_SETBYTESCHAR :
    handler_correct (handle_instr SETBYTESCHAR) (clight_of SETBYTESCHAR)
      (pre_of SETBYTESCHAR)
      (P_error_of SETBYTESCHAR) (P_halt_of SETBYTESCHAR) (P_ccall_of SETBYTESCHAR).

  Parameter correct_GETSTRINGCHAR :
    handler_correct (handle_instr GETSTRINGCHAR) (clight_of GETSTRINGCHAR)
      (pre_of GETSTRINGCHAR)
      (P_error_of GETSTRINGCHAR) (P_halt_of GETSTRINGCHAR) (P_ccall_of GETSTRINGCHAR).

  Parameter correct_BRANCH : forall z,
    handler_correct (handle_instr (BRANCH z)) (clight_of (BRANCH z))
      (pre_of (BRANCH z))
      (P_error_of (BRANCH z)) (P_halt_of (BRANCH z)) (P_ccall_of (BRANCH z)).

  Parameter correct_BRANCHIF : forall z,
    handler_correct (handle_instr (BRANCHIF z)) (clight_of (BRANCHIF z))
      (pre_of (BRANCHIF z))
      (P_error_of (BRANCHIF z)) (P_halt_of (BRANCHIF z)) (P_ccall_of (BRANCHIF z)).

  Parameter correct_BRANCHIFNOT : forall z,
    handler_correct (handle_instr (BRANCHIFNOT z)) (clight_of (BRANCHIFNOT z))
      (pre_of (BRANCHIFNOT z))
      (P_error_of (BRANCHIFNOT z)) (P_halt_of (BRANCHIFNOT z)) (P_ccall_of (BRANCHIFNOT z)).

  Parameter correct_SWITCH : forall n1 n2 l1 l2,
    handler_correct (handle_instr (SWITCH n1 n2 l1 l2)) (clight_of (SWITCH n1 n2 l1 l2))
      (pre_of (SWITCH n1 n2 l1 l2))
      (P_error_of (SWITCH n1 n2 l1 l2)) (P_halt_of (SWITCH n1 n2 l1 l2)) (P_ccall_of (SWITCH n1 n2 l1 l2)).

  Parameter correct_BOOLNOT :
    handler_correct (handle_instr BOOLNOT) (clight_of BOOLNOT)
      (pre_of BOOLNOT)
      (P_error_of BOOLNOT) (P_halt_of BOOLNOT) (P_ccall_of BOOLNOT).

  Parameter correct_PUSHTRAP : forall z,
    handler_correct (handle_instr (PUSHTRAP z)) (clight_of (PUSHTRAP z))
      (pre_of (PUSHTRAP z))
      (P_error_of (PUSHTRAP z)) (P_halt_of (PUSHTRAP z)) (P_ccall_of (PUSHTRAP z)).

  Parameter correct_POPTRAP :
    handler_correct (handle_instr POPTRAP) (clight_of POPTRAP)
      (pre_of POPTRAP)
      (P_error_of POPTRAP) (P_halt_of POPTRAP) (P_ccall_of POPTRAP).

  Parameter correct_RAISE :
    handler_correct (handle_instr RAISE) (clight_of RAISE)
      (pre_of RAISE)
      (P_error_of RAISE) (P_halt_of RAISE) (P_ccall_of RAISE).

  Parameter correct_RERAISE :
    handler_correct (handle_instr RERAISE) (clight_of RERAISE)
      (pre_of RERAISE)
      (P_error_of RERAISE) (P_halt_of RERAISE) (P_ccall_of RERAISE).

  Parameter correct_RAISE_NOTRACE :
    handler_correct (handle_instr RAISE_NOTRACE) (clight_of RAISE_NOTRACE)
      (pre_of RAISE_NOTRACE)
      (P_error_of RAISE_NOTRACE) (P_halt_of RAISE_NOTRACE) (P_ccall_of RAISE_NOTRACE).

  Parameter correct_CHECK_SIGNALS :
    handler_correct (handle_instr CHECK_SIGNALS) (clight_of CHECK_SIGNALS)
      (pre_of CHECK_SIGNALS)
      (P_error_of CHECK_SIGNALS) (P_halt_of CHECK_SIGNALS) (P_ccall_of CHECK_SIGNALS).

  Parameter correct_C_CALL : forall n1 n2,
    handler_correct (handle_instr (C_CALL n1 n2)) (clight_of (C_CALL n1 n2))
      (pre_of (C_CALL n1 n2))
      (P_error_of (C_CALL n1 n2)) (P_halt_of (C_CALL n1 n2)) (P_ccall_of (C_CALL n1 n2)).

  Parameter correct_CONSTINT : forall z,
    handler_correct (handle_instr (CONSTINT z)) (clight_of (CONSTINT z))
      (pre_of (CONSTINT z))
      (P_error_of (CONSTINT z)) (P_halt_of (CONSTINT z)) (P_ccall_of (CONSTINT z)).

  Parameter correct_PUSHCONSTINT : forall z,
    handler_correct (handle_instr (PUSHCONSTINT z)) (clight_of (PUSHCONSTINT z))
      (pre_of (PUSHCONSTINT z))
      (P_error_of (PUSHCONSTINT z)) (P_halt_of (PUSHCONSTINT z)) (P_ccall_of (PUSHCONSTINT z)).

  Parameter correct_NEGINT :
    handler_correct (handle_instr NEGINT) (clight_of NEGINT)
      (pre_of NEGINT)
      (P_error_of NEGINT) (P_halt_of NEGINT) (P_ccall_of NEGINT).

  Parameter correct_ADDINT :
    handler_correct (handle_instr ADDINT) (clight_of ADDINT)
      (pre_of ADDINT)
      (P_error_of ADDINT) (P_halt_of ADDINT) (P_ccall_of ADDINT).

  Parameter correct_SUBINT :
    handler_correct (handle_instr SUBINT) (clight_of SUBINT)
      (pre_of SUBINT)
      (P_error_of SUBINT) (P_halt_of SUBINT) (P_ccall_of SUBINT).

  Parameter correct_MULINT :
    handler_correct (handle_instr MULINT) (clight_of MULINT)
      (pre_of MULINT)
      (P_error_of MULINT) (P_halt_of MULINT) (P_ccall_of MULINT).

  Parameter correct_DIVINT :
    handler_correct (handle_instr DIVINT) (clight_of DIVINT)
      (pre_of DIVINT)
      (P_error_of DIVINT) (P_halt_of DIVINT) (P_ccall_of DIVINT).

  Parameter correct_MODINT :
    handler_correct (handle_instr MODINT) (clight_of MODINT)
      (pre_of MODINT)
      (P_error_of MODINT) (P_halt_of MODINT) (P_ccall_of MODINT).

  Parameter correct_ANDINT :
    handler_correct (handle_instr ANDINT) (clight_of ANDINT)
      (pre_of ANDINT)
      (P_error_of ANDINT) (P_halt_of ANDINT) (P_ccall_of ANDINT).

  Parameter correct_ORINT :
    handler_correct (handle_instr ORINT) (clight_of ORINT)
      (pre_of ORINT)
      (P_error_of ORINT) (P_halt_of ORINT) (P_ccall_of ORINT).

  Parameter correct_XORINT :
    handler_correct (handle_instr XORINT) (clight_of XORINT)
      (pre_of XORINT)
      (P_error_of XORINT) (P_halt_of XORINT) (P_ccall_of XORINT).

  Parameter correct_LSLINT :
    handler_correct (handle_instr LSLINT) (clight_of LSLINT)
      (pre_of LSLINT)
      (P_error_of LSLINT) (P_halt_of LSLINT) (P_ccall_of LSLINT).

  Parameter correct_LSRINT :
    handler_correct (handle_instr LSRINT) (clight_of LSRINT)
      (pre_of LSRINT)
      (P_error_of LSRINT) (P_halt_of LSRINT) (P_ccall_of LSRINT).

  Parameter correct_ASRINT :
    handler_correct (handle_instr ASRINT) (clight_of ASRINT)
      (pre_of ASRINT)
      (P_error_of ASRINT) (P_halt_of ASRINT) (P_ccall_of ASRINT).

  Parameter correct_EQ :
    handler_correct (handle_instr EQ) (clight_of EQ)
      (pre_of EQ)
      (P_error_of EQ) (P_halt_of EQ) (P_ccall_of EQ).

  Parameter correct_NEQ :
    handler_correct (handle_instr NEQ) (clight_of NEQ)
      (pre_of NEQ)
      (P_error_of NEQ) (P_halt_of NEQ) (P_ccall_of NEQ).

  Parameter correct_LTINT :
    handler_correct (handle_instr LTINT) (clight_of LTINT)
      (pre_of LTINT)
      (P_error_of LTINT) (P_halt_of LTINT) (P_ccall_of LTINT).

  Parameter correct_LEINT :
    handler_correct (handle_instr LEINT) (clight_of LEINT)
      (pre_of LEINT)
      (P_error_of LEINT) (P_halt_of LEINT) (P_ccall_of LEINT).

  Parameter correct_GTINT :
    handler_correct (handle_instr GTINT) (clight_of GTINT)
      (pre_of GTINT)
      (P_error_of GTINT) (P_halt_of GTINT) (P_ccall_of GTINT).

  Parameter correct_GEINT :
    handler_correct (handle_instr GEINT) (clight_of GEINT)
      (pre_of GEINT)
      (P_error_of GEINT) (P_halt_of GEINT) (P_ccall_of GEINT).

  Parameter correct_OFFSETINT : forall z,
    handler_correct (handle_instr (OFFSETINT z)) (clight_of (OFFSETINT z))
      (pre_of (OFFSETINT z))
      (P_error_of (OFFSETINT z)) (P_halt_of (OFFSETINT z)) (P_ccall_of (OFFSETINT z)).

  Parameter correct_OFFSETREF : forall z,
    handler_correct (handle_instr (OFFSETREF z)) (clight_of (OFFSETREF z))
      (pre_of (OFFSETREF z))
      (P_error_of (OFFSETREF z)) (P_halt_of (OFFSETREF z)) (P_ccall_of (OFFSETREF z)).

  Parameter correct_ISINT :
    handler_correct (handle_instr ISINT) (clight_of ISINT)
      (pre_of ISINT)
      (P_error_of ISINT) (P_halt_of ISINT) (P_ccall_of ISINT).

  Parameter correct_GETMETHOD :
    handler_correct (handle_instr GETMETHOD) (clight_of GETMETHOD)
      (pre_of GETMETHOD)
      (P_error_of GETMETHOD) (P_halt_of GETMETHOD) (P_ccall_of GETMETHOD).

  Parameter correct_GETPUBMET : forall z,
    handler_correct (handle_instr (GETPUBMET z)) (clight_of (GETPUBMET z))
      (pre_of (GETPUBMET z))
      (P_error_of (GETPUBMET z)) (P_halt_of (GETPUBMET z)) (P_ccall_of (GETPUBMET z)).

  Parameter correct_GETDYNMET :
    handler_correct (handle_instr GETDYNMET) (clight_of GETDYNMET)
      (pre_of GETDYNMET)
      (P_error_of GETDYNMET) (P_halt_of GETDYNMET) (P_ccall_of GETDYNMET).

  Parameter correct_BEQ : forall z1 z2,
    handler_correct (handle_instr (BEQ z1 z2)) (clight_of (BEQ z1 z2))
      (pre_of (BEQ z1 z2))
      (P_error_of (BEQ z1 z2)) (P_halt_of (BEQ z1 z2)) (P_ccall_of (BEQ z1 z2)).

  Parameter correct_BNEQ : forall z1 z2,
    handler_correct (handle_instr (BNEQ z1 z2)) (clight_of (BNEQ z1 z2))
      (pre_of (BNEQ z1 z2))
      (P_error_of (BNEQ z1 z2)) (P_halt_of (BNEQ z1 z2)) (P_ccall_of (BNEQ z1 z2)).

  Parameter correct_BLTINT : forall z1 z2,
    handler_correct (handle_instr (BLTINT z1 z2)) (clight_of (BLTINT z1 z2))
      (pre_of (BLTINT z1 z2))
      (P_error_of (BLTINT z1 z2)) (P_halt_of (BLTINT z1 z2)) (P_ccall_of (BLTINT z1 z2)).

  Parameter correct_BLEINT : forall z1 z2,
    handler_correct (handle_instr (BLEINT z1 z2)) (clight_of (BLEINT z1 z2))
      (pre_of (BLEINT z1 z2))
      (P_error_of (BLEINT z1 z2)) (P_halt_of (BLEINT z1 z2)) (P_ccall_of (BLEINT z1 z2)).

  Parameter correct_BGTINT : forall z1 z2,
    handler_correct (handle_instr (BGTINT z1 z2)) (clight_of (BGTINT z1 z2))
      (pre_of (BGTINT z1 z2))
      (P_error_of (BGTINT z1 z2)) (P_halt_of (BGTINT z1 z2)) (P_ccall_of (BGTINT z1 z2)).

  Parameter correct_BGEINT : forall z1 z2,
    handler_correct (handle_instr (BGEINT z1 z2)) (clight_of (BGEINT z1 z2))
      (pre_of (BGEINT z1 z2))
      (P_error_of (BGEINT z1 z2)) (P_halt_of (BGEINT z1 z2)) (P_ccall_of (BGEINT z1 z2)).

  Parameter correct_ULTINT :
    handler_correct (handle_instr ULTINT) (clight_of ULTINT)
      (pre_of ULTINT)
      (P_error_of ULTINT) (P_halt_of ULTINT) (P_ccall_of ULTINT).

  Parameter correct_UGEINT :
    handler_correct (handle_instr UGEINT) (clight_of UGEINT)
      (pre_of UGEINT)
      (P_error_of UGEINT) (P_halt_of UGEINT) (P_ccall_of UGEINT).

  Parameter correct_BULTINT : forall z1 z2,
    handler_correct (handle_instr (BULTINT z1 z2)) (clight_of (BULTINT z1 z2))
      (pre_of (BULTINT z1 z2))
      (P_error_of (BULTINT z1 z2)) (P_halt_of (BULTINT z1 z2)) (P_ccall_of (BULTINT z1 z2)).

  Parameter correct_BUGEINT : forall z1 z2,
    handler_correct (handle_instr (BUGEINT z1 z2)) (clight_of (BUGEINT z1 z2))
      (pre_of (BUGEINT z1 z2))
      (P_error_of (BUGEINT z1 z2)) (P_halt_of (BUGEINT z1 z2)) (P_ccall_of (BUGEINT z1 z2)).

  Parameter correct_STOP :
    handler_correct (handle_instr STOP) (clight_of STOP)
      (pre_of STOP)
      (P_error_of STOP) (P_halt_of STOP) (P_ccall_of STOP).

End InstructVerificationFineGrainedSpec.

Module Type InstructVerificationSpec (Import HI : HandleInstrSpec).
  Parameter handler_correct_all :
    forall i, handler_correct (handle_instr i) (clight_of i)
                (pre_of i)
                (P_error_of i) (P_halt_of i) (P_ccall_of i).
End InstructVerificationSpec.

Module InstructVerificationFromFineGrained
       (Import HI : HandleInstrSpec)
       (Import FG : InstructVerificationFineGrainedSpec HI) <: InstructVerificationSpec HI.

    Lemma handler_correct_all :
      forall i, handler_correct (handle_instr i) (clight_of i)
                  (pre_of i)
                  (P_error_of i) (P_halt_of i) (P_ccall_of i).
    Proof.
      intro i; destruct i;
      [ apply correct_ACC | apply correct_PUSH | apply correct_PUSHACC | apply correct_POP
      | apply correct_ASSIGN | apply correct_ENVACC | apply correct_PUSHENVACC
      | apply correct_PUSH_RETADDR | apply correct_APPLY | apply correct_APPLY1
      | apply correct_APPLY2 | apply correct_APPLY3 | apply correct_APPTERM
      | apply correct_APPTERM1 | apply correct_APPTERM2 | apply correct_APPTERM3
      | apply correct_RETURN | apply correct_RESTART | apply correct_GRAB
      | apply correct_CLOSURE | apply correct_CLOSUREREC | apply correct_OFFSETCLOSURE
      | apply correct_PUSHOFFSETCLOSURE | apply correct_GETGLOBAL | apply correct_PUSHGETGLOBAL
      | apply correct_GETGLOBALFIELD | apply correct_PUSHGETGLOBALFIELD | apply correct_SETGLOBAL
      | apply correct_ATOM | apply correct_PUSHATOM | apply correct_MAKEBLOCK
      | apply correct_MAKEBLOCK1 | apply correct_MAKEBLOCK2 | apply correct_MAKEBLOCK3
      | apply correct_MAKEFLOATBLOCK | apply correct_GETFIELD | apply correct_GETFLOATFIELD
      | apply correct_SETFIELD | apply correct_SETFLOATFIELD | apply correct_VECTLENGTH
      | apply correct_GETVECTITEM | apply correct_SETVECTITEM | apply correct_GETBYTESCHAR
      | apply correct_SETBYTESCHAR | apply correct_GETSTRINGCHAR | apply correct_BRANCH
      | apply correct_BRANCHIF | apply correct_BRANCHIFNOT | apply correct_SWITCH
      | apply correct_BOOLNOT | apply correct_PUSHTRAP | apply correct_POPTRAP
      | apply correct_RAISE | apply correct_RERAISE | apply correct_RAISE_NOTRACE
      | apply correct_CHECK_SIGNALS | apply correct_C_CALL | apply correct_CONSTINT
      | apply correct_PUSHCONSTINT | apply correct_NEGINT | apply correct_ADDINT
      | apply correct_SUBINT | apply correct_MULINT | apply correct_DIVINT
      | apply correct_MODINT | apply correct_ANDINT | apply correct_ORINT
      | apply correct_XORINT | apply correct_LSLINT | apply correct_LSRINT
      | apply correct_ASRINT | apply correct_EQ | apply correct_NEQ
      | apply correct_LTINT | apply correct_LEINT | apply correct_GTINT
      | apply correct_GEINT | apply correct_OFFSETINT | apply correct_OFFSETREF
      | apply correct_ISINT | apply correct_GETMETHOD | apply correct_GETPUBMET
      | apply correct_GETDYNMET | apply correct_BEQ | apply correct_BNEQ
      | apply correct_BLTINT | apply correct_BLEINT | apply correct_BGTINT
      | apply correct_BGEINT | apply correct_ULTINT | apply correct_UGEINT
      | apply correct_BULTINT | apply correct_BUGEINT | apply correct_STOP ].
    Qed.
End InstructVerificationFromFineGrained.

