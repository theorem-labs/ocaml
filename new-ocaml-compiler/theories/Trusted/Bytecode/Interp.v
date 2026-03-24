(* Interp.v - [TRUSTED] OCaml bytecode interpreter.
   Core trusted component: step function + fuel-based run loop.
   Each case corresponds one-to-one to a case in OCaml's runtime/interp.c. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From OCamlInterp.Trusted.Bytecode Require Import Value AST Machine.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Local Notation nth_error := List.nth_error (only parsing).
Local Notation length := Datatypes.length (only parsing).
Local Notation skipn := List.skipn (only parsing).
Local Notation firstn := List.firstn (only parsing).

(* OCaml int is 63-bit on 64-bit architectures. *)
Definition word_bits := 63.
Definition z_unsigned (a : Z) : Z := Z.land a (Z.ones word_bits).
Definition z_lsr (a b : Z) : Z := Z.shiftr (z_unsigned a) b.

Definition get_code_ptr_from (fields : list value) (ofs : nat) : option Z :=
  match nth_error fields ofs with
  | Some (Val_int pc) => Some pc
  | _ => None
  end.

Definition get_code_ptr_s (s : state) (v : value) : option Z :=
  match v with
  | Val_block t fields =>
    if Nat.eqb t Closure_tag then
      match fields with Val_int pc :: _ => Some pc | _ => None end
    else None
  | Val_closure addr ofs =>
    match heap_lookup s.(hp) addr with
    | Some (t, fields) =>
      if Nat.eqb t Closure_tag then get_code_ptr_from fields ofs
      else None
    | None => None
    end
  | _ => None
  end.

(* Helper: build a new state sharing heap from the input state, with updated
   trap_sp.  Most instructions leave trap_sp unchanged; pass s.(trap_sp). *)
Definition st (s : state) (pc : Z) (accu : value) (stack : list value)
  (env : value) (ea : nat) (glob : list value) (tsp : nat) : state :=
  mk_state pc accu stack env ea glob tsp s.(hp) s.(next_addr).

Definition step (code : list instruction) (s : state) : step_result :=
  match nth_error code (Z.to_nat s.(pc)) with
  | None => Error "pc out of bounds"
  | Some instr =>
  let pc' := s.(pc) + 1 in
  match instr with

  | ACC n =>
    match nth_error s.(stack) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "ACC: stack underflow"
    end

  | PUSH =>
    Step (st s pc' s.(accu) (s.(accu) :: s.(stack)) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | PUSHACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error new_stack n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "PUSHACC: stack underflow"
    end

  | POP n =>
    Step (st s pc' s.(accu) (skipn n s.(stack)) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | ASSIGN n =>
    match set_nth s.(stack) n s.(accu) with
    | Some new_stack => Step (st s pc' val_unit new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "ASSIGN: stack underflow"
    end

  | ENVACC n =>
    match field_or_heap s s.(env) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "ENVACC: env access out of bounds"
    end

  | PUSHENVACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match field_or_heap s s.(env) n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "PUSHENVACC: env access out of bounds"
    end

  (* PUSH_RETADDR: pushes [ret_addr, env, extra_args] onto the stack.
     In interp.c: sp[0]=pc+ofs, sp[1]=env, sp[2]=Long_val(extra_args). *)
  | PUSH_RETADDR ret_addr =>
    let frame := Val_int ret_addr :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    Step (st s pc' s.(accu) frame s.(env) s.(extra_args) s.(global) s.(trap_sp))

  (* APPLY n: tail call with n args already on stack; sets extra_args = n-1. *)
  | APPLY n =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (st s target_pc s.(accu) s.(stack) s.(accu) (Nat.sub n 1) s.(global) s.(trap_sp))
    | None => Error "APPLY: accu is not a closure"
    end

  (* APPLY1/2/3: save return frame then call closure. *)
  | APPLY1 =>
    match s.(stack) with
    | arg1 :: rest =>
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        let new_stack := arg1 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
        Step (st s target_pc s.(accu) new_stack s.(accu) 0 s.(global) s.(trap_sp))
      | None => Error "APPLY1: accu is not a closure"
      end
    | _ => Error "APPLY1: stack underflow"
    end

  | APPLY2 =>
    match s.(stack) with
    | arg1 :: arg2 :: rest =>
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        let new_stack := arg1 :: arg2 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
        Step (st s target_pc s.(accu) new_stack s.(accu) 1 s.(global) s.(trap_sp))
      | None => Error "APPLY2: accu is not a closure"
      end
    | _ => Error "APPLY2: stack underflow"
    end

  | APPLY3 =>
    match s.(stack) with
    | arg1 :: arg2 :: arg3 :: rest =>
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        let new_stack := arg1 :: arg2 :: arg3 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
        Step (st s target_pc s.(accu) new_stack s.(accu) 2 s.(global) s.(trap_sp))
      | None => Error "APPLY3: accu is not a closure"
      end
    | _ => Error "APPLY3: stack underflow"
    end

  (* APPTERM n s: slide top n args down by (slotsize - n), tail call. *)
  | APPTERM nargs slotsize =>
    let args := firstn nargs s.(stack) in
    let base := skipn slotsize s.(stack) in
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (st s target_pc s.(accu) (args ++ base) s.(accu) (Nat.add s.(extra_args) (Nat.sub nargs 1)) s.(global) s.(trap_sp))
    | None => Error "APPTERM: accu is not a closure"
    end

  | APPTERM1 slotsize =>
    match s.(stack) with
    | arg1 :: _ =>
      let base := skipn slotsize s.(stack) in
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) (arg1 :: base) s.(accu) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "APPTERM1: accu is not a closure"
      end
    | _ => Error "APPTERM1: stack underflow"
    end

  | APPTERM2 slotsize =>
    match s.(stack) with
    | arg1 :: arg2 :: _ =>
      let base := skipn slotsize s.(stack) in
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) (arg1 :: arg2 :: base) s.(accu) (Nat.add s.(extra_args) 1) s.(global) s.(trap_sp))
      | None => Error "APPTERM2: accu is not a closure"
      end
    | _ => Error "APPTERM2: stack underflow"
    end

  | APPTERM3 slotsize =>
    match s.(stack) with
    | arg1 :: arg2 :: arg3 :: _ =>
      let base := skipn slotsize s.(stack) in
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) (arg1 :: arg2 :: arg3 :: base) s.(accu) (Nat.add s.(extra_args) 2) s.(global) s.(trap_sp))
      | None => Error "APPTERM3: accu is not a closure"
      end
    | _ => Error "APPTERM3: stack underflow"
    end

  (* RETURN n: pop n locals; if extra_args > 0 tail-call accu, else restore return frame. *)
  | RETURN stacksize =>
    let stk := skipn stacksize s.(stack) in
    if Nat.ltb 0 s.(extra_args) then
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) stk s.(accu) (Nat.sub s.(extra_args) 1) s.(global) s.(trap_sp))
      | None => Error "RETURN: accu is not a closure"
      end
    else
      match stk with
      | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
        Step (st s ret_pc s.(accu) rest saved_env (Z.to_nat saved_ea) s.(global) s.(trap_sp))
      | _ => Error "RETURN: malformed return frame"
      end

  (* RESTART: restore args from partial application closure in env. *)
  | RESTART =>
    let restart_fields (all_fields : list value) (ofs : nat) : step_result :=
      let fields := skipn ofs all_fields in
      let num_args := Nat.sub (length fields) 3 in
      let args := skipn 3 fields in
      let new_stack := args ++ s.(stack) in
      match nth_error fields 2 with
      | Some saved_env =>
        Step (st s pc' s.(accu) new_stack saved_env (Nat.add s.(extra_args) num_args) s.(global) s.(trap_sp))
      | None => Error "RESTART: malformed closure"
      end in
    match s.(env) with
    | Val_closure addr ofs =>
      match heap_lookup s.(hp) addr with
      | Some (t, all_fields) =>
        if Nat.eqb t Closure_tag then restart_fields all_fields ofs
        else Error "RESTART: env is not a closure"
      | None => Error "RESTART: dangling pointer"
      end
    | Val_block t fields =>
      if Nat.eqb t Closure_tag then restart_fields fields 0%nat
      else Error "RESTART: env is not a closure"
    | _ => Error "RESTART: env is not a block"
    end

  (* GRAB n: if extra_args >= n, consume n and continue;
     else build partial application closure and return to caller. *)
  | GRAB required =>
    if Nat.leb required s.(extra_args) then
      Step (st s pc' s.(accu) s.(stack) s.(env) (Nat.sub s.(extra_args) required) s.(global) s.(trap_sp))
    else
      let num_args := S s.(extra_args) in
      let saved_args := firstn num_args s.(stack) in
      let rest_stack := skipn num_args s.(stack) in
      (* Partial application closure: [code=RESTART, closinfo, saved_env, arg1, ...] *)
      let closinfo := Val_int 0 in
      let fields := Val_int (s.(pc) - 1) :: closinfo :: s.(env) :: saved_args in
      let '(s', base_ptr) := heap_alloc s Closure_tag fields in
      let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
      let closure := Val_closure addr 0%nat in
      match rest_stack with
      | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
        Step (st s' ret_pc closure rest saved_env (Z.to_nat saved_ea) s.(global) s.(trap_sp))
      | _ => Error "GRAB: malformed return frame"
      end

  (* CLOSURE n ofs: build closure of n+1 fields [code, closinfo, v0, ..., vn-1].
     If n > 0 the accumulator is pushed first (it becomes v0). *)
  | CLOSURE nvars code_ofs =>
    let stk := if Nat.ltb 0 nvars then s.(accu) :: s.(stack) else s.(stack) in
    let vars := firstn nvars stk in
    let rest := skipn nvars stk in
    let closinfo := Val_int 0 in
    let fields := Val_int code_ofs :: closinfo :: vars in
    let '(s', base_ptr) := heap_alloc s Closure_tag fields in
    let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
    let closure := Val_closure addr 0%nat in
    Step (st s' pc' closure rest s.(env) s.(extra_args) s.(global) s.(trap_sp))

  (* CLOSUREREC nf nv [ofs0;ofs1;...]: build flat closure block of
     (nf*3-1+nv) fields.  Layout: [code0,ci0, infix,code1,ci1, ..., v0,v1,...]
     Each closure_i is pushed as Val_closure(addr, 3*i). *)
  | CLOSUREREC nfuncs nvars code_offsets =>
    let stk := if Nat.ltb 0 nvars then s.(accu) :: s.(stack) else s.(stack) in
    let vars := firstn nvars stk in
    let rest := skipn nvars stk in
    match code_offsets with
    | [] => Error "CLOSUREREC: no code offsets"
    | _ =>
      let closinfo := Val_int 0 in
      let infix_hdr := Val_block Infix_tag [] in
      let fix build_closure_fields (i : nat) (offsets : list Z) : list value :=
        match offsets with
        | [] => vars
        | ofs :: rest_ofs =>
          if Nat.eqb i 0 then
            Val_int ofs :: closinfo :: build_closure_fields 1%nat rest_ofs
          else
            infix_hdr :: Val_int ofs :: closinfo :: build_closure_fields (S i) rest_ofs
        end in
      let fields := build_closure_fields 0%nat code_offsets in
      let '(s', base_ptr) := heap_alloc s Closure_tag fields in
      let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
      let closure_at (i : nat) : value :=
        if Nat.eqb i 0 then Val_closure addr 0%nat
        else Val_closure addr (3 * i) in
      (* Push closures: closure_{nf-1} on top, closure_0 at bottom.
         After this instruction accu = closure_0. *)
      let fix push_closures (i : nat) (stk : list value) : list value :=
        match i with
        | O => stk
        | S i' =>
          let stk' := push_closures i' stk in
          closure_at i' :: stk'
        end in
      let new_stack := push_closures nfuncs rest in
      Step (st s' pc' (closure_at 0%nat) new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    end

  (* OFFSETCLOSURE n: accu := env offset by n fields (within the same heap block). *)
  | OFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      Step (st s pc' (Val_closure addr new_ofs) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (st s pc' s.(env) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
      else Error "OFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "OFFSETCLOSURE: invalid env"
    end

  | PUSHOFFSETCLOSURE ofs =>
    let new_stack := s.(accu) :: s.(stack) in
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      Step (st s pc' (Val_closure addr new_ofs) new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (st s pc' s.(env) new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
      else Error "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "PUSHOFFSETCLOSURE: invalid env"
    end

  | GETGLOBAL n =>
    match nth_error s.(global) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "GETGLOBAL: index out of bounds"
    end

  | PUSHGETGLOBAL n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "PUSHGETGLOBAL: index out of bounds"
    end

  | GETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "GETGLOBALFIELD: field access failed"
      end
    | None => Error "GETGLOBALFIELD: index out of bounds"
    end

  | PUSHGETGLOBALFIELD n p =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "PUSHGETGLOBALFIELD: field access failed"
      end
    | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
    end

  | SETGLOBAL n =>
    let new_global := match set_nth s.(global) n s.(accu) with
                      | Some g => g | None => s.(global) end in
    Step (st s pc' val_unit s.(stack) s.(env) s.(extra_args) new_global s.(trap_sp))

  | ATOM t =>
    let '(s', ptr) := heap_alloc s t [] in
    Step (st s' pc' ptr s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | PUSHATOM t =>
    let new_stack := s.(accu) :: s.(stack) in
    let '(s', ptr) := heap_alloc s t [] in
    Step (st s' pc' ptr new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))

  (* MAKEBLOCK tag size: accu=field0, pop (size-1) from stack. *)
  | MAKEBLOCK t size =>
    let fields := s.(accu) :: firstn (Nat.sub size 1) s.(stack) in
    let new_stack := skipn (Nat.sub size 1) s.(stack) in
    let '(s', ptr) := heap_alloc s t fields in
    Step (st s' pc' ptr new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | MAKEBLOCK1 t =>
    let '(s', ptr) := heap_alloc s t [s.(accu)] in
    Step (st s' pc' ptr s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | MAKEBLOCK2 t =>
    match s.(stack) with
    | v1 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
      Step (st s' pc' ptr rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "MAKEBLOCK2: stack underflow"
    end

  | MAKEBLOCK3 t =>
    match s.(stack) with
    | v1 :: v2 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1; v2] in
      Step (st s' pc' ptr rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "MAKEBLOCK3: stack underflow"
    end

  | MAKEFLOATBLOCK _ => Error "MAKEFLOATBLOCK: not supported"

  | GETFIELD n =>
    match field_or_heap s s.(accu) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "GETFIELD: access failed"
    end

  | GETFLOATFIELD _ => Error "GETFLOATFIELD: not supported"

  | SETFIELD n =>
    match s.(stack) with
    | newval :: rest =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields n newval with
          | Some new_fields =>
            let new_hp := heap_update s.(hp) addr new_fields in
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_sp) new_hp s.(next_addr))
          | None => Error "SETFIELD: index out of bounds"
          end
        | None => Error "SETFIELD: dangling pointer"
        end
      | _ => Error "SETFIELD: not a mutable block"
      end
    | _ => Error "SETFIELD: stack underflow"
    end

  | SETFLOATFIELD _ => Error "SETFLOATFIELD: not supported"

  | VECTLENGTH =>
    match size_or_heap s s.(accu) with
    | Some n => Step (st s pc' (Val_int (Z.of_nat n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | None => Error "VECTLENGTH: not a block"
    end

  | GETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: rest =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some v => Step (st s pc' v rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "GETVECTITEM: index out of bounds"
      end
    | _ => Error "GETVECTITEM: bad index or stack underflow"
    end

  | SETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: newval :: rest =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields (Z.to_nat idx) newval with
          | Some new_fields =>
            let new_hp := heap_update s.(hp) addr new_fields in
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_sp) new_hp s.(next_addr))
          | None => Error "SETVECTITEM: index out of bounds"
          end
        | None => Error "SETVECTITEM: dangling pointer"
        end
      | _ => Error "SETVECTITEM: not a heap block"
      end
    | _ => Error "SETVECTITEM: stack underflow"
    end

  | GETBYTESCHAR | GETSTRINGCHAR =>
    match s.(stack) with
    | Val_int idx :: rest =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some (Val_int c) => Step (st s pc' (Val_int c) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | _ => Error "GETSTRINGCHAR: index out of bounds or not a char"
      end
    | _ => Error "GETSTRINGCHAR: stack underflow"
    end

  | SETBYTESCHAR =>
    match s.(stack) with
    | Val_int idx :: Val_int newchar :: rest =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields (Z.to_nat idx) (Val_int newchar) with
          | Some new_fields =>
            let new_hp := heap_update s.(hp) addr new_fields in
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_sp) new_hp s.(next_addr))
          | None => Error "SETBYTESCHAR: index out of bounds"
          end
        | None => Error "SETBYTESCHAR: dangling pointer"
        end
      | _ => Error "SETBYTESCHAR: not a heap bytes"
      end
    | _ => Error "SETBYTESCHAR: stack underflow"
    end

  | BRANCH target =>
    Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | BRANCHIF target =>
    match s.(accu) with
    | Val_int 0 => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    end

  | BRANCHIFNOT target =>
    match s.(accu) with
    | Val_int 0 => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    end

  | SWITCH _nc _nb const_targets block_targets =>
    match s.(accu) with
    | Val_int n =>
      match nth_error const_targets (Z.to_nat n) with
      | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "SWITCH: constant index out of range"
      end
    | Val_block t _ =>
      match nth_error block_targets t with
      | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
      | None => Error "SWITCH: block tag out of range"
      end
    | Val_ptr addr | Val_closure addr _ =>
      match tag_or_heap s s.(accu) with
      | Some t =>
        match nth_error block_targets t with
        | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
        | None => Error "SWITCH: block tag out of range"
        end
      | None => Error "SWITCH: dangling pointer"
      end
    end

  | BOOLNOT =>
    match s.(accu) with
    | Val_int 0 => Step (st s pc' val_true s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Step (st s pc' val_false s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    end

  (* PUSHTRAP: push trap frame [handler_pc, prev_trap_sp, env, extra_args] onto
     the stack, then set trap_sp = length(new_stack).
     Layout mirrors interp.c: sp[0]=handler_pc, sp[1]=trap_link, sp[2]=env, sp[3]=extra_args. *)
  | PUSHTRAP handler_pc =>
    let prev_tsp := Val_int (Z.of_nat s.(trap_sp)) in
    let new_stack := Val_int handler_pc :: prev_tsp :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    let new_tsp := length new_stack in
    Step (st s pc' s.(accu) new_stack s.(env) s.(extra_args) s.(global) new_tsp)

  (* POPTRAP: restore trap_sp from the trap link (sp[1]) and pop 4 values.
     For well-formed code the trap frame is always at the current stack top. *)
  | POPTRAP =>
    match s.(stack) with
    | _ :: Val_int prev_tsp :: _ :: _ :: rest =>
      Step (st s pc' s.(accu) rest s.(env) s.(extra_args) s.(global) (Z.to_nat prev_tsp))
    | _ => Error "POPTRAP: malformed trap frame"
    end

  (* RAISE/RERAISE/RAISE_NOTRACE: restore sp to the trap frame, extract
     handler_pc / prev_trap_sp / env / extra_args from the frame, and jump.
     In interp.c: sp = trapsp; pc = Trap_pc(sp); trapsp = sp+link; env=sp[2]; ea=sp[3]; sp+=4. *)
  | RAISE | RERAISE | RAISE_NOTRACE =>
    if Nat.eqb s.(trap_sp) 0 then Error "unhandled exception"
    else
      let k := Nat.sub (length s.(stack)) s.(trap_sp) in
      let frame_top := skipn k s.(stack) in
      match frame_top with
      | Val_int handler_pc :: Val_int prev_tsp :: saved_env :: Val_int saved_ea :: rest =>
        Step (mk_state handler_pc s.(accu) rest saved_env (Z.to_nat saved_ea) s.(global)
                       (Z.to_nat prev_tsp) s.(hp) s.(next_addr))
      | _ => Error "RAISE: malformed trap frame"
      end

  | CHECK_SIGNALS =>
    Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  (* C_CALL: suspend and request a C primitive call. *)
  | C_CALL nargs prim_idx =>
    let args := s.(accu) :: firstn (Nat.sub nargs 1) s.(stack) in
    let new_stack := skipn (Nat.sub nargs 1) s.(stack) in
    let cont := st s pc' val_unit new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp) in
    CCall_request prim_idx args cont

  | CONSTINT n =>
    Step (st s pc' (Val_int n) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | PUSHCONSTINT n =>
    let new_stack := s.(accu) :: s.(stack) in
    Step (st s pc' (Val_int n) new_stack s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | NEGINT =>
    match s.(accu) with
    | Val_int n => Step (st s pc' (Val_int (- n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "NEGINT: not an integer"
    end

  | ADDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a + b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "ADDINT: type error or stack underflow"
    end

  | SUBINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a - b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "SUBINT: type error or stack underflow"
    end

  | MULINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a * b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "MULINT: type error or stack underflow"
    end

  | DIVINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then Error "DIVINT: division by zero"
      else Step (st s pc' (Val_int (Z.quot a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "DIVINT: type error or stack underflow"
    end

  | MODINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then Error "MODINT: division by zero"
      else Step (st s pc' (Val_int (Z.rem a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "MODINT: type error or stack underflow"
    end

  | ANDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.land a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "ANDINT: type error or stack underflow"
    end

  | ORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.lor a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "ORINT: type error or stack underflow"
    end

  | XORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.lxor a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "XORINT: type error or stack underflow"
    end

  | LSLINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.shiftl a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "LSLINT: type error or stack underflow"
    end

  | LSRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (z_lsr a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "LSRINT: type error or stack underflow"
    end

  | ASRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.shiftr a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "ASRINT: type error or stack underflow"
    end

  | EQ =>
    match s.(stack) with
    | b :: rest => Step (st s pc' (if value_eqb s.(accu) b then val_true else val_false) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "EQ: stack underflow"
    end

  | NEQ =>
    match s.(stack) with
    | b :: rest => Step (st s pc' (if value_eqb s.(accu) b then val_false else val_true) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "NEQ: stack underflow"
    end

  | LTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a <? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "LTINT: type error or stack underflow"
    end

  | LEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a <=? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "LEINT: type error or stack underflow"
    end

  | GTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a >? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "GTINT: type error or stack underflow"
    end

  | GEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a >=? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "GEINT: type error or stack underflow"
    end

  | OFFSETINT n =>
    match s.(accu) with
    | Val_int a => Step (st s pc' (Val_int (a + n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "OFFSETINT: not an integer"
    end

  | OFFSETREF n =>
    match s.(accu) with
    | Val_ptr addr =>
      match heap_lookup s.(hp) addr with
      | Some (_, Val_int old :: rest) =>
        let new_hp := heap_update s.(hp) addr (Val_int (old + n) :: rest) in
        Step (mk_state pc' val_unit s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp) new_hp s.(next_addr))
      | _ => Error "OFFSETREF: not a ref"
      end
    | _ => Error "OFFSETREF: not a ref"
    end

  | ISINT =>
    Step (st s pc' (if is_int s.(accu) then val_true else val_false) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | GETMETHOD => Error "GETMETHOD: OO not supported"
  | GETPUBMET _ => Error "GETPUBMET: OO not supported"
  | GETDYNMET => Error "GETDYNMET: OO not supported"

  (* B-comparison instructions: the spec says "increments pc by ofs-1 if val CMP accu".
     In interp.c the operand is an absolute instruction index (after decode). *)
  | BEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BEQ: not an integer"
    end

  | BNEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BNEQ: not an integer"
    end

  (* B-comparison instructions: semantics is *pc++ CMP Long_val(accu),
     i.e., the OPERAND is on the LEFT and ACCU on the RIGHT. *)

  | BLTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BLTINT: not an integer"
    end

  | BLEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.leb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BLEINT: not an integer"
    end

  | BGTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.gtb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BGTINT: not an integer"
    end

  | BGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BGEINT: not an integer"
    end

  | ULTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (z_unsigned a <? z_unsigned b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "ULTINT: type error or stack underflow"
    end

  | UGEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (z_unsigned a >=? z_unsigned b)) rest s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _, _ => Error "UGEINT: type error or stack underflow"
    end

  | BULTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb (z_unsigned n) (z_unsigned a) then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BULTINT: not an integer"
    end

  | BUGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb (z_unsigned n) (z_unsigned a) then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
    | _ => Error "BUGEINT: not an integer"
    end

  | STOP => Halt s.(accu)
  | EVENT => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))
  | BREAK => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_sp))

  | PERFORM => Error "PERFORM: effects not supported"
  | RESUME => Error "RESUME: effects not supported"
  | RESUMETERM _ => Error "RESUMETERM: effects not supported"
  | REPERFORMTERM _ => Error "REPERFORMTERM: effects not supported"

  end
  end.

Fixpoint run (fuel : nat) (code : list instruction) (s : state)
  (handle_ccall : nat -> list value -> option value) : run_result :=
  match fuel with
  | O => Out_of_fuel s
  | S fuel' =>
    match step code s with
    | Step s' => run fuel' code s' handle_ccall
    | Halt v => Finished v
    | Error msg => Run_error msg
    | CCall_request prim_idx args cont =>
      match handle_ccall prim_idx args with
      | Some result => run fuel' code (set_accu cont result) handle_ccall
      | None => Run_error "C call failed"
      end
    end
  end.

Definition run_pure (fuel : nat) (code : list instruction) (global_data : list value) : run_result :=
  run fuel code (initial_state global_data) (fun _ _ => None).
