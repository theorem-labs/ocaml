(* Interp.v - [TRUSTED] OCaml bytecode interpreter.
   Core trusted component: step function + fuel-based run loop.
   Each case corresponds one-to-one to a case in OCaml's runtime/interp.c. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From OCamlInterp.Trusted Require Import Value Bytecode Machine.
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

(* Helper: build state with same heap as the input state *)
Definition st (s : state) (pc : Z) (accu : value) (stack : list value)
  (env : value) (ea : nat) (glob : list value) (ts : list trap_frame) : state :=
  mk_state pc accu stack env ea glob ts s.(hp) s.(next_addr).

Definition step (code : list instruction) (s : state) : step_result :=
  match nth_error code (Z.to_nat s.(pc)) with
  | None => Error "pc out of bounds"
  | Some instr =>
  let pc' := s.(pc) + 1 in
  match instr with

  | ACC n =>
    match nth_error s.(stack) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "ACC: stack underflow"
    end

  | PUSH =>
    Step (st s pc' s.(accu) (s.(accu) :: s.(stack)) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | PUSHACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error new_stack n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "PUSHACC: stack underflow"
    end

  | POP n =>
    Step (st s pc' s.(accu) (skipn n s.(stack)) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | ASSIGN n =>
    match set_nth s.(stack) n s.(accu) with
    | Some new_stack => Step (st s pc' val_unit new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "ASSIGN: stack underflow"
    end

  | ENVACC n =>
    match field_or_heap s s.(env) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "ENVACC: env access out of bounds"
    end

  | PUSHENVACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match field_or_heap s s.(env) n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "PUSHENVACC: env access out of bounds"
    end

  | PUSH_RETADDR ret_addr =>
    let frame := Val_int ret_addr :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    Step (st s pc' s.(accu) frame s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | APPLY n =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (st s target_pc s.(accu) s.(stack) s.(accu) (Nat.sub n 1) s.(global) s.(trap_stack))
    | None => Error "APPLY: accu is not a closure"
    end

  | APPLY1 =>
    match s.(stack) with
    | arg1 :: rest =>
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        let new_stack := arg1 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
        Step (st s target_pc s.(accu) new_stack s.(accu) 0 s.(global) s.(trap_stack))
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
        Step (st s target_pc s.(accu) new_stack s.(accu) 1 s.(global) s.(trap_stack))
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
        Step (st s target_pc s.(accu) new_stack s.(accu) 2 s.(global) s.(trap_stack))
      | None => Error "APPLY3: accu is not a closure"
      end
    | _ => Error "APPLY3: stack underflow"
    end

  | APPTERM nargs slotsize =>
    let args := firstn nargs s.(stack) in
    let base := skipn slotsize s.(stack) in
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (st s target_pc s.(accu) (args ++ base) s.(accu) (Nat.add s.(extra_args) (Nat.sub nargs 1)) s.(global) s.(trap_stack))
    | None => Error "APPTERM: accu is not a closure"
    end

  | APPTERM1 slotsize =>
    match s.(stack) with
    | arg1 :: _ =>
      let base := skipn slotsize s.(stack) in
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) (arg1 :: base) s.(accu) s.(extra_args) s.(global) s.(trap_stack))
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
        Step (st s target_pc s.(accu) (arg1 :: arg2 :: base) s.(accu) (Nat.add s.(extra_args) 1) s.(global) s.(trap_stack))
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
        Step (st s target_pc s.(accu) (arg1 :: arg2 :: arg3 :: base) s.(accu) (Nat.add s.(extra_args) 2) s.(global) s.(trap_stack))
      | None => Error "APPTERM3: accu is not a closure"
      end
    | _ => Error "APPTERM3: stack underflow"
    end

  | RETURN stacksize =>
    let stk := skipn stacksize s.(stack) in
    if Nat.ltb 0 s.(extra_args) then
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (st s target_pc s.(accu) stk s.(accu) (Nat.sub s.(extra_args) 1) s.(global) s.(trap_stack))
      | None => Error "RETURN: accu is not a closure"
      end
    else
      match stk with
      | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
        Step (st s ret_pc s.(accu) rest saved_env (Z.to_nat saved_ea) s.(global) s.(trap_stack))
      | _ => Error "RETURN: malformed return frame"
      end

  | RESTART =>
    (* Partial application closure: [code, closinfo, saved_env, arg1, arg2, ...] *)
    let restart_fields (all_fields : list value) (ofs : nat) : step_result :=
      let fields := skipn ofs all_fields in
      let num_args := Nat.sub (length fields) 3 in
      let args := skipn 3 fields in
      let new_stack := args ++ s.(stack) in
      match nth_error fields 2 with
      | Some saved_env =>
        Step (st s pc' s.(accu) new_stack saved_env (Nat.add s.(extra_args) num_args) s.(global) s.(trap_stack))
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

  | GRAB required =>
    (* GRAB n: if extra_args >= n, consume n and continue; else build partial application *)
    if Nat.leb required s.(extra_args) then
      Step (st s pc' s.(accu) s.(stack) s.(env) (Nat.sub s.(extra_args) required) s.(global) s.(trap_stack))
    else
      let num_args := S s.(extra_args) in
      let saved_args := firstn num_args s.(stack) in
      let rest_stack := skipn num_args s.(stack) in
      let closinfo := Val_int 0 in
      let fields := Val_int (s.(pc) - 1) :: closinfo :: s.(env) :: saved_args in
      let '(s', base_ptr) := heap_alloc s Closure_tag fields in
      let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
      let closure := Val_closure addr 0%nat in
      match rest_stack with
      | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
        Step (st s' ret_pc closure rest saved_env (Z.to_nat saved_ea) s.(global) s.(trap_stack))
      | _ => Error "GRAB: malformed return frame"
      end

  | CLOSURE nvars code_ofs =>
    let stk := if Nat.ltb 0 nvars then s.(accu) :: s.(stack) else s.(stack) in
    let vars := firstn nvars stk in
    let rest := skipn nvars stk in
    let closinfo := Val_int 0 in
    let fields := Val_int code_ofs :: closinfo :: vars in
    let '(s', base_ptr) := heap_alloc s Closure_tag fields in
    let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
    let closure := Val_closure addr 0%nat in
    Step (st s' pc' closure rest s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | CLOSUREREC nfuncs nvars code_offsets =>
    let stk := if Nat.ltb 0 nvars then s.(accu) :: s.(stack) else s.(stack) in
    let vars := firstn nvars stk in
    let rest := skipn nvars stk in
    match code_offsets with
    | [] => Error "CLOSUREREC: no code offsets"
    | _ =>
      (* Build flat closure block: [code0, closinfo0, infix, code1, closinfo1, infix, ..., env_vars]
         First closure at field 0; subsequent at field 3*i (with infix header before each).
         For nfuncs=1, no infix headers. *)
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
      (* Each closure i is at field offset 3*i (for i>0) or 0 (for i=0).
         Closure 0 = Val_closure(addr, 0), Closure 1 = Val_closure(addr, 3), etc. *)
      let closure_at (i : nat) : value :=
        if Nat.eqb i 0 then Val_closure addr 0%nat
        else Val_closure addr (3 * i) in
      (* Push closures: closure 0 pushed first (bottom), closure nfuncs-1 last (top).
         OCaml: *--sp = closure_0, then *--sp = closure_1, ..., *--sp = closure_{nf-1}.
         Result: sp[0] = closure_{nf-1}, sp[nf-1] = closure_0. *)
      let fix push_closures (i : nat) (stk : list value) : list value :=
        match i with
        | O => stk
        | S i' =>
          let stk' := push_closures i' stk in
          closure_at i' :: stk'
        end in
      let new_stack := push_closures nfuncs rest in
      Step (st s' pc' (closure_at 0%nat) new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    end

  | OFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      let clos := Val_closure addr new_ofs in
      Step (st s pc' clos s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (st s pc' s.(env) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
      else Error "OFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "OFFSETCLOSURE: invalid env"
    end

  | PUSHOFFSETCLOSURE ofs =>
    let new_stack := s.(accu) :: s.(stack) in
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      let clos := Val_closure addr new_ofs in
      Step (st s pc' clos new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (st s pc' s.(env) new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
      else Error "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "PUSHOFFSETCLOSURE: invalid env"
    end

  | GETGLOBAL n =>
    match nth_error s.(global) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "GETGLOBAL: index out of bounds"
    end

  | PUSHGETGLOBAL n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "PUSHGETGLOBAL: index out of bounds"
    end

  | GETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
      | None => Error "GETGLOBALFIELD: field access failed"
      end
    | None => Error "GETGLOBALFIELD: index out of bounds"
    end

  | PUSHGETGLOBALFIELD n p =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (st s pc' v new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))
      | None => Error "PUSHGETGLOBALFIELD: field access failed"
      end
    | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
    end

  | SETGLOBAL n =>
    let new_global := match set_nth s.(global) n s.(accu) with
                      | Some g => g | None => s.(global) end in
    Step (st s pc' val_unit s.(stack) s.(env) s.(extra_args) new_global s.(trap_stack))

  | ATOM t =>
    let '(s', ptr) := heap_alloc s t [] in
    Step (st s' pc' ptr s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | PUSHATOM t =>
    let new_stack := s.(accu) :: s.(stack) in
    let '(s', ptr) := heap_alloc s t [] in
    Step (st s' pc' ptr new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | MAKEBLOCK t size =>
    let fields := s.(accu) :: firstn (Nat.sub size 1) s.(stack) in
    let new_stack := skipn (Nat.sub size 1) s.(stack) in
    let '(s', ptr) := heap_alloc s t fields in
    Step (st s' pc' ptr new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | MAKEBLOCK1 t =>
    let '(s', ptr) := heap_alloc s t [s.(accu)] in
    Step (st s' pc' ptr s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | MAKEBLOCK2 t =>
    match s.(stack) with
    | v1 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
      Step (st s' pc' ptr rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "MAKEBLOCK2: stack underflow"
    end

  | MAKEBLOCK3 t =>
    match s.(stack) with
    | v1 :: v2 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1; v2] in
      Step (st s' pc' ptr rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "MAKEBLOCK3: stack underflow"
    end

  | MAKEFLOATBLOCK _ => Error "MAKEFLOATBLOCK: not supported"

  | GETFIELD n =>
    match field_or_heap s s.(accu) n with
    | Some v => Step (st s pc' v s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
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
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_stack) new_hp s.(next_addr))
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
    | Some n => Step (st s pc' (Val_int (Z.of_nat n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | None => Error "VECTLENGTH: not a block"
    end

  | GETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: rest =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some v => Step (st s pc' v rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
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
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_stack) new_hp s.(next_addr))
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
      | Some (Val_int c) => Step (st s pc' (Val_int c) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
      | _ => Error "GETSTRINGCHAR: index out of bounds"
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
            Step (mk_state pc' val_unit rest s.(env) s.(extra_args) s.(global) s.(trap_stack) new_hp s.(next_addr))
          | None => Error "SETBYTESCHAR: index out of bounds"
          end
        | None => Error "SETBYTESCHAR: dangling pointer"
        end
      | _ => Error "SETBYTESCHAR: not a heap bytes"
      end
    | _ => Error "SETBYTESCHAR: stack underflow"
    end

  | BRANCH target =>
    Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | BRANCHIF target =>
    match s.(accu) with
    | Val_int 0 => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    end

  | BRANCHIFNOT target =>
    match s.(accu) with
    | Val_int 0 => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    end

  | SWITCH _nc _nb const_targets block_targets =>
    match s.(accu) with
    | Val_int n =>
      match nth_error const_targets (Z.to_nat n) with
      | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
      | None => Error "SWITCH: constant index out of range"
      end
    | Val_block t _ =>
      match nth_error block_targets t with
      | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
      | None => Error "SWITCH: block tag out of range"
      end
    | Val_ptr addr | Val_closure addr _ =>
      match tag_or_heap s s.(accu) with
      | Some t =>
        match nth_error block_targets t with
        | Some target => Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
        | None => Error "SWITCH: block tag out of range"
        end
      | None => Error "SWITCH: dangling pointer"
      end
    end

  | BOOLNOT =>
    match s.(accu) with
    | Val_int 0 => Step (st s pc' val_true s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Step (st s pc' val_false s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    end

  | PUSHTRAP handler_pc =>
    (* PUSHTRAP pushes 4 values onto the stack: handler_pc, trap_link (0), env, extra_args *)
    let trap_frame := Val_int handler_pc :: Val_int 0 :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    let tf := mk_trap_frame handler_pc (length trap_frame) s.(env) s.(extra_args) in
    Step (st s pc' s.(accu) trap_frame s.(env) s.(extra_args) s.(global) (tf :: s.(trap_stack)))

  | POPTRAP =>
    match s.(trap_stack) with
    | _ :: rest =>
      (* POPTRAP pops the 4 trap frame values from the stack *)
      Step (st s pc' s.(accu) (skipn 4 s.(stack)) s.(env) s.(extra_args) s.(global) rest)
    | [] => Error "POPTRAP: no trap frame"
    end

  | RAISE | RERAISE | RAISE_NOTRACE =>
    match s.(trap_stack) with
    | tf :: rest =>
      let stack_depth := tf.(trap_sp_offset) in
      (* Restore stack to the depth at PUSHTRAP time (includes the 4 trap frame values) *)
      let restored := skipn (Nat.sub (length s.(stack)) stack_depth) s.(stack) in
      (* The trap frame values are at the top: [handler_pc, link, env, extra_args, ...] *)
      (* Pop the 4 trap frame values; restore env and extra_args from them *)
      match restored with
      | _ :: _ :: saved_env :: Val_int saved_ea :: real_stack =>
        Step (st s tf.(trap_pc) s.(accu) real_stack saved_env (Z.to_nat saved_ea) s.(global) rest)
      | _ =>
        (* Fallback: use trap frame info *)
        Step (st s tf.(trap_pc) s.(accu) (skipn 4 restored) tf.(trap_env) tf.(trap_extra_args) s.(global) rest)
      end
    | [] => Error "unhandled exception"
    end

  | CHECK_SIGNALS =>
    Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | C_CALL nargs prim_idx =>
    let args := s.(accu) :: firstn (Nat.sub nargs 1) s.(stack) in
    let new_stack := skipn (Nat.sub nargs 1) s.(stack) in
    let cont := st s pc' val_unit new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack) in
    CCall_request prim_idx args cont

  | CONSTINT n =>
    Step (st s pc' (Val_int n) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | PUSHCONSTINT n =>
    let new_stack := s.(accu) :: s.(stack) in
    Step (st s pc' (Val_int n) new_stack s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | NEGINT =>
    match s.(accu) with
    | Val_int n => Step (st s pc' (Val_int (- n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "NEGINT: not an integer"
    end

  | ADDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a + b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "ADDINT: type error or stack underflow"
    end

  | SUBINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a - b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "SUBINT: type error or stack underflow"
    end

  | MULINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (a * b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "MULINT: type error or stack underflow"
    end

  | DIVINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then Error "DIVINT: division by zero"
      else Step (st s pc' (Val_int (Z.quot a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "DIVINT: type error or stack underflow"
    end

  | MODINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then Error "MODINT: division by zero"
      else Step (st s pc' (Val_int (Z.rem a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "MODINT: type error or stack underflow"
    end

  | ANDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.land a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "ANDINT: type error or stack underflow"
    end

  | ORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.lor a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "ORINT: type error or stack underflow"
    end

  | XORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.lxor a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "XORINT: type error or stack underflow"
    end

  | LSLINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.shiftl a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "LSLINT: type error or stack underflow"
    end

  | LSRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (z_lsr a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "LSRINT: type error or stack underflow"
    end

  | ASRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (Val_int (Z.shiftr a b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "ASRINT: type error or stack underflow"
    end

  | EQ =>
    match s.(stack) with
    | b :: rest => Step (st s pc' (if value_eqb s.(accu) b then val_true else val_false) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "EQ: stack underflow"
    end

  | NEQ =>
    match s.(stack) with
    | b :: rest => Step (st s pc' (if value_eqb s.(accu) b then val_false else val_true) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "NEQ: stack underflow"
    end

  | LTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a <? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "LTINT: type error or stack underflow"
    end

  | LEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a <=? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "LEINT: type error or stack underflow"
    end

  | GTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a >? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "GTINT: type error or stack underflow"
    end

  | GEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (a >=? b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "GEINT: type error or stack underflow"
    end

  | OFFSETINT n =>
    match s.(accu) with
    | Val_int a => Step (st s pc' (Val_int (a + n)) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "OFFSETINT: not an integer"
    end

  | OFFSETREF n =>
    match s.(accu) with
    | Val_ptr addr =>
      match heap_lookup s.(hp) addr with
      | Some (_, Val_int old :: rest) =>
        let new_hp := heap_update s.(hp) addr (Val_int (old + n) :: rest) in
        Step (mk_state pc' val_unit s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack) new_hp s.(next_addr))
      | _ => Error "OFFSETREF: not a ref"
      end
    | _ => Error "OFFSETREF: not a ref"
    end

  | ISINT =>
    Step (st s pc' (if is_int s.(accu) then val_true else val_false) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

  | GETMETHOD => Error "GETMETHOD: OO not supported"
  | GETPUBMET _ => Error "GETPUBMET: OO not supported"
  | GETDYNMET => Error "GETDYNMET: OO not supported"

  | BEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BEQ: not an integer"
    end

  | BNEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BNEQ: not an integer"
    end

  (* B-comparison instructions: semantics is *pc++ CMP Long_val(accu),
     i.e., the OPERAND is on the LEFT and ACCU on the RIGHT. *)

  | BLTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BLTINT: not an integer"
    end

  | BLEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.leb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BLEINT: not an integer"
    end

  | BGTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.gtb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BGTINT: not an integer"
    end

  | BGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb n a then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BGEINT: not an integer"
    end

  | ULTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (z_unsigned a <? z_unsigned b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "ULTINT: type error or stack underflow"
    end

  | UGEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (st s pc' (val_bool (z_unsigned a >=? z_unsigned b)) rest s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _, _ => Error "UGEINT: type error or stack underflow"
    end

  | BULTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb (z_unsigned n) (z_unsigned a) then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BULTINT: not an integer"
    end

  | BUGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb (z_unsigned n) (z_unsigned a) then Step (st s target s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
                   else Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
    | _ => Error "BUGEINT: not an integer"
    end

  | STOP => Halt s.(accu)
  | EVENT => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))
  | BREAK => Step (st s pc' s.(accu) s.(stack) s.(env) s.(extra_args) s.(global) s.(trap_stack))

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
