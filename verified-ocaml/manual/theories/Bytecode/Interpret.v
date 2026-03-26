(* Interpret.v - [TRUSTED] OCaml bytecode interpreter.
   Core trusted component: step function + fuel-based run loop.
   Each case corresponds one-to-one to a case in OCaml's runtime/interp.c. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib.Array Require Import PrimArray.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From RecordUpdate Require Import RecordUpdate.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Local Notation nth_error := List.nth_error (only parsing).
Local Notation length := Datatypes.length (only parsing).
Local Notation skipn := List.skipn (only parsing).
Local Notation firstn := List.firstn (only parsing).

(* Fetch instruction from PrimArray-based code segment.
   Uses Uint63 index; returns None if out of bounds. *)
Definition fetch_instr (code : array instruction) (pc : Z) : option instruction :=
  let idx := Uint63.of_Z pc in
  if Uint63.ltb idx (PrimArray.length code) then
    Some (PrimArray.get code idx)
  else
    None.

(* Convert a list of instructions to a PrimArray.
   Uses STOP as the default element. *)
Definition list_to_code_array (l : list instruction) : array instruction :=
  let len := Uint63.of_Z (Z.of_nat (List.length l)) in
  let arr := PrimArray.make len STOP in
  (fix go (i : nat) (rest : list instruction) (a : array instruction) :=
    match rest with
    | [] => a
    | x :: xs => go (S i) xs (PrimArray.set a (Uint63.of_Z (Z.of_nat i)) x)
    end) 0%nat l arr.

(* OCaml int is 63-bit on 64-bit architectures. *)
Definition word_bits := 63.
Definition z_unsigned (a : Z) : Z := Z.land a (Z.ones word_bits).
Definition z_lsr (a b : Z) : Z := Z.shiftr (z_unsigned a) b.

(* XOR with 2^(word_bits-1) flips the sign bit, converting signed↔unsigned order.
   This works in both Rocq Z arithmetic and extracted OCaml int:
   in OCaml, (1 lsl 62) = min_int, and (a lxor min_int) gives the unsigned comparison trick.
   Used to implement BULTINT/BUGEINT/ULTINT/UGEINT with correct unsigned semantics. *)
Definition z_flip_sign (a : Z) : Z := Z.lxor a (Z.shiftl 1 (word_bits - 1)).

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
  | Val_ptr addr =>
    match heap_lookup s.(hp) addr with
    | Some (t, fields) =>
      if Nat.eqb t Closure_tag then
        match fields with Val_int pc :: _ => Some pc | _ => None end
      else None
    | None => None
    end
  | _ => None
  end.

(* Predefined exception values (tag=248, fields=[name_string, unique_id]).
   Ids match OCaml runtime: Division_by_zero=-6. *)
Definition make_exn_string (chars : list Z) : value :=
  Val_block 252 (List.map Val_int chars).

(* "Division_by_zero" ASCII codes *)
Definition div_by_zero_exn : value :=
  Val_block 248 [make_exn_string [68;105;118;105;115;105;111;110;95;98;121;95;122;101;114;111];
                 Val_int (-6)].

(* Perform the RAISE operation with a given exception value.
   Mirrors interp.c: sp = trap_sp; pc = handler_pc; env = env; extra_args = ea; sp+=4. *)
Definition do_raise (exn : value) (s : state) : step_result :=
  if Nat.eqb s.(trap_sp) 0 then Error "unhandled exception"
  else
    let k := Nat.sub (length s.(stack)) s.(trap_sp) in
    let frame_top := skipn k s.(stack) in
    match frame_top with
    | Val_int handler_pc :: Val_int prev_tsp :: saved_env :: Val_int saved_ea :: rest =>
      Step (s <|pc := handler_pc|> <|accu := exn|> <|stack := rest|> <|env := saved_env|>
              <|extra_args := Z.to_nat saved_ea|> <|trap_sp := Z.to_nat prev_tsp|>)
    | _ => Error "RAISE: malformed trap frame"
    end.

Definition step (code : array instruction) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | None => Error "pc out of bounds"
  | Some instr =>
  let pc' := s.(pc) + 1 in
  match instr with

  | ACC n =>
    match nth_error s.(stack) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "ACC: stack underflow"
    end

  | PUSH =>
    Step (s <|pc := pc'|> <|stack := s.(accu) :: s.(stack)|>)

  | PUSHACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error new_stack n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHACC: stack underflow"
    end

  | POP n =>
    Step (s <|pc := pc'|> <|stack := skipn n s.(stack)|>)

  | ASSIGN n =>
    match set_nth s.(stack) n s.(accu) with
    | Some new_stack => Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := new_stack|>)
    | None => Error "ASSIGN: stack underflow"
    end

  | ENVACC n =>
    match field_or_heap s s.(env) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "ENVACC: env access out of bounds"
    end

  | PUSHENVACC n =>
    let new_stack := s.(accu) :: s.(stack) in
    match field_or_heap s s.(env) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHENVACC: env access out of bounds"
    end

  (* PUSH_RETADDR: pushes [ret_addr, env, extra_args] onto the stack.
     In interp.c: sp[0]=pc+ofs, sp[1]=env, sp[2]=Long_val(extra_args). *)
  | PUSH_RETADDR ret_addr =>
    let frame := Val_int ret_addr :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    Step (s <|pc := pc'|> <|stack := frame|>)

  (* APPLY n: tail call with n args already on stack; sets extra_args = n-1. *)
  | APPLY n =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (s <|pc := target_pc|> <|env := s.(accu)|> <|extra_args := Nat.sub n 1|>)
    | None => Error "APPLY: accu is not a closure"
    end

  (* APPLY1/2/3: save return frame then call closure. *)
  | APPLY1 =>
    match s.(stack) with
    | arg1 :: rest =>
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        let new_stack := arg1 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
        Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 0%nat|>)
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
        Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 1%nat|>)
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
        Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 2%nat|>)
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
      Step (s <|pc := target_pc|> <|stack := args ++ base|> <|env := s.(accu)|>
              <|extra_args := Nat.add s.(extra_args) (Nat.sub nargs 1)|>)
    | None => Error "APPTERM: accu is not a closure"
    end

  | APPTERM1 slotsize =>
    match s.(stack) with
    | arg1 :: _ =>
      let base := skipn slotsize s.(stack) in
      match get_code_ptr_s s s.(accu) with
      | Some target_pc =>
        Step (s <|pc := target_pc|> <|stack := arg1 :: base|> <|env := s.(accu)|>)
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
        Step (s <|pc := target_pc|> <|stack := arg1 :: arg2 :: base|> <|env := s.(accu)|>
                <|extra_args := Nat.add s.(extra_args) 1|>)
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
        Step (s <|pc := target_pc|> <|stack := arg1 :: arg2 :: arg3 :: base|> <|env := s.(accu)|>
                <|extra_args := Nat.add s.(extra_args) 2|>)
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
        Step (s <|pc := target_pc|> <|stack := stk|> <|env := s.(accu)|>
                <|extra_args := Nat.sub s.(extra_args) 1|>)
      | None => Error "RETURN: accu is not a closure"
      end
    else
      match stk with
      | Val_int ret_pc :: saved_env :: Val_int saved_ea :: rest =>
        Step (s <|pc := ret_pc|> <|stack := rest|> <|env := saved_env|>
                <|extra_args := Z.to_nat saved_ea|>)
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
        Step (s <|pc := pc'|> <|stack := new_stack|> <|env := saved_env|>
                <|extra_args := Nat.add s.(extra_args) num_args|>)
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
      Step (s <|pc := pc'|> <|extra_args := Nat.sub s.(extra_args) required|>)
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
        Step (s' <|pc := ret_pc|> <|accu := closure|> <|stack := rest|> <|env := saved_env|>
                 <|extra_args := Z.to_nat saved_ea|>)
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
    Step (s' <|pc := pc'|> <|accu := closure|> <|stack := rest|>)

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
      Step (s' <|pc := pc'|> <|accu := closure_at 0%nat|> <|stack := new_stack|>)
    end

  (* OFFSETCLOSURE n: accu := env offset by n fields (within the same heap block). *)
  | OFFSETCLOSURE ofs =>
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      Step (s <|pc := pc'|> <|accu := Val_closure addr new_ofs|>)
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (s <|pc := pc'|> <|accu := s.(env)|>)
      else Error "OFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "OFFSETCLOSURE: invalid env"
    end

  | PUSHOFFSETCLOSURE ofs =>
    let new_stack := s.(accu) :: s.(stack) in
    match s.(env) with
    | Val_closure addr base_ofs =>
      let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
      Step (s <|pc := pc'|> <|accu := Val_closure addr new_ofs|> <|stack := new_stack|>)
    | Val_block t _ =>
      if Z.eqb ofs 0 then
        Step (s <|pc := pc'|> <|accu := s.(env)|> <|stack := new_stack|>)
      else Error "PUSHOFFSETCLOSURE: non-zero offset on non-closure env"
    | _ => Error "PUSHOFFSETCLOSURE: invalid env"
    end

  | GETGLOBAL n =>
    match nth_error s.(global) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETGLOBAL: index out of bounds"
    end

  | PUSHGETGLOBAL n =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHGETGLOBAL: index out of bounds"
    end

  | GETGLOBALFIELD n p =>
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (s <|pc := pc'|> <|accu := v|>)
      | None => Error "GETGLOBALFIELD: field access failed"
      end
    | None => Error "GETGLOBALFIELD: index out of bounds"
    end

  | PUSHGETGLOBALFIELD n p =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some glob =>
      match field_or_heap s glob p with
      | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
      | None => Error "PUSHGETGLOBALFIELD: field access failed"
      end
    | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
    end

  | SETGLOBAL n =>
    let new_global := match set_nth s.(global) n s.(accu) with
                      | Some g => g | None => s.(global) end in
    Step (s <|pc := pc'|> <|accu := val_unit|> <|global := new_global|>)

  | ATOM t =>
    let '(s', ptr) := heap_alloc s t [] in
    Step (s' <|pc := pc'|> <|accu := ptr|>)

  | PUSHATOM t =>
    let new_stack := s.(accu) :: s.(stack) in
    let '(s', ptr) := heap_alloc s t [] in
    Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := new_stack|>)

  (* MAKEBLOCK tag size: accu=field0, pop (size-1) from stack. *)
  | MAKEBLOCK t size =>
    let fields := s.(accu) :: firstn (Nat.sub size 1) s.(stack) in
    let new_stack := skipn (Nat.sub size 1) s.(stack) in
    let '(s', ptr) := heap_alloc s t fields in
    Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := new_stack|>)

  | MAKEBLOCK1 t =>
    let '(s', ptr) := heap_alloc s t [s.(accu)] in
    Step (s' <|pc := pc'|> <|accu := ptr|>)

  | MAKEBLOCK2 t =>
    match s.(stack) with
    | v1 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
      Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := rest|>)
    | _ => Error "MAKEBLOCK2: stack underflow"
    end

  | MAKEBLOCK3 t =>
    match s.(stack) with
    | v1 :: v2 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1; v2] in
      Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := rest|>)
    | _ => Error "MAKEBLOCK3: stack underflow"
    end

  (* MAKEFLOATBLOCK n: accu=field0, pop (n-1) from stack.
     Use tag 254 (double array) to hold float fields. *)
  | MAKEFLOATBLOCK n =>
    let fields := s.(accu) :: firstn (Nat.sub n 1) s.(stack) in
    let new_stack := skipn (Nat.sub n 1) s.(stack) in
    let '(s', ptr) := heap_alloc s 254 fields in
    Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := new_stack|>)

  | GETFIELD n =>
    match field_or_heap s s.(accu) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETFIELD: access failed"
    end

  (* GETFLOATFIELD n: accu is a float array (tag 254), get field n. *)
  | GETFLOATFIELD n =>
    match field_or_heap s s.(accu) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETFLOATFIELD: access failed"
    end

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
            Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := rest|> <|hp := new_hp|>)
          | None => Error "SETFIELD: index out of bounds"
          end
        | None => Error "SETFIELD: dangling pointer"
        end
      | _ => Error "SETFIELD: not a mutable block"
      end
    | _ => Error "SETFIELD: stack underflow"
    end

  (* SETFLOATFIELD n: accu is the float array (tag 254), sp[0] is the new float value. *)
  | SETFLOATFIELD n =>
    match s.(stack) with
    | newval :: rest =>
      match s.(accu) with
      | Val_ptr addr =>
        match heap_lookup s.(hp) addr with
        | Some (_, fields) =>
          match set_nth fields n newval with
          | Some new_fields =>
            let new_hp := heap_update s.(hp) addr new_fields in
            Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := rest|> <|hp := new_hp|>)
          | None => Error "SETFLOATFIELD: index out of bounds"
          end
        | None => Error "SETFLOATFIELD: dangling pointer"
        end
      | _ => Error "SETFLOATFIELD: not a heap float array"
      end
    | _ => Error "SETFLOATFIELD: stack underflow"
    end

  | VECTLENGTH =>
    match size_or_heap s s.(accu) with
    | Some n => Step (s <|pc := pc'|> <|accu := Val_int (Z.of_nat n)|>)
    | None => Error "VECTLENGTH: not a block"
    end

  | GETVECTITEM =>
    match s.(stack) with
    | Val_int idx :: rest =>
      match field_or_heap s s.(accu) (Z.to_nat idx) with
      | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := rest|>)
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
            Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := rest|> <|hp := new_hp|>)
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
      | Some (Val_int c) => Step (s <|pc := pc'|> <|accu := Val_int c|> <|stack := rest|>)
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
            Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := rest|> <|hp := new_hp|>)
          | None => Error "SETBYTESCHAR: index out of bounds"
          end
        | None => Error "SETBYTESCHAR: dangling pointer"
        end
      | _ => Error "SETBYTESCHAR: not a heap bytes"
      end
    | _ => Error "SETBYTESCHAR: stack underflow"
    end

  | BRANCH target =>
    Step (s <|pc := target|>)

  | BRANCHIF target =>
    match s.(accu) with
    | Val_int 0 => Step (s <|pc := pc'|>)
    | _ => Step (s <|pc := target|>)
    end

  | BRANCHIFNOT target =>
    match s.(accu) with
    | Val_int 0 => Step (s <|pc := target|>)
    | _ => Step (s <|pc := pc'|>)
    end

  | SWITCH _nc _nb const_targets block_targets =>
    match s.(accu) with
    | Val_int n =>
      match nth_error const_targets (Z.to_nat n) with
      | Some target => Step (s <|pc := target|>)
      | None => Error "SWITCH: constant index out of range"
      end
    | Val_block t _ =>
      match nth_error block_targets t with
      | Some target => Step (s <|pc := target|>)
      | None => Error "SWITCH: block tag out of range"
      end
    | Val_ptr addr | Val_closure addr _ =>
      match tag_or_heap s s.(accu) with
      | Some t =>
        match nth_error block_targets t with
        | Some target => Step (s <|pc := target|>)
        | None => Error "SWITCH: block tag out of range"
        end
      | None => Error "SWITCH: dangling pointer"
      end
    end

  | BOOLNOT =>
    match s.(accu) with
    | Val_int 0 => Step (s <|pc := pc'|> <|accu := val_true|>)
    | _ => Step (s <|pc := pc'|> <|accu := val_false|>)
    end

  (* PUSHTRAP: push trap frame [handler_pc, prev_trap_sp, env, extra_args] onto
     the stack, then set trap_sp = length(new_stack).
     Layout mirrors interp.c: sp[0]=handler_pc, sp[1]=trap_link, sp[2]=env, sp[3]=extra_args. *)
  | PUSHTRAP handler_pc =>
    let prev_tsp := Val_int (Z.of_nat s.(trap_sp)) in
    let new_stack := Val_int handler_pc :: prev_tsp :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
    let new_tsp := length new_stack in
    Step (s <|pc := pc'|> <|stack := new_stack|> <|trap_sp := new_tsp|>)

  (* POPTRAP: restore trap_sp from the trap link (sp[1]) and pop 4 values.
     For well-formed code the trap frame is always at the current stack top. *)
  | POPTRAP =>
    match s.(stack) with
    | _ :: Val_int prev_tsp :: _ :: _ :: rest =>
      Step (s <|pc := pc'|> <|stack := rest|> <|trap_sp := Z.to_nat prev_tsp|>)
    | _ => Error "POPTRAP: malformed trap frame"
    end

  (* RAISE/RERAISE/RAISE_NOTRACE: restore sp to the trap frame, extract
     handler_pc / prev_trap_sp / env / extra_args from the frame, and jump.
     In interp.c: sp = trapsp; pc = Trap_pc(sp); trapsp = sp+link; env=sp[2]; ea=sp[3]; sp+=4. *)
  | RAISE | RERAISE | RAISE_NOTRACE =>
    do_raise s.(accu) s

  | CHECK_SIGNALS =>
    Step (s <|pc := pc'|>)

  (* C_CALL: suspend and request a C primitive call. *)
  | C_CALL nargs prim_idx =>
    let args := s.(accu) :: firstn (Nat.sub nargs 1) s.(stack) in
    let new_stack := skipn (Nat.sub nargs 1) s.(stack) in
    let cont := s <|pc := pc'|> <|accu := val_unit|> <|stack := new_stack|> in
    CCall_request prim_idx args cont

  | CONSTINT n =>
    Step (s <|pc := pc'|> <|accu := Val_int n|>)

  | PUSHCONSTINT n =>
    let new_stack := s.(accu) :: s.(stack) in
    Step (s <|pc := pc'|> <|accu := Val_int n|> <|stack := new_stack|>)

  | NEGINT =>
    match s.(accu) with
    | Val_int n => Step (s <|pc := pc'|> <|accu := Val_int (- n)|>)
    | _ => Error "NEGINT: not an integer"
    end

  | ADDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a + b)|> <|stack := rest|>)
    | _, _ => Error "ADDINT: type error or stack underflow"
    end

  | SUBINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a - b)|> <|stack := rest|>)
    | _, _ => Error "SUBINT: type error or stack underflow"
    end

  | MULINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a * b)|> <|stack := rest|>)
    | _, _ => Error "MULINT: type error or stack underflow"
    end

  | DIVINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then do_raise div_by_zero_exn s
      else Step (s <|pc := pc'|> <|accu := Val_int (Z.quot a b)|> <|stack := rest|>)
    | _, _ => Error "DIVINT: type error or stack underflow"
    end

  | MODINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest =>
      if Z.eqb b 0 then do_raise div_by_zero_exn s
      else Step (s <|pc := pc'|> <|accu := Val_int (Z.rem a b)|> <|stack := rest|>)
    | _, _ => Error "MODINT: type error or stack underflow"
    end

  | ANDINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.land a b)|> <|stack := rest|>)
    | _, _ => Error "ANDINT: type error or stack underflow"
    end

  | ORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.lor a b)|> <|stack := rest|>)
    | _, _ => Error "ORINT: type error or stack underflow"
    end

  | XORINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.lxor a b)|> <|stack := rest|>)
    | _, _ => Error "XORINT: type error or stack underflow"
    end

  | LSLINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.shiftl a b)|> <|stack := rest|>)
    | _, _ => Error "LSLINT: type error or stack underflow"
    end

  | LSRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (z_lsr a b)|> <|stack := rest|>)
    | _, _ => Error "LSRINT: type error or stack underflow"
    end

  | ASRINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.shiftr a b)|> <|stack := rest|>)
    | _, _ => Error "ASRINT: type error or stack underflow"
    end

  | EQ =>
    match s.(stack) with
    | b :: rest => Step (s <|pc := pc'|> <|accu := if value_phys_eqb s.(accu) b then val_true else val_false|> <|stack := rest|>)
    | _ => Error "EQ: stack underflow"
    end

  | NEQ =>
    match s.(stack) with
    | b :: rest => Step (s <|pc := pc'|> <|accu := if value_phys_eqb s.(accu) b then val_false else val_true|> <|stack := rest|>)
    | _ => Error "NEQ: stack underflow"
    end

  | LTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a <? b)|> <|stack := rest|>)
    | _, _ => Error "LTINT: type error or stack underflow"
    end

  | LEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a <=? b)|> <|stack := rest|>)
    | _, _ => Error "LEINT: type error or stack underflow"
    end

  | GTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a >? b)|> <|stack := rest|>)
    | _, _ => Error "GTINT: type error or stack underflow"
    end

  | GEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a >=? b)|> <|stack := rest|>)
    | _, _ => Error "GEINT: type error or stack underflow"
    end

  | OFFSETINT n =>
    match s.(accu) with
    | Val_int a => Step (s <|pc := pc'|> <|accu := Val_int (a + n)|>)
    | _ => Error "OFFSETINT: not an integer"
    end

  | OFFSETREF n =>
    match s.(accu) with
    | Val_ptr addr =>
      match heap_lookup s.(hp) addr with
      | Some (_, Val_int old :: rest) =>
        let new_hp := heap_update s.(hp) addr (Val_int (old + n) :: rest) in
        Step (s <|pc := pc'|> <|accu := val_unit|> <|hp := new_hp|>)
      | _ => Error "OFFSETREF: not a ref"
      end
    | _ => Error "OFFSETREF: not a ref"
    end

  | ISINT =>
    Step (s <|pc := pc'|> <|accu := if is_int s.(accu) then val_true else val_false|>)

  (* GETMETHOD: accu is the method index, stack top is the object.
     Look up method at position accu in the object's class table. *)
  | GETMETHOD =>
    match s.(stack) with
    | obj :: _ =>
      match field_or_heap s obj 0 with
      | Some class_tbl =>
        match s.(accu) with
        | Val_int n =>
          match field_or_heap s class_tbl (Z.to_nat n) with
          | Some method_fn => Step (s <|pc := pc'|> <|accu := method_fn|>)
          | None => Error "GETMETHOD: method not found"
          end
        | _ => Error "GETMETHOD: not an integer index"
        end
      | None => Error "GETMETHOD: no class table"
      end
    | _ => Error "GETMETHOD: stack underflow"
    end

  (* OCaml class table layout (from caml_get_public_method):
     meths[0] = count (index of last+1 tag slot, always odd).
     meths[1] = padding (0).
     meths[2k]   = closure of method k (even indices >= 2).
     meths[2k+1] = tag    of method k (odd  indices >= 3).
     The method for tag T is found by scanning pairs (closure, tag) starting
     after the first two header words. *)
  | GETPUBMET tag =>
    let new_stack := s.(accu) :: s.(stack) in
    match field_or_heap s s.(accu) 0 with
    | Some class_tbl =>
      (* collect all fields of class_tbl *)
      let fields :=
        match class_tbl with
        | Val_block _ fs => fs
        | Val_ptr addr => match heap_lookup s.(hp) addr with Some (_, fs) => fs | None => [] end
        | _ => []
        end
      in
      (* Linear scan: skip meths[0] (count) and meths[1] (padding),
         then scan pairs (closure, tag). *)
      let fix scan (remaining : list value) : step_result :=
        match remaining with
        | [] => Error "GETPUBMET: method not found"
        | _ :: [] => Error "GETPUBMET: method not found"
        | method_fn :: tag_val :: rest =>
          if value_eqb tag_val (Val_int tag) then
            Step (s <|pc := pc'|> <|accu := method_fn|> <|stack := new_stack|>)
          else scan rest
        end
      in scan (skipn 2 fields)
    | None => Error "GETPUBMET: no class table"
    end

  (* GETDYNMET: accu is method tag (val), stack top is object. *)
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
        (* Linear scan: skip meths[0] (count) and meths[1] (padding),
           then scan pairs (closure, tag). *)
        let fix scan (remaining : list value) : step_result :=
          match remaining with
          | [] => Error "GETDYNMET: method not found"
          | _ :: [] => Error "GETDYNMET: method not found"
          | method_fn :: tag_val :: rest =>
            if value_eqb tag_val tag then
              Step (s <|pc := pc'|> <|accu := method_fn|>)
            else scan rest
          end
        in scan (skipn 2 fields)
      | None => Error "GETDYNMET: no class table"
      end
    | _ => Error "GETDYNMET: stack underflow"
    end

  (* B-comparison instructions: the spec says "increments pc by ofs-1 if val CMP accu".
     In interp.c the operand is an absolute instruction index (after decode). *)
  | BEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    (* Non-integer values are never equal to Val_int n, so don't branch *)
    | _ => Step (s <|pc := pc'|>)
    end

  | BNEQ n target =>
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (s <|pc := pc'|>)
                   else Step (s <|pc := target|>)
    (* Non-integer values are never equal to Val_int n, so always branch *)
    | _ => Step (s <|pc := target|>)
    end

  (* B-comparison instructions: semantics is *pc++ CMP Long_val(accu),
     i.e., the OPERAND is on the LEFT and ACCU on the RIGHT. *)

  | BLTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BLTINT: not an integer"
    end

  | BLEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.leb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BLEINT: not an integer"
    end

  | BGTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.gtb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BGTINT: not an integer"
    end

  | BGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BGEINT: not an integer"
    end

  | ULTINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (Z.ltb (z_flip_sign a) (z_flip_sign b))|> <|stack := rest|>)
    | _, _ => Error "ULTINT: type error or stack underflow"
    end

  | UGEINT =>
    match s.(accu), s.(stack) with
    | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (Z.geb (z_flip_sign a) (z_flip_sign b))|> <|stack := rest|>)
    | _, _ => Error "UGEINT: type error or stack underflow"
    end

  (* BULTINT(n, target): branch if n < accu (unsigned). "n is ULT the integer accu."
     BUGEINT(n, target): branch if n >= accu (unsigned). "n is UGE the integer accu."
     Like signed B-ops (which use n CMP accu), both use z_flip_sign for unsigned order. *)
  | BULTINT n target =>
    match s.(accu) with
    | Val_int a => if Z.ltb (z_flip_sign n) (z_flip_sign a) then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BULTINT: not an integer"
    end

  | BUGEINT n target =>
    match s.(accu) with
    | Val_int a => if Z.geb (z_flip_sign n) (z_flip_sign a) then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BUGEINT: not an integer"
    end

  | STOP => Halt s.(accu)
  | EVENT => Step (s <|pc := pc'|>)
  | BREAK => Step (s <|pc := pc'|>)

  | PERFORM => Error "PERFORM: effects not supported"
  | RESUME => Error "RESUME: effects not supported"
  | RESUMETERM _ => Error "RESUMETERM: effects not supported"
  | REPERFORMTERM _ => Error "REPERFORMTERM: effects not supported"

  end
  end.

(* Monadic run loop: produces a bcmicro tree.
   Each C-call becomes a MVis node whose continuation resumes execution. *)
Fixpoint run_micro (fuel : nat) (code : array instruction) (s : state) : bcmicro :=
  match fuel with
  | O => MFuel s
  | S fuel' =>
    match step code s with
    | Step s' => run_micro fuel' code s'
    | Halt v => MRet v
    | Error msg => MErr msg
    | CCall_request prim_idx args cont =>
      MVis prim_idx args (fun result =>
        match result with
        | Some v => run_micro fuel' code (cont <|accu := v|>)
        | None => MErr "C call returned None"
        end)
    end
  end.

(* Handler: collapses a bcmicro tree into a run_result by supplying C-call responses.
   Needs its own fuel because Coq cannot see termination through function application. *)
Fixpoint handle_bcmicro (fuel : nat) (t : bcmicro)
  (h : nat -> list value -> option value) : run_result :=
  match fuel with
  | O => match t with
         | MFuel s => Out_of_fuel s
         | _ => Run_error "handler fuel exhausted"
         end
  | S fuel' =>
    match t with
    | MRet v => Finished v
    | MErr msg => Run_error msg
    | MFuel s => Out_of_fuel s
    | MVis idx args k => handle_bcmicro fuel' (k (h idx args)) h
    end
  end.

(* Backward-compatible run: produce tree then collapse with handler. *)
Definition run (fuel : nat) (code : array instruction) (s : state)
  (handle_ccall : nat -> list value -> option value) : run_result :=
  handle_bcmicro fuel (run_micro fuel code s) handle_ccall.

Definition run_pure (fuel : nat) (code : array instruction) (global_data : list value) : run_result :=
  run fuel code (initial_state global_data) (fun _ _ => None).
