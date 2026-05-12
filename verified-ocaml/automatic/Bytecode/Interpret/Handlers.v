(* Handlers.v - [UNTRUSTED] Per-instruction handlers of the OCaml bytecode
   interpreter plus the helpers they depend on.  Each handler corresponds
   one-to-one to a case in OCaml's runtime/interp.c.

   The top-level instruction dispatcher that routes an instruction to the
   right handler lives in automatic/Bytecode/Interpret/Dispatch.v; the
   step/run composition layer that consumes that dispatcher lives in
   manual/Bytecode/Interpret/Run.v as a functor. *)

From Stdlib Require Import ZArith Bool PeanoNat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From compcert Require Import Integers.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Export Helpers.
From RecordUpdate Require Import RecordUpdate.
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

(* XOR with 2^(word_bits-1) flips the sign bit, converting signed↔unsigned order.
   This works in both Rocq Z arithmetic and extracted OCaml int:
   in OCaml, (1 lsl 62) = min_int, and (a lxor min_int) gives the unsigned comparison trick.
   Used to implement BULTINT/BUGEINT/ULTINT/UGEINT with correct unsigned semantics. *)
Definition z_flip_sign (a : Z) : Z := Z.lxor a (Z.shiftl 1 (word_bits - 1)).

(* Predefined exception values (tag=248, fields=[name_string, unique_id]).
   Ids match OCaml runtime: Division_by_zero=-6. *)
Definition make_exn_string (chars : list Z) : value :=
  Val_block 252 (List.map Val_int chars).

Definition list_Z_of_string (s : string) : list Z :=
  List.map Z.of_N (List.map Ascii.N_of_ascii (list_ascii_of_string s)).
Definition div_by_zero_list_Z := Eval cbv in list_Z_of_string "Division_by_zero".
Definition div_by_zero_exn : value :=
  Val_block 248 [make_exn_string div_by_zero_list_Z; Val_int (-6)].

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

(* ------------------------------------------------------------------ *)
(* Per-instruction handler functions                                    *)
(* ------------------------------------------------------------------ *)

Definition handle_ACC (n : nat) (pc' : Z) (s : state) : step_result :=
  if (Z.of_nat n <? Int.half_modulus)%Z then
    match nth_error s.(stack) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "ACC: stack underflow"
    end
  else
    Error "ACC: malformed operand".

Definition handle_PUSH (pc' : Z) (s : state) : step_result :=
  Step (s <|pc := pc'|> <|stack := s.(accu) :: s.(stack)|>).

Definition handle_PUSHACC (n : nat) (pc' : Z) (s : state) : step_result :=
  match n with
  | 1%nat | 2%nat | 3%nat | 4%nat | 5%nat | 6%nat | 7%nat =>
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error new_stack n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHACC: stack underflow"
    end
  | _ => Error "PUSHACC: malformed operand"
  end.

Definition handle_POP (n : nat) (pc' : Z) (s : state) : step_result :=
  if (Z.of_nat n <? Int.half_modulus)%Z then
    Step (s <|pc := pc'|> <|stack := skipn n s.(stack)|>)
  else
    Error "POP: malformed operand".

Definition handle_ASSIGN (n : nat) (pc' : Z) (s : state) : step_result :=
  match set_nth s.(stack) n s.(accu) with
  | Some new_stack => Step (s <|pc := pc'|> <|accu := val_unit|> <|stack := new_stack|>)
  | None => Error "ASSIGN: stack underflow"
  end.

Definition handle_ENVACC (n : nat) (pc' : Z) (s : state) : step_result :=
  if (Z.of_nat n <? Int.half_modulus)%Z then
    match field_or_heap s s.(env) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "ENVACC: env access out of bounds"
    end
  else
    Error "ENVACC: malformed operand".

Definition handle_PUSHENVACC (n : nat) (pc' : Z) (s : state) : step_result :=
  let new_stack := s.(accu) :: s.(stack) in
  match field_or_heap s s.(env) n with
  | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
  | None => Error "PUSHENVACC: env access out of bounds"
  end.

(* PUSH_RETADDR: pushes [ret_addr, env, extra_args] onto the stack.
   In interp.c: sp[0]=pc+ofs, sp[1]=env, sp[2]=Long_val(extra_args). *)
Definition handle_PUSH_RETADDR (ret_addr : Z) (pc' : Z) (s : state) : step_result :=
  let frame := Val_int ret_addr :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
  Step (s <|pc := pc'|> <|stack := frame|>).

(* APPLY n: tail call with n args already on stack; sets extra_args = n-1. *)
Definition handle_APPLY (n : nat) (s : state) : step_result :=
  match get_code_ptr_s s s.(accu) with
  | Some target_pc =>
    Step (s <|pc := target_pc|> <|env := s.(accu)|> <|extra_args := Nat.sub n 1|>)
  | None => Error "APPLY: accu is not a closure"
  end.

(* APPLY1/2/3: save return frame then call closure. *)
Definition handle_APPLY1 (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | arg1 :: rest =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      let new_stack := arg1 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
      Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 0%nat|>)
    | None => Error "APPLY1: accu is not a closure"
    end
  | _ => Error "APPLY1: stack underflow"
  end.

Definition handle_APPLY2 (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | arg1 :: arg2 :: rest =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      let new_stack := arg1 :: arg2 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
      Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 1%nat|>)
    | None => Error "APPLY2: accu is not a closure"
    end
  | _ => Error "APPLY2: stack underflow"
  end.

Definition handle_APPLY3 (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | arg1 :: arg2 :: arg3 :: rest =>
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      let new_stack := arg1 :: arg2 :: arg3 :: Val_int pc' :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: rest in
      Step (s <|pc := target_pc|> <|stack := new_stack|> <|env := s.(accu)|> <|extra_args := 2%nat|>)
    | None => Error "APPLY3: accu is not a closure"
    end
  | _ => Error "APPLY3: stack underflow"
  end.

(* APPTERM n s: slide top n args down by (slotsize - n), tail call. *)
Definition handle_APPTERM (nargs slotsize : nat) (s : state) : step_result :=
  let args := firstn nargs s.(stack) in
  let base := skipn slotsize s.(stack) in
  match get_code_ptr_s s s.(accu) with
  | Some target_pc =>
    Step (s <|pc := target_pc|> <|stack := args ++ base|> <|env := s.(accu)|>
            <|extra_args := Nat.add s.(extra_args) (Nat.sub nargs 1)|>)
  | None => Error "APPTERM: accu is not a closure"
  end.

Definition handle_APPTERM1 (slotsize : nat) (s : state) : step_result :=
  match s.(stack) with
  | arg1 :: _ =>
    let base := skipn slotsize s.(stack) in
    match get_code_ptr_s s s.(accu) with
    | Some target_pc =>
      Step (s <|pc := target_pc|> <|stack := arg1 :: base|> <|env := s.(accu)|>)
    | None => Error "APPTERM1: accu is not a closure"
    end
  | _ => Error "APPTERM1: stack underflow"
  end.

Definition handle_APPTERM2 (slotsize : nat) (s : state) : step_result :=
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
  end.

Definition handle_APPTERM3 (slotsize : nat) (s : state) : step_result :=
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
  end.

(* RETURN n: pop n locals; if extra_args > 0 tail-call accu, else restore return frame. *)
Definition handle_RETURN (stacksize : nat) (s : state) : step_result :=
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
    end.

(* RESTART: restore args from partial application closure in env. *)
Definition handle_RESTART (pc' : Z) (s : state) : step_result :=
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
  end.

(* GRAB n: if extra_args >= n, consume n and continue;
   else build partial application closure and return to caller. *)
Definition handle_GRAB (required : nat) (pc' : Z) (s : state) : step_result :=
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
    end.

(* CLOSURE n ofs: build closure of n+1 fields [code, closinfo, v0, ..., vn-1].
   If n > 0 the accumulator is pushed first (it becomes v0). *)
Definition handle_CLOSURE (nvars : nat) (code_ofs : Z) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat (2 + nvars)) && (Z.of_nat (2 + nvars) <=? Int.max_signed) &&
      (Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z then
    let stk := if Nat.ltb 0 nvars then s.(accu) :: s.(stack) else s.(stack) in
    let vars := firstn nvars stk in
    let rest := skipn nvars stk in
    let closinfo := Val_int 0 in
    let fields := Val_int code_ofs :: closinfo :: vars in
    let '(s', base_ptr) := heap_alloc s Closure_tag fields in
    let addr := match base_ptr with Val_ptr a => a | _ => 0%nat end in
    let closure := Val_closure addr 0%nat in
    Step (s' <|pc := pc'|> <|accu := closure|> <|stack := rest|>)
  else
    Error "CLOSURE: malformed operand".

(* CLOSUREREC nf nv [ofs0;ofs1;...]: build flat closure block of
   (nf*3-1+nv) fields.  Layout: [code0,ci0, infix,code1,ci1, ..., v0,v1,...]
   Each closure_i is pushed as Val_closure(addr, 3*i). *)
Definition handle_CLOSUREREC (nfuncs nvars : nat) (code_offsets : list Z) (pc' : Z) (s : state) : step_result :=
  let wf :=
    match nfuncs, code_offsets with
    | 1%nat, (code_ofs :: nil)%list =>
        ((Int.min_signed <=? code_ofs) && (code_ofs <=? Int.max_signed))%Z
    | _, _ => false
    end in
  if wf then
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
  else
    Error "CLOSUREREC: malformed operand".

(* OFFSETCLOSURE n: accu := env offset by n fields (within the same heap block). *)
Definition handle_OFFSETCLOSURE (ofs : Z) (pc' : Z) (s : state) : step_result :=
  match s.(env) with
  | Val_closure addr base_ofs =>
    let new_ofs := Z.to_nat (Z.of_nat base_ofs + ofs) in
    Step (s <|pc := pc'|> <|accu := Val_closure addr new_ofs|>)
  | Val_block t _ =>
    if Z.eqb ofs 0 then
      Step (s <|pc := pc'|> <|accu := s.(env)|>)
    else Error "OFFSETCLOSURE: non-zero offset on non-closure env"
  | _ => Error "OFFSETCLOSURE: invalid env"
  end.

Definition handle_PUSHOFFSETCLOSURE (ofs : Z) (pc' : Z) (s : state) : step_result :=
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
  end.

Definition handle_GETGLOBAL (n : nat) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
    match nth_error s.(global) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETGLOBAL: index out of bounds"
    end
  else
    Error "GETGLOBAL: malformed operand".

Definition handle_PUSHGETGLOBAL (n : nat) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
    let new_stack := s.(accu) :: s.(stack) in
    match nth_error s.(global) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHGETGLOBAL: index out of bounds"
    end
  else
    Error "PUSHGETGLOBAL: malformed operand".

Definition handle_GETGLOBALFIELD (n p : nat) (pc' : Z) (s : state) : step_result :=
  match nth_error s.(global) n with
  | Some glob =>
    match field_or_heap s glob p with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETGLOBALFIELD: field access failed"
    end
  | None => Error "GETGLOBALFIELD: index out of bounds"
  end.

Definition handle_PUSHGETGLOBALFIELD (n p : nat) (pc' : Z) (s : state) : step_result :=
  let new_stack := s.(accu) :: s.(stack) in
  match nth_error s.(global) n with
  | Some glob =>
    match field_or_heap s glob p with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := new_stack|>)
    | None => Error "PUSHGETGLOBALFIELD: field access failed"
    end
  | None => Error "PUSHGETGLOBALFIELD: index out of bounds"
  end.

Definition handle_SETGLOBAL (n : nat) (pc' : Z) (s : state) : step_result :=
  let new_global := match set_nth s.(global) n s.(accu) with
                    | Some g => g | None => s.(global) end in
  Step (s <|pc := pc'|> <|accu := val_unit|> <|global := new_global|>).

(* Atoms are empty blocks (tag, []) represented as tagged integers —
   no heap allocation needed. *)
Definition handle_ATOM0 (pc' : Z) (s : state) : step_result :=
  Step (s <|accu := Val_block 0 []|>).

Definition handle_ATOM (t : nat) (pc' : Z) (s : state) : step_result :=
  if (Z.of_nat t <=? 2097151)%Z then
    Step (s <|pc := pc'|> <|accu := Val_block t []|>)
  else
    Error "ATOM: malformed operand".

Definition handle_PUSHATOM0 (pc' : Z) (s : state) : step_result :=
  Step (s <|accu := Val_block 0 []|> <|stack := s.(accu) :: s.(stack)|>).

Definition handle_PUSHATOM (t : nat) (pc' : Z) (s : state) : step_result :=
  if (Z.of_nat t <=? 2097151)%Z then
    Step (s <|pc := pc'|> <|accu := Val_block t []|> <|stack := s.(accu) :: s.(stack)|>)
  else
    Error "PUSHATOM: malformed operand".

(* MAKEBLOCK tag size: accu=field0, pop (size-1) from stack. *)
Definition handle_MAKEBLOCK (t size : nat) (pc' : Z) (s : state) : step_result :=
  if (1 <=? size)%nat then
    let fields := s.(accu) :: firstn (Nat.sub size 1) s.(stack) in
    let new_stack := skipn (Nat.sub size 1) s.(stack) in
    let '(s', ptr) := heap_alloc s t fields in
    Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := new_stack|>)
  else
    Error "MAKEBLOCK: malformed operand".

Definition handle_MAKEBLOCK1 (t : nat) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then
    let '(s', ptr) := heap_alloc s t [s.(accu)] in
    Step (s' <|pc := pc'|> <|accu := ptr|>)
  else
    Error "MAKEBLOCK1: malformed operand".

Definition handle_MAKEBLOCK2 (t : nat) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then
    match s.(stack) with
    | v1 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1] in
      Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := rest|>)
    | _ => Error "MAKEBLOCK2: stack underflow"
    end
  else
    Error "MAKEBLOCK2: malformed operand".

Definition handle_MAKEBLOCK3 (t : nat) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? Z.of_nat t) && (Z.of_nat t <=? 255))%Z then
    match s.(stack) with
    | v1 :: v2 :: rest =>
      let '(s', ptr) := heap_alloc s t [s.(accu); v1; v2] in
      Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := rest|>)
    | _ => Error "MAKEBLOCK3: stack underflow"
    end
  else
    Error "MAKEBLOCK3: malformed operand".

(* MAKEFLOATBLOCK n: accu=field0, pop (n-1) from stack.
   Use tag 254 (double array) to hold float fields. *)
Definition handle_MAKEFLOATBLOCK (n : nat) (pc' : Z) (s : state) : step_result :=
  if (1 <=? n)%nat then
    let fields := s.(accu) :: firstn (Nat.sub n 1) s.(stack) in
    let new_stack := skipn (Nat.sub n 1) s.(stack) in
    let '(s', ptr) := heap_alloc s 254 fields in
    Step (s' <|pc := pc'|> <|accu := ptr|> <|stack := new_stack|>)
  else
    Error "MAKEFLOATBLOCK: malformed operand".

Definition handle_GETFIELD (n : nat) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? Z.of_nat n) && (Z.of_nat n <=? Int.max_signed))%Z then
    match field_or_heap s s.(accu) n with
    | Some v => Step (s <|pc := pc'|> <|accu := v|>)
    | None => Error "GETFIELD: access failed"
    end
  else
    Error "GETFIELD: malformed operand".

(* GETFLOATFIELD n: accu is a float array (tag 254), get field n. *)
Definition handle_GETFLOATFIELD (n : nat) (pc' : Z) (s : state) : step_result :=
  match field_or_heap s s.(accu) n with
  | Some v => Step (s <|pc := pc'|> <|accu := v|>)
  | None => Error "GETFLOATFIELD: access failed"
  end.

Definition handle_SETFIELD (n : nat) (pc' : Z) (s : state) : step_result :=
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
  end.

(* SETFLOATFIELD n: accu is the float array (tag 254), sp[0] is the new float value. *)
Definition handle_SETFLOATFIELD (n : nat) (pc' : Z) (s : state) : step_result :=
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
  end.

Definition handle_VECTLENGTH (pc' : Z) (s : state) : step_result :=
  match size_or_heap s s.(accu) with
  | Some n => Step (s <|pc := pc'|> <|accu := Val_int (Z.of_nat n)|>)
  | None => Error "VECTLENGTH: not a block"
  end.

Definition handle_GETVECTITEM (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | Val_int idx :: rest =>
    match field_or_heap s s.(accu) (Z.to_nat idx) with
    | Some v => Step (s <|pc := pc'|> <|accu := v|> <|stack := rest|>)
    | None => Error "GETVECTITEM: index out of bounds"
    end
  | _ => Error "GETVECTITEM: bad index or stack underflow"
  end.

Definition handle_SETVECTITEM (pc' : Z) (s : state) : step_result :=
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
  end.

Definition handle_GETSTRINGCHAR (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | Val_int idx :: rest =>
    match field_or_heap s s.(accu) (Z.to_nat idx) with
    | Some (Val_int c) => Step (s <|pc := pc'|> <|accu := Val_int c|> <|stack := rest|>)
    | _ => Error "GETSTRINGCHAR: index out of bounds or not a char"
    end
  | _ => Error "GETSTRINGCHAR: stack underflow"
  end.

Definition handle_SETBYTESCHAR (pc' : Z) (s : state) : step_result :=
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
  end.

Definition handle_BRANCH (target : Z) (s : state) : step_result :=
  Step (s <|pc := target|>).

Definition handle_BRANCHIF (target : Z) (pc' : Z) (s : state) : step_result :=
  match s.(accu) with
  | Val_int 0 => Step (s <|pc := pc'|>)
  | _ => Step (s <|pc := target|>)
  end.

Definition handle_BRANCHIFNOT (target : Z) (pc' : Z) (s : state) : step_result :=
  match s.(accu) with
  | Val_int 0 => Step (s <|pc := target|>)
  | _ => Step (s <|pc := pc'|>)
  end.

Definition handle_SWITCH (_nc _nb : nat) (const_targets block_targets : list Z) (s : state) : step_result :=
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
  end.

Definition handle_BOOLNOT (pc' : Z) (s : state) : step_result :=
  match s.(accu) with
  | Val_int 0 => Step (s <|pc := pc'|> <|accu := val_true|>)
  | _ => Step (s <|pc := pc'|> <|accu := val_false|>)
  end.

(* PUSHTRAP: push trap frame [handler_pc, prev_trap_sp, env, extra_args] onto
   the stack, then set trap_sp = length(new_stack).
   Layout mirrors interp.c: sp[0]=handler_pc, sp[1]=trap_link, sp[2]=env, sp[3]=extra_args. *)
Definition handle_PUSHTRAP (handler_pc : Z) (pc' : Z) (s : state) : step_result :=
  let prev_tsp := Val_int (Z.of_nat s.(trap_sp)) in
  let new_stack := Val_int handler_pc :: prev_tsp :: s.(env) :: Val_int (Z.of_nat s.(extra_args)) :: s.(stack) in
  let new_tsp := length new_stack in
  Step (s <|pc := pc'|> <|stack := new_stack|> <|trap_sp := new_tsp|>).

(* POPTRAP: restore trap_sp from the trap link (sp[1]) and pop 4 values.
   For well-formed code the trap frame is always at the current stack top. *)
Definition handle_POPTRAP (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | _ :: Val_int prev_tsp :: _ :: _ :: rest =>
    Step (s <|pc := pc'|> <|stack := rest|> <|trap_sp := Z.to_nat prev_tsp|>)
  | _ => Error "POPTRAP: malformed trap frame"
  end.

Definition handle_CHECK_SIGNALS (pc' : Z) (s : state) : step_result :=
  Step (s <|pc := pc'|>).

(* C_CALL: suspend and request a C primitive call. *)
Definition handle_C_CALL (nargs : nat) (prim_idx : nat) (pc' : Z) (s : state) : step_result :=
  let args := s.(accu) :: firstn (Nat.sub nargs 1) s.(stack) in
  let new_stack := skipn (Nat.sub nargs 1) s.(stack) in
  let cont := s <|pc := pc'|> <|accu := val_unit|> <|stack := new_stack|> in
  CCall_request prim_idx args cont.

Definition handle_CONSTINT (n : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    Step (s <|pc := pc'|> <|accu := Val_int n|>)
  else
    Error "CONSTINT: malformed operand".

Definition handle_PUSHCONSTINT (n : Z) (pc' : Z) (s : state) : step_result :=
  let new_stack := s.(accu) :: s.(stack) in
  Step (s <|pc := pc'|> <|accu := Val_int n|> <|stack := new_stack|>).

Definition handle_NEGINT (pc' : Z) (s : state) : step_result :=
  match s.(accu) with
  | Val_int n => Step (s <|pc := pc'|> <|accu := Val_int (- n)|>)
  | _ => Error "NEGINT: not an integer"
  end.

Definition handle_ADDINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a + b)|> <|stack := rest|>)
  | _, _ => Error "ADDINT: type error or stack underflow"
  end.

Definition handle_SUBINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a - b)|> <|stack := rest|>)
  | _, _ => Error "SUBINT: type error or stack underflow"
  end.

Definition handle_MULINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (a * b)|> <|stack := rest|>)
  | _, _ => Error "MULINT: type error or stack underflow"
  end.

Definition handle_DIVINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest =>
    if Z.eqb b 0 then do_raise div_by_zero_exn s
    else Step (s <|pc := pc'|> <|accu := Val_int (Z.quot a b)|> <|stack := rest|>)
  | _, _ => Error "DIVINT: type error or stack underflow"
  end.

Definition handle_MODINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest =>
    if Z.eqb b 0 then do_raise div_by_zero_exn s
    else Step (s <|pc := pc'|> <|accu := Val_int (Z.rem a b)|> <|stack := rest|>)
  | _, _ => Error "MODINT: type error or stack underflow"
  end.

Definition handle_ANDINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.land a b)|> <|stack := rest|>)
  | _, _ => Error "ANDINT: type error or stack underflow"
  end.

Definition handle_ORINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.lor a b)|> <|stack := rest|>)
  | _, _ => Error "ORINT: type error or stack underflow"
  end.

Definition handle_XORINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.lxor a b)|> <|stack := rest|>)
  | _, _ => Error "XORINT: type error or stack underflow"
  end.

Definition handle_LSLINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.shiftl a b)|> <|stack := rest|>)
  | _, _ => Error "LSLINT: type error or stack underflow"
  end.

Definition handle_LSRINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (z_lsr a b)|> <|stack := rest|>)
  | _, _ => Error "LSRINT: type error or stack underflow"
  end.

Definition handle_ASRINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := Val_int (Z.shiftr a b)|> <|stack := rest|>)
  | _, _ => Error "ASRINT: type error or stack underflow"
  end.

Definition handle_EQ (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | b :: rest => Step (s <|pc := pc'|> <|accu := if value_phys_eqb s.(accu) b then val_true else val_false|> <|stack := rest|>)
  | _ => Error "EQ: stack underflow"
  end.

Definition handle_NEQ (pc' : Z) (s : state) : step_result :=
  match s.(stack) with
  | b :: rest => Step (s <|pc := pc'|> <|accu := if value_phys_eqb s.(accu) b then val_false else val_true|> <|stack := rest|>)
  | _ => Error "NEQ: stack underflow"
  end.

Definition handle_LTINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a <? b)|> <|stack := rest|>)
  | _, _ => Error "LTINT: type error or stack underflow"
  end.

Definition handle_LEINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a <=? b)|> <|stack := rest|>)
  | _, _ => Error "LEINT: type error or stack underflow"
  end.

Definition handle_GTINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a >? b)|> <|stack := rest|>)
  | _, _ => Error "GTINT: type error or stack underflow"
  end.

Definition handle_GEINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (a >=? b)|> <|stack := rest|>)
  | _, _ => Error "GEINT: type error or stack underflow"
  end.

Definition handle_OFFSETINT (n : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n * 2) && (n * 2 <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => Step (s <|pc := pc'|> <|accu := Val_int (a + n)|>)
    | _ => Error "OFFSETINT: not an integer"
    end
  else
    Error "OFFSETINT: malformed operand".

Definition handle_OFFSETREF (n : Z) (pc' : Z) (s : state) : step_result :=
  match s.(accu) with
  | Val_ptr addr =>
    match heap_lookup s.(hp) addr with
    | Some (_, Val_int old :: rest) =>
      let new_hp := heap_update s.(hp) addr (Val_int (old + n) :: rest) in
      Step (s <|pc := pc'|> <|accu := val_unit|> <|hp := new_hp|>)
    | _ => Error "OFFSETREF: not a ref"
    end
  | _ => Error "OFFSETREF: not a ref"
  end.

Definition handle_ISINT (pc' : Z) (s : state) : step_result :=
  Step (s <|pc := pc'|> <|accu := if is_int s.(accu) then val_true else val_false|>).

(* GETMETHOD: accu is the method index, stack top is the object.
   Look up method at position accu in the object's class table. *)
Definition handle_GETMETHOD (pc' : Z) (s : state) : step_result :=
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
  end.

(* OCaml class table layout (from caml_get_public_method):
   meths[0] = count (index of last+1 tag slot, always odd).
   meths[1] = padding (0).
   meths[2k]   = closure of method k (even indices >= 2).
   meths[2k+1] = tag    of method k (odd  indices >= 3).
   The method for tag T is found by scanning pairs (closure, tag) starting
   after the first two header words. *)
Definition handle_GETPUBMET (tag : Z) (pc' : Z) (s : state) : step_result :=
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
  end.

(* GETDYNMET: accu is method tag (val), stack top is object. *)
Definition handle_GETDYNMET (pc' : Z) (s : state) : step_result :=
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
  end.

(* B-comparison instructions: the spec says "increments pc by ofs-1 if val CMP accu".
   In interp.c the operand is an absolute instruction index (after decode). *)
Definition handle_BEQ (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    (* Non-integer values are never equal to Val_int n, so don't branch *)
    | _ => Step (s <|pc := pc'|>)
    end
  else
    Error "BEQ: malformed operand".

Definition handle_BNEQ (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.eqb a n then Step (s <|pc := pc'|>)
                   else Step (s <|pc := target|>)
    (* Non-integer values are never equal to Val_int n, so always branch *)
    | _ => Step (s <|pc := target|>)
    end
  else
    Error "BNEQ: malformed operand".

(* B-comparison instructions: semantics is *pc++ CMP Long_val(accu),
   i.e., the OPERAND is on the LEFT and ACCU on the RIGHT. *)

Definition handle_BLTINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.ltb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BLTINT: not an integer"
    end
  else
    Error "BLTINT: malformed operand".

Definition handle_BLEINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.leb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BLEINT: not an integer"
    end
  else
    Error "BLEINT: malformed operand".

Definition handle_BGTINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.gtb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BGTINT: not an integer"
    end
  else
    Error "BGTINT: malformed operand".

Definition handle_BGEINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.geb n a then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BGEINT: not an integer"
    end
  else
    Error "BGEINT: malformed operand".

Definition handle_ULTINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (Z.ltb (z_flip_sign a) (z_flip_sign b))|> <|stack := rest|>)
  | _, _ => Error "ULTINT: type error or stack underflow"
  end.

Definition handle_UGEINT (pc' : Z) (s : state) : step_result :=
  match s.(accu), s.(stack) with
  | Val_int a, Val_int b :: rest => Step (s <|pc := pc'|> <|accu := val_bool (Z.geb (z_flip_sign a) (z_flip_sign b))|> <|stack := rest|>)
  | _, _ => Error "UGEINT: type error or stack underflow"
  end.

(* BULTINT(n, target): branch if n < accu (unsigned). "n is ULT the integer accu."
   BUGEINT(n, target): branch if n >= accu (unsigned). "n is UGE the integer accu."
   Like signed B-ops (which use n CMP accu), both use z_flip_sign for unsigned order. *)
Definition handle_BULTINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.ltb (z_flip_sign n) (z_flip_sign a) then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BULTINT: not an integer"
    end
  else
    Error "BULTINT: malformed operand".

Definition handle_BUGEINT (n : Z) (target : Z) (pc' : Z) (s : state) : step_result :=
  if ((0 <=? n) && (Int.min_signed <=? n) && (n <=? Int.max_signed))%Z then
    match s.(accu) with
    | Val_int a => if Z.geb (z_flip_sign n) (z_flip_sign a) then Step (s <|pc := target|>)
                   else Step (s <|pc := pc'|>)
    | _ => Error "BUGEINT: not an integer"
    end
  else
    Error "BUGEINT: malformed operand".

Definition handle_STOP (s : state) : step_result :=
  Halt s.(accu).
