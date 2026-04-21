(* Helpers.v - Small utility definitions used across the bytecode
   interpreter that do not depend on the full Handlers module.

   Currently contains get_code_ptr_from / get_code_ptr_s, which are
   needed by both Handlers.v (instruction handlers) and InstructSpec.v
   (Clight correctness specifications). *)

From Stdlib Require Import ZArith PeanoNat List.
Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import Machine.

Open Scope Z_scope.

Definition get_code_ptr_from (fields : list value) (ofs : nat) : option Z :=
  match List.nth_error fields ofs with
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
