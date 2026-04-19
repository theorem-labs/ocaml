(* Run.v - [TRUSTED] Functor that builds step / run_micro / handle_bcmicro /
   run / run_pure on top of an abstract per-instruction dispatcher.  The
   implementation of that dispatcher lives in
   automatic/Bytecode/HandleInstr.v and is ascribed to HandleInstrSpec
   inside checker/Bytecode/InterpretChecker.v. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib.Array Require Import PrimArray.
From Stdlib.Numbers.Cyclic.Int63 Require Import Uint63.
From OCamlInterp.Manual.Utils Require Import Value.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.
From RecordUpdate Require Import RecordUpdate.
Open Scope Z_scope.

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
    | nil => a
    | cons x xs => go (S i) xs (PrimArray.set a (Uint63.of_Z (Z.of_nat i)) x)
    end) 0%nat l arr.

Module Make (H : HandleInstrSpec).

(* One step of the abstract machine: fetch, dispatch to H.handle_instr. *)
Definition step (code : array instruction) (s : state) : step_result :=
  match fetch_instr code s.(pc) with
  | None => Error "pc out of bounds"
  | Some instr => H.handle_instr instr (s.(pc) + 1) s
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

End Make.
