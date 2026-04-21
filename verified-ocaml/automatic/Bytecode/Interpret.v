(* Interpret.v - [UNTRUSTED] Umbrella that instantiates the
   Run functor (from manual/Bytecode/Interpret/Run.v) at the Dispatch
   module (from automatic/Bytecode/Interpret/Dispatch.v) and exposes the
   resulting step / run / run_micro / handle_bcmicro / run_pure at the
   top level via Include.

   It re-exports Handlers (the 151 per-opcode definitions) and Dispatch
   (handle_instr) so downstream callers that used to `Import
   Automatic.Bytecode.Interpret` and name handle_<OP> or handle_instr
   directly keep working.

   This file lives in automatic/ specifically so manual/ stays minimal:
   any unfold-ergonomics or re-exports that exist only to spare
   downstream proofs from updates belong here, not in the trusted base. *)

From OCamlInterp.Automatic.Bytecode.Interpret Require Export Handlers Dispatch.
From OCamlInterp.Manual.Bytecode.Interpret Require Export Run.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.

Module DispatchImpl <: HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End DispatchImpl.

Include Run.Make DispatchImpl.
