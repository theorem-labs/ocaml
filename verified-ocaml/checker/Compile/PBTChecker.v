(* PBTChecker.v - Verifies that the untrusted Stage 2 PBT obligations
   satisfy the trusted PBTSpec Module Type. *)

From OCamlInterp.Manual.Compile Require Import PBTSpec.
From OCamlInterp.Manual.Bytecode.Interpret Require Import HandleInstrSpec.
From OCamlInterp.Automatic.Bytecode.Interpret Require Import Dispatch.
From OCamlInterp.Automatic.Compile Require Import PBTProof.

Module DispatchHI <: HandleInstrSpec.
  Definition handle_instr := Dispatch.handle_instr.
End DispatchHI.

Module Check <: PBTSpec DispatchHI := PBTProof.Make DispatchHI.
