(* DecodeCorrectnessSpec.v - [TRUSTED] Module Type specifying the contract
   for the encode/decode roundtrip. The encoder (Trusted) produces bytes;
   the decoder (Untrusted) must invert it. The theorem statement is trusted;
   the proof is untrusted and checked in Checker. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
From OCamlInterp.Manual.Utils Require Import AST.
From OCamlInterp.Manual.InterpBytecode Require Import Encode WellFormed.

Module Type DecodeCorrectnessSpec.

  (* Decoder (provided by Untrusted): takes raw bytes, returns instructions *)
  Parameter decode : list Z -> list instruction.

  (* Main roundtrip theorem: decoding encoded bytecode recovers the original *)
  Axiom decode_encode_inverse : forall code,
    well_formed code = true ->
    decode (encode_bytecode code) = code.

End DecodeCorrectnessSpec.
