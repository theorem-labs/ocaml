(* DecodeCorrectnessChecker.v - Checker: verifies that the untrusted decoder
   and roundtrip proofs satisfy the trusted DecodeCorrectnessSpec. *)

From OCamlInterp.Manual.InterpBytecode Require Import DecodeCorrectnessSpec.
From OCamlInterp.Automatic.InterpBytecode Require Import DecodeCorrectnessProofs.

Module Check <: DecodeCorrectnessSpec.
  Definition decode := decode.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
