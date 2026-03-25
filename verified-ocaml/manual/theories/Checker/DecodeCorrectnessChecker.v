(* DecodeCorrectnessChecker.v - Checker: verifies that the untrusted decoder
   and roundtrip proofs satisfy the trusted DecodeSpec. *)

From OCamlInterp.Manual.Bytecode Require Import DecodeSpec.
From OCamlInterp.Automatic.Bytecode Require Import DecodeProof.

Module Check <: DecodeSpec.
  Definition decode := decode.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
