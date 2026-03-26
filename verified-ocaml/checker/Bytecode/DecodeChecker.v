(* DecodeChecker.v - Verifies that the untrusted proof satisfies the
   trusted DecodeSpec Module Type. *)

From OCamlInterp.Manual.Bytecode Require Import DecodeSpec.
From OCamlInterp.Automatic.Bytecode Require Import DecodeProof.

Module Check <: DecodeSpec.
  Definition decode := decode.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
