(* LoaderCorrectness.v - Checker: verifies that the untrusted decoder
   and roundtrip proofs satisfy the trusted LoaderCorrectnessSpec. *)

From OCamlInterp.Trusted Require Import LoaderCorrectnessSpec.
From OCamlInterp.Untrusted Require Import Loader LoaderCorrectnessProofs.

Module Check <: LoaderCorrectnessSpec.
  Definition decode_bytecode := decode_bytecode.
  Definition read_u32_le := read_u32_le.
  Definition read_i32_le := read_i32_le.
  Definition read_u32_le_encode_word_le := read_u32_le_encode_word_le.
  Definition read_i32_le_encode_word_le := read_i32_le_encode_word_le.
  Definition decode_encode_inverse := decode_encode_inverse.
End Check.
