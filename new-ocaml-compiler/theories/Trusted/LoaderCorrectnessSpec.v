(* LoaderCorrectnessSpec.v - [TRUSTED] Module Type specifying the contract
   for the encode/decode roundtrip. The encoder (Trusted) produces bytes;
   the decoder (Untrusted) must invert it. The theorem statement is trusted;
   the proof is untrusted and checked in Checker. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
From OCamlInterp.Trusted Require Import Bytecode Encode.

Module Type LoaderCorrectnessSpec.

  (* Decoder (provided by Untrusted) *)
  Parameter decode_bytecode : list Z -> nat -> nat -> list instruction.

  (* Well-formedness predicates (provided by Untrusted) *)
  Parameter z_fits_i32 : Z -> Prop.
  Parameter well_formed : list instruction -> Prop.

  (* Byte-level roundtrip: reading back encoded words *)
  Parameter read_u32_le : list Z -> nat -> Z.
  Parameter read_i32_le : list Z -> nat -> Z.

  Axiom read_u32_le_encode_word_le : forall v,
    (0 <= v < 4294967296)%Z ->
    read_u32_le (encode_word_le v) 0 = v.

  Axiom read_i32_le_encode_word_le : forall v,
    z_fits_i32 v ->
    read_i32_le (encode_word_le v) 0 = v.

  (* Main roundtrip theorem: decoding encoded bytecode recovers the original *)
  Axiom decode_encode_inverse : forall code,
    well_formed code ->
    decode_bytecode (encode_bytecode code) 0
                    (List.length (encode_bytecode code)) = code.

End LoaderCorrectnessSpec.
