(* LoaderCorrectnessSpec.v - [TRUSTED] Module Type specifying the contract
   for the encode/decode roundtrip. The encoder and well-formedness predicate
   are declared as Parameters (provided by Untrusted code); the theorems
   state that decoding encoded bytecode recovers the original program. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
From OCamlInterp.Trusted Require Import Bytecode Loader.

Module Type LoaderCorrectnessSpec.

  (* Encoder (provided by Untrusted) *)
  Parameter encode_bytecode : list instruction -> list Z.
  Parameter encode_word_le : Z -> list Z.

  (* Well-formedness predicates (provided by Untrusted) *)
  Parameter z_fits_i32 : Z -> Prop.
  Parameter well_formed : list instruction -> Prop.

  (* Byte-level roundtrip *)
  Axiom read_u32_le_encode_word_le : forall v,
    (0 <= v < 4294967296)%Z ->
    read_u32_le (encode_word_le v) 0 = v.

  Axiom read_i32_le_encode_word_le : forall v,
    z_fits_i32 v ->
    read_i32_le (encode_word_le v) 0 = v.

  (* Main roundtrip theorem *)
  Axiom decode_encode_inverse : forall code,
    well_formed code ->
    decode_bytecode (encode_bytecode code) 0
                    (List.length (encode_bytecode code)) = code.

End LoaderCorrectnessSpec.
