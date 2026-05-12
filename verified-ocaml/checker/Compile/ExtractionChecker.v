(* ExtractionChecker.v - Verifies that the untrusted Stage 2 extraction
   obligations satisfy the trusted ExtractionSpec Module Type. *)

From OCamlInterp.Manual.Compile Require Import ExtractionSpec.
From OCamlInterp.Automatic.Compile Require Import ExtractionProof.

Module Check <: ExtractionSpec := ExtractionProof.ExtractionValidation.
