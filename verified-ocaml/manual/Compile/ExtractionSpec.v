(* ExtractionSpec.v - [TRUSTED] Module Type specifying translation
   validation of the extracted compiler.

   The extracted bytecode is abstract; the checker fills it with
   concrete instruction lists obtained by running the extracted OCaml
   binary on pp_program(prog) and decoding its output.

   Trust model: this file defines the CONCRETE validation statement using
   only trusted components. The untrusted code must provide compile_program,
   validation_programs, extracted_bytecode, and a proof of agreement.

   This file has NO dependencies outside manual/. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST.
From OCamlInterp.Manual.Utils Require Import Syntax.
Open Scope list_scope.

Module Type ExtractionSpec.

  (* Compiler (the Rocq definition, from automatic/) *)
  Parameter compile_program : program -> list instruction.

  (* Finite validation suite *)
  Parameter validation_programs : list program.

  (* Bytecode produced by the extracted compiler binary.
     At proof time, filled with instruction lists obtained by:
     1. Extracting compile_program to OCaml (via checker/Extract.v)
     2. Running the extracted binary on pp_program(prog) for each prog
     3. Decoding the output bytecode back to list instruction *)
  Parameter extracted_bytecode : program -> list instruction.

  (* Non-triviality *)
  Axiom validation_suite_nonempty : (length validation_programs >= 1)%nat.

  (* Translation validation: the extracted compiler produces identical
     bytecode to the Rocq definition on every validation program. *)
  Axiom extraction_faithful :
    forall (prog : program),
      In prog validation_programs ->
      extracted_bytecode prog = compile_program prog.

End ExtractionSpec.
