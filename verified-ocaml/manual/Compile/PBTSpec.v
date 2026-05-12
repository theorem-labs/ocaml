(* PBTSpec.v - [TRUSTED] Module Type for the PBT connection between
   our compiler and ocamlc.

   Following the pattern from the Go verified compiler: external tools
   (ocamlc, decoder) are Parameters that the untrusted side fills with
   concrete implementations embedding actual test results. The theorem
   is universally quantified over a seed type.

   The seed type is abstract here; the auto side defines it as a finite
   inductive type whose constructors correspond to concrete test cases.
   For each seed, pbt_program maps it deterministically to a source
   program. ocamlc_compile and ocamlc_decode model the external pipeline
   (pretty-print, run ocamlc, decode bytecode file). The proof is by
   exhaustive case analysis over seeds + native_compute/vm_compute.

   Trust model: this file defines the correctness statement using only
   trusted components (bytecode_behavior, behavior_equiv, step_list_of
   from CompileSpec.v). The untrusted code provides all Parameters and
   a proof of compile_models_ocamlc_ok.

   This file has NO dependencies outside manual/. *)

From Stdlib Require Import ZArith PeanoNat Strings.String.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Utils Require Import Value.
From RecordUpdate Require Import RecordUpdate.
From OCamlInterp.Manual.Bytecode Require Import AST Machine.
From OCamlInterp.Manual.Bytecode.Interpret Require Import Run HandleInstrSpec.
From OCamlInterp.Manual.Utils Require Import Observable.
From OCamlInterp.Manual.Utils Require Import Syntax.
From OCamlInterp.Manual.Compile Require Import CompileSpec.

Module Type PBTSpec (Import HI : HandleInstrSpec).

  Definition step_fn : list instruction -> state -> step_result :=
    step_list_of HI.handle_instr.

  (* Compiler under test (provided by automatic/) *)
  Parameter compile_program : program -> list instruction.

  (* PBT seed type and deterministic program generator.
     The auto side defines pbt_seed as a finite inductive type
     (e.g. Inductive pbt_seed := Seed1 | Seed2 | ... | SeedN)
     and pbt_program as a function mapping each seed to a
     concrete test program. *)
  Parameter pbt_seed : Type.
  Parameter pbt_program : pbt_seed -> program.

  (* External ocamlc pipeline: pretty-print the program, compile
     with ocamlc, return raw bytecode file bytes as list Z.
     Returns None if ocamlc rejects the program. *)
  Parameter ocamlc_compile : program -> option (list Z).

  (* Bytecode file decoder: parse ocamlc's bytecode output into
     an instruction list suitable for our interpreter.
     Returns None if decoding fails. *)
  Parameter ocamlc_decode : list Z -> option (list instruction).

  (* PBT connection theorem: for every seed, if ocamlc compiles the
     seed's program and we can decode the output, then our compiled
     bytecode and ocamlc's bytecode exhibit equivalent observable
     behavior under our interpreter at every fuel level.

     None branches are True: ocamlc rejection or decode failure on a
     seed is acceptable (not a compiler bug). Only a behavioral
     *disagreement* where both succeed constitutes a failure. *)
  Axiom compile_models_ocamlc_ok :
    forall (seed : pbt_seed),
      let p := pbt_program seed in
      match ocamlc_compile p with
      | Some ocamlc_bytes =>
        match ocamlc_decode ocamlc_bytes with
        | Some ocamlc_instrs =>
          forall (fuel : nat),
            behavior_equiv
              (bytecode_behavior step_fn fuel (compile_program p) [])
              (bytecode_behavior step_fn fuel ocamlc_instrs [])
        | None => True
        end
      | None => True
      end.

  (* Anti-vacuity: at least one seed compiles and decodes successfully,
     preventing ocamlc_compile/ocamlc_decode from trivially returning
     None on all inputs. *)
  Parameter golden_seed : pbt_seed.
  Axiom golden_compiles_and_decodes :
    match ocamlc_compile (pbt_program golden_seed) with
    | Some bytes =>
      match ocamlc_decode bytes with
      | Some _ => True
      | None => False
      end
    | None => False
    end.

End PBTSpec.
