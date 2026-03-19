(* Extract.v - Extraction directives. *)

From Stdlib Require Import ZArith Strings.String List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

From OCamlInterp Require Import Value Bytecode Machine Interp Syntax PrettyPrint.

Extraction "Interp_extracted.ml"
  step run run_pure
  pp_expr pp_pattern pp_decl pp_program
  initial_state.
