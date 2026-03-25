(* Extract.v - Extraction directives.
   Run with: coqc -R _build/default/theories OCamlInterp theories/Extract.v
   Output goes to Interp_extracted.ml in the current directory. *)

From Stdlib Require Import ZArith Strings.String List.
From Stdlib Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlZInt.
From Stdlib Require Import ExtrOcamlString.

From OCamlInterp.Trusted.Bytecode Require Import Value AST Machine Interp Encode.
From OCamlInterp.Trusted Require Import IO.
From OCamlInterp Require Import Main.
From OCamlInterp.Trusted Require Import Observable.
From OCamlInterp.SemiTrusted Require Import Syntax PrettyPrint.
From OCamlInterp.Untrusted Require Import SourceInterp Compile Loader CorrectnessProofs.

(* z_flip_sign must use native OCaml lxor with min_int for correct unsigned comparison.
   Z.lxor is not extracted natively by ExtrOcamlZInt (it uses big-integer algorithms),
   so we override it directly. *)
Extract Constant z_flip_sign => "fun a -> a lxor min_int".

(* z_lsr must use native OCaml lsr for correct unsigned (logical) right shift.
   The Rocq definition uses Z.ones 63 as a mask, but Z.ones 63 = pred(2^63) overflows
   in 63-bit OCaml int arithmetic, making z_unsigned and z_lsr incorrect.
   Native `lsr` correctly handles the 63-bit unsigned shift. *)
Extract Constant z_lsr => "fun a b -> a lsr b".

Extraction "Interp_extracted.ml"
  (* Value *)
  value Val_int Val_block Val_ptr Val_closure
  (* Bytecode *)
  instruction
  (* Machine / bytecode interpreter *)
  state mk_state step run run_pure
  step_result run_result
  set_accu initial_state
  field_or_heap tag_or_heap size_or_heap
  heap_alloc heap_lookup heap_update
  (* Pretty-printer *)
  pp_expr pp_pattern pp_decl pp_program
  (* Observable behavior *)
  event behavior termination mk_behavior
  (* Source interpreter *)
  svalue env eval eval_program interpret
  (* Compiler *)
  compile_program
  (* Encoder *)
  encode_bytecode
  (* Loader / decoder *)
  decode_bytecode load_code_section
  parse_sections find_section section
  read_u32_le read_i32_le read_u32_be.
  (* main excluded: it's an eager top-level value that reads argv[1] on module load *)
