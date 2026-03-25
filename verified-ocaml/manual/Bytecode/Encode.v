(* Encode.v - Bytecode encoder.
   Inverse of the loader/decoder: given a list of instructions (using
   abstract instruction indices for branch targets), produce the CODE
   section bytes in the same binary format that ocamlc produces.

   Encoding strategy:
   - Always use the general opcode form (e.g. ACC=8 with one operand,
     never ACC0..ACC7).  This is simpler and still valid bytecode.
   - Two-pass: first pass computes instruction sizes to build an
     index-to-word-offset map; second pass emits words, converting
     absolute instruction indices back to relative word offsets for
     branch targets.
   - Words are emitted as 4-byte little-endian sequences of Z values
     (each byte 0..255). *)

From Stdlib Require Import ZArith List PeanoNat.
From OCamlInterp.Manual.Bytecode Require Import AST.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Instruction word sizes                                              *)
(* ------------------------------------------------------------------ *)

(* Number of 32-bit words an instruction occupies (opcode + operands). *)
Definition instr_word_size (i : instruction) : nat :=
  match i with
  | ACC _            => 2
  | PUSH             => 1
  | PUSHACC _        => 2
  | POP _            => 2
  | ASSIGN _         => 2
  | ENVACC _         => 2
  | PUSHENVACC _     => 2
  | PUSH_RETADDR _   => 2
  | APPLY _          => 2
  | APPLY1           => 1
  | APPLY2           => 1
  | APPLY3           => 1
  | APPTERM _ _      => 3
  | APPTERM1 _       => 2
  | APPTERM2 _       => 2
  | APPTERM3 _       => 2
  | RETURN _         => 2
  | RESTART          => 1
  | GRAB _           => 2
  | CLOSURE _ _      => 3
  | CLOSUREREC nf _ ofs => 3 + List.length ofs
  | OFFSETCLOSURE _      => 2
  | PUSHOFFSETCLOSURE _  => 2
  | GETGLOBAL _          => 2
  | PUSHGETGLOBAL _      => 2
  | GETGLOBALFIELD _ _       => 3
  | PUSHGETGLOBALFIELD _ _   => 3
  | SETGLOBAL _          => 2
  | ATOM _           => 2
  | PUSHATOM _       => 2
  | MAKEBLOCK _ _    => 3
  | MAKEBLOCK1 _     => 2
  | MAKEBLOCK2 _     => 2
  | MAKEBLOCK3 _     => 2
  | MAKEFLOATBLOCK _ => 2
  | GETFIELD _       => 2
  | GETFLOATFIELD _  => 2
  | SETFIELD _       => 2
  | SETFLOATFIELD _  => 2
  | VECTLENGTH       => 1
  | GETVECTITEM      => 1
  | SETVECTITEM      => 1
  | GETBYTESCHAR     => 1
  | SETBYTESCHAR     => 1
  | GETSTRINGCHAR    => 1
  | BRANCH _         => 2
  | BRANCHIF _       => 2
  | BRANCHIFNOT _    => 2
  | SWITCH nc nb ct bt => 2 + List.length ct + List.length bt
  | BOOLNOT          => 1
  | PUSHTRAP _       => 2
  | POPTRAP          => 1
  | RAISE            => 1
  | RERAISE          => 1
  | RAISE_NOTRACE    => 1
  | CHECK_SIGNALS    => 1
  | C_CALL _ _       => 3
  | CONSTINT _       => 2
  | PUSHCONSTINT _   => 2
  | NEGINT           => 1
  | ADDINT           => 1
  | SUBINT           => 1
  | MULINT           => 1
  | DIVINT           => 1
  | MODINT           => 1
  | ANDINT           => 1
  | ORINT            => 1
  | XORINT           => 1
  | LSLINT           => 1
  | LSRINT           => 1
  | ASRINT           => 1
  | EQ               => 1
  | NEQ              => 1
  | LTINT            => 1
  | LEINT            => 1
  | GTINT            => 1
  | GEINT            => 1
  | OFFSETINT _      => 2
  | OFFSETREF _      => 2
  | ISINT            => 1
  | GETMETHOD        => 1
  | GETPUBMET _      => 3  (* tag + cache skip word *)
  | GETDYNMET        => 1
  | BEQ _ _          => 3
  | BNEQ _ _         => 3
  | BLTINT _ _       => 3
  | BLEINT _ _       => 3
  | BGTINT _ _       => 3
  | BGEINT _ _       => 3
  | ULTINT           => 1
  | UGEINT           => 1
  | BULTINT _ _      => 3
  | BUGEINT _ _      => 3
  | STOP             => 1
  | EVENT            => 1
  | BREAK            => 1
  | PERFORM          => 1
  | RESUME           => 1
  | RESUMETERM _     => 2
  | REPERFORMTERM _  => 2
  end.

(* ------------------------------------------------------------------ *)
(* Offset map: instruction index -> word offset                        *)
(* ------------------------------------------------------------------ *)

(* Build a list where the i-th element is the word offset of instruction i. *)
Fixpoint build_offset_list (code : list instruction) (acc : nat) : list nat :=
  match code with
  | nil => nil
  | i :: rest => acc :: build_offset_list rest (acc + instr_word_size i)
  end.

Definition offset_map (code : list instruction) : list nat :=
  build_offset_list code 0.

(* Look up the word offset for instruction index idx. *)
Definition lookup_offset (omap : list nat) (idx : Z) : Z :=
  match List.nth_error omap (Z.to_nat idx) with
  | Some n => Z.of_nat n
  | None   => 0  (* should not happen for well-formed programs *)
  end.

(* ------------------------------------------------------------------ *)
(* Little-endian 32-bit word encoding                                  *)
(* ------------------------------------------------------------------ *)

Definition encode_word_le (v : Z) : list Z :=
  let u := Z.land v 4294967295 in  (* mask to 32 bits = 0xFFFFFFFF *)
  let b0 := Z.land u 255 in
  let b1 := Z.land (Z.shiftr u 8) 255 in
  let b2 := Z.land (Z.shiftr u 16) 255 in
  let b3 := Z.land (Z.shiftr u 24) 255 in
  [b0; b1; b2; b3].

(* ------------------------------------------------------------------ *)
(* Instruction encoding (second pass)                                  *)
(* ------------------------------------------------------------------ *)

(* Emit a list of Z words as consecutive LE 32-bit values. *)
Definition emit_words (ws : list Z) : list Z :=
  List.flat_map encode_word_le ws.

(* Helper: relative branch offset.
   The branch operand word is at position [from_word].  The target
   instruction index is [target_idx].  The relative offset stored in
   the bytecode is target_word_offset - from_word. *)
Definition rel_offset (omap : list nat) (from_word : Z) (target_idx : Z) : Z :=
  lookup_offset omap target_idx - from_word.

(* Encode one instruction at instruction index [idx] using [omap]. *)
Definition encode_instr (omap : list nat) (idx : nat) (i : instruction) : list Z :=
  let w := Z.of_nat (match List.nth_error omap idx with
                      | Some n => n | None => 0 end) in
  match i with
  (* --- ACC family: opcode 8 + operand --- *)
  | ACC n            => emit_words [8; Z.of_nat n]
  | PUSH             => emit_words [9]
  | PUSHACC n        => emit_words [18; Z.of_nat n]
  | POP n            => emit_words [19; Z.of_nat n]
  | ASSIGN n         => emit_words [20; Z.of_nat n]
  | ENVACC n         => emit_words [25; Z.of_nat n]
  | PUSHENVACC n     => emit_words [30; Z.of_nat n]
  (* Branch target: PUSH_RETADDR operand at w+1 *)
  | PUSH_RETADDR t  => emit_words [31; rel_offset omap (w + 1) t]
  | APPLY n          => emit_words [32; Z.of_nat n]
  | APPLY1           => emit_words [33]
  | APPLY2           => emit_words [34]
  | APPLY3           => emit_words [35]
  | APPTERM n s      => emit_words [36; Z.of_nat n; Z.of_nat s]
  | APPTERM1 s       => emit_words [37; Z.of_nat s]
  | APPTERM2 s       => emit_words [38; Z.of_nat s]
  | APPTERM3 s       => emit_words [39; Z.of_nat s]
  | RETURN n         => emit_words [40; Z.of_nat n]
  | RESTART          => emit_words [41]
  | GRAB n           => emit_words [42; Z.of_nat n]
  (* CLOSURE: opcode 43, nv, code_offset.
     In the decoder: target = (w+2) + ofs, so ofs = target_word - (w+2). *)
  | CLOSURE nv codeptr =>
      emit_words [43; Z.of_nat nv; rel_offset omap (w + 2) codeptr]
  (* CLOSUREREC: opcode 44, nfuncs, nvars, offsets...
     In the decoder: target = (w+3) + ofs for each offset word. *)
  | CLOSUREREC nf nv ofs_list =>
      emit_words ([44; Z.of_nat nf; Z.of_nat nv] ++
                  List.map (fun t => rel_offset omap (w + 3) t) ofs_list)
  | OFFSETCLOSURE n      => emit_words [48; n]
  | PUSHOFFSETCLOSURE n  => emit_words [52; n]
  | GETGLOBAL n          => emit_words [53; Z.of_nat n]
  | PUSHGETGLOBAL n      => emit_words [54; Z.of_nat n]
  | GETGLOBALFIELD n p   => emit_words [55; Z.of_nat n; Z.of_nat p]
  | PUSHGETGLOBALFIELD n p => emit_words [56; Z.of_nat n; Z.of_nat p]
  | SETGLOBAL n          => emit_words [57; Z.of_nat n]
  | ATOM t           => emit_words [59; Z.of_nat t]
  | PUSHATOM t       => emit_words [61; Z.of_nat t]
  (* MAKEBLOCK: opcode 62, size, tag *)
  | MAKEBLOCK tag sz => emit_words [62; Z.of_nat sz; Z.of_nat tag]
  | MAKEBLOCK1 t     => emit_words [63; Z.of_nat t]
  | MAKEBLOCK2 t     => emit_words [64; Z.of_nat t]
  | MAKEBLOCK3 t     => emit_words [65; Z.of_nat t]
  | MAKEFLOATBLOCK s => emit_words [66; Z.of_nat s]
  | GETFIELD n       => emit_words [71; Z.of_nat n]
  | GETFLOATFIELD n  => emit_words [72; Z.of_nat n]
  | SETFIELD n       => emit_words [77; Z.of_nat n]
  | SETFLOATFIELD n  => emit_words [78; Z.of_nat n]
  | VECTLENGTH       => emit_words [79]
  | GETVECTITEM      => emit_words [80]
  | SETVECTITEM      => emit_words [81]
  | GETBYTESCHAR     => emit_words [82]
  | SETBYTESCHAR     => emit_words [83]
  | GETSTRINGCHAR    => emit_words [148]
  (* Branches: operand at w+1 *)
  | BRANCH t         => emit_words [84; rel_offset omap (w + 1) t]
  | BRANCHIF t       => emit_words [85; rel_offset omap (w + 1) t]
  | BRANCHIFNOT t    => emit_words [86; rel_offset omap (w + 1) t]
  (* SWITCH: opcode 87, packed sizes, then table entries.
     Decoder: base = w+2, target = base + entry *)
  | SWITCH nc nb ct bt =>
      let sizes := Z.lor (Z.of_nat nc) (Z.shiftl (Z.of_nat nb) 16) in
      let base := w + 2 in
      let ct_rels := List.map (fun t => rel_offset omap base t) ct in
      let bt_rels := List.map (fun t => rel_offset omap base t) bt in
      emit_words ([87; sizes] ++ ct_rels ++ bt_rels)
  | BOOLNOT          => emit_words [88]
  | PUSHTRAP t       => emit_words [89; rel_offset omap (w + 1) t]
  | POPTRAP          => emit_words [90]
  | RAISE            => emit_words [91]
  | CHECK_SIGNALS    => emit_words [92]
  (* C_CALLN: opcode 98, narg, prim *)
  | C_CALL narg prim => emit_words [98; Z.of_nat narg; Z.of_nat prim]
  | CONSTINT n       => emit_words [103; n]
  | PUSHCONSTINT n   => emit_words [108; n]
  | NEGINT           => emit_words [109]
  | ADDINT           => emit_words [110]
  | SUBINT           => emit_words [111]
  | MULINT           => emit_words [112]
  | DIVINT           => emit_words [113]
  | MODINT           => emit_words [114]
  | ANDINT           => emit_words [115]
  | ORINT            => emit_words [116]
  | XORINT           => emit_words [117]
  | LSLINT           => emit_words [118]
  | LSRINT           => emit_words [119]
  | ASRINT           => emit_words [120]
  | EQ               => emit_words [121]
  | NEQ              => emit_words [122]
  | LTINT            => emit_words [123]
  | LEINT            => emit_words [124]
  | GTINT            => emit_words [125]
  | GEINT            => emit_words [126]
  | OFFSETINT n      => emit_words [127; n]
  | OFFSETREF n      => emit_words [128; n]
  | ISINT            => emit_words [129]
  | GETMETHOD        => emit_words [130]
  (* BEQ..BGEINT: opcode, constant, branch offset.
     Branch operand is at w+2. *)
  | BEQ n t          => emit_words [131; n; rel_offset omap (w + 2) t]
  | BNEQ n t         => emit_words [132; n; rel_offset omap (w + 2) t]
  | BLTINT n t       => emit_words [133; n; rel_offset omap (w + 2) t]
  | BLEINT n t       => emit_words [134; n; rel_offset omap (w + 2) t]
  | BGTINT n t       => emit_words [135; n; rel_offset omap (w + 2) t]
  | BGEINT n t       => emit_words [136; n; rel_offset omap (w + 2) t]
  | ULTINT           => emit_words [137]
  | UGEINT           => emit_words [138]
  | BULTINT n t      => emit_words [139; n; rel_offset omap (w + 2) t]
  | BUGEINT n t      => emit_words [140; n; rel_offset omap (w + 2) t]
  (* GETPUBMET: opcode 141, tag, cache (always 0) *)
  | GETPUBMET t      => emit_words [141; t; 0]
  | GETDYNMET        => emit_words [142]
  | STOP             => emit_words [143]
  | EVENT            => emit_words [144]
  | BREAK            => emit_words [145]
  | RERAISE          => emit_words [146]
  | RAISE_NOTRACE    => emit_words [147]
  | PERFORM          => emit_words [149]
  | RESUME           => emit_words [150]
  | RESUMETERM n     => emit_words [151; Z.of_nat n]
  | REPERFORMTERM n  => emit_words [152; Z.of_nat n]
  end.

(* ------------------------------------------------------------------ *)
(* Main entry point                                                    *)
(* ------------------------------------------------------------------ *)

Fixpoint encode_instrs (omap : list nat) (idx : nat) (code : list instruction) : list Z :=
  match code with
  | nil => nil
  | i :: rest => encode_instr omap idx i ++ encode_instrs omap (S idx) rest
  end.

Definition encode_bytecode (code : list instruction) : list Z :=
  let omap := offset_map code in
  encode_instrs omap 0 code.
