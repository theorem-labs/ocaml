(* Decode.v - Bytecode decoder.
   Ports the decoding logic from test/common/loader.ml to Rocq.
   Works on (list Z) raw bytes, producing (list instruction). *)

From Stdlib Require Import ZArith PeanoNat Bool.
From Stdlib Require Import List. Import ListNotations.
From OCamlInterp.Manual.Bytecode Require Import AST DecodeSpec.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Byte-level helpers                                                  *)
(* ------------------------------------------------------------------ *)

(* Read a single byte from a list at a given offset. Returns 0 if out of bounds. *)
Fixpoint byte_at (data : list Z) (off : nat) : Z :=
  match data, off with
  | [], _ => 0
  | b :: _, O => b
  | _ :: rest, S n => byte_at rest n
  end.

(* Read unsigned 32-bit little-endian value. *)
Definition read_u32_le (data : list Z) (off : nat) : Z :=
  let b0 := byte_at data off in
  let b1 := byte_at data (S off) in
  let b2 := byte_at data (S (S off)) in
  let b3 := byte_at data (S (S (S off))) in
  Z.lor b0
    (Z.lor (Z.shiftl b1 8)
       (Z.lor (Z.shiftl b2 16)
              (Z.shiftl b3 24))).

(* Read signed 32-bit little-endian value. *)
Definition read_i32_le (data : list Z) (off : nat) : Z :=
  let u := read_u32_le data off in
  if Z.testbit u 31 then Z.lor u (Z.lnot (Z.ones 32))
  else u.

(* Read unsigned 32-bit big-endian value. *)
Definition read_u32_be (data : list Z) (off : nat) : Z :=
  let b0 := byte_at data off in
  let b1 := byte_at data (S off) in
  let b2 := byte_at data (S (S off)) in
  let b3 := byte_at data (S (S (S off))) in
  Z.lor (Z.shiftl b0 24)
    (Z.lor (Z.shiftl b1 16)
       (Z.lor (Z.shiftl b2 8) b3)).

(* ------------------------------------------------------------------ *)
(* Section table parsing                                               *)
(* ------------------------------------------------------------------ *)

(* section type imported from Manual.Bytecode.DecodeSpec *)

(* Parse section table from the trailer of a .byte file.
   data = full file contents as list Z, data_len = length of data. *)
Fixpoint sum_section_lengths (data : list Z) (toc_offset : nat) (n : nat) : nat :=
  match n with
  | O => O
  | S n' =>
    let len := Z.to_nat (read_u32_be data (toc_offset + n' * 8 + 4)%nat) in
    (len + sum_section_lengths data toc_offset n')%nat
  end.

Fixpoint build_sections (data : list Z) (toc_offset : nat)
    (current : nat) (i : nat) (count : nat) : list section :=
  match count with
  | O => []
  | S count' =>
    let entry := (toc_offset + i * 8)%nat in
    let name := read_u32_be data entry in
    let slen := Z.to_nat (read_u32_be data (entry + 4)%nat) in
    mk_section name current slen ::
      build_sections data toc_offset (current + slen)%nat (S i) count'
  end.

Definition parse_sections (data : list Z) (data_len : nat) : list section :=
  let num_sections := Z.to_nat (read_u32_be data (data_len - 16)%nat) in
  let toc_offset := (data_len - 16 - num_sections * 8)%nat in
  let total_data := sum_section_lengths data toc_offset num_sections in
  let data_start := (toc_offset - total_data)%nat in
  build_sections data toc_offset data_start 0 num_sections.

(* Encode "CODE" as big-endian u32: C=67, O=79, D=68, E=69. *)
Definition CODE_name : Z :=
  Z.lor (Z.shiftl 67 24)
    (Z.lor (Z.shiftl 79 16)
       (Z.lor (Z.shiftl 68 8) 69)).

Fixpoint find_section (secs : list section) (name : Z) : option section :=
  match secs with
  | [] => None
  | s :: rest =>
    if Z.eqb s.(sec_name) name then Some s
    else find_section rest name
  end.

(* ------------------------------------------------------------------ *)
(* Raw instruction decoding (pass 1)                                   *)
(* ------------------------------------------------------------------ *)

(* A raw instruction: opcode + list of signed operands, plus the word
   offset at which this instruction appeared in the CODE section. *)
Record raw_instr : Type := mk_raw {
  ri_word_offset : nat;
  ri_opcode      : Z;
  ri_operands    : list Z;
}.

(* Operand count by opcode. Returns None for special opcodes (SWITCH=87,
   CLOSUREREC=44, GETPUBMET=141) that need custom handling. *)
Definition operand_count (op : Z) : option nat :=
  (* 1-operand *)
  if Z.eqb op 8 then Some 1%nat else
  if Z.eqb op 18 then Some 1%nat else
  if Z.eqb op 19 then Some 1%nat else
  if Z.eqb op 20 then Some 1%nat else
  if Z.eqb op 25 then Some 1%nat else
  if Z.eqb op 30 then Some 1%nat else
  if Z.eqb op 31 then Some 1%nat else
  if Z.eqb op 32 then Some 1%nat else
  if Z.eqb op 37 then Some 1%nat else
  if Z.eqb op 38 then Some 1%nat else
  if Z.eqb op 39 then Some 1%nat else
  if Z.eqb op 40 then Some 1%nat else
  if Z.eqb op 42 then Some 1%nat else
  if Z.eqb op 48 then Some 1%nat else
  if Z.eqb op 52 then Some 1%nat else
  if Z.eqb op 53 then Some 1%nat else
  if Z.eqb op 54 then Some 1%nat else
  if Z.eqb op 57 then Some 1%nat else
  if Z.eqb op 59 then Some 1%nat else
  if Z.eqb op 61 then Some 1%nat else
  if Z.eqb op 63 then Some 1%nat else
  if Z.eqb op 64 then Some 1%nat else
  if Z.eqb op 65 then Some 1%nat else
  if Z.eqb op 66 then Some 1%nat else
  if Z.eqb op 71 then Some 1%nat else
  if Z.eqb op 72 then Some 1%nat else
  if Z.eqb op 77 then Some 1%nat else
  if Z.eqb op 78 then Some 1%nat else
  if Z.eqb op 84 then Some 1%nat else
  if Z.eqb op 85 then Some 1%nat else
  if Z.eqb op 86 then Some 1%nat else
  if Z.eqb op 89 then Some 1%nat else
  if Z.eqb op 93 then Some 1%nat else
  if Z.eqb op 94 then Some 1%nat else
  if Z.eqb op 95 then Some 1%nat else
  if Z.eqb op 96 then Some 1%nat else
  if Z.eqb op 97 then Some 1%nat else
  if Z.eqb op 103 then Some 1%nat else
  if Z.eqb op 108 then Some 1%nat else
  if Z.eqb op 127 then Some 1%nat else
  if Z.eqb op 128 then Some 1%nat else
  if Z.eqb op 151 then Some 1%nat else
  if Z.eqb op 152 then Some 1%nat else
  (* 2-operand *)
  if Z.eqb op 36 then Some 2%nat else
  if Z.eqb op 43 then Some 2%nat else
  if Z.eqb op 55 then Some 2%nat else
  if Z.eqb op 56 then Some 2%nat else
  if Z.eqb op 62 then Some 2%nat else
  if Z.eqb op 98 then Some 2%nat else
  if Z.eqb op 131 then Some 2%nat else
  if Z.eqb op 132 then Some 2%nat else
  if Z.eqb op 133 then Some 2%nat else
  if Z.eqb op 134 then Some 2%nat else
  if Z.eqb op 135 then Some 2%nat else
  if Z.eqb op 136 then Some 2%nat else
  if Z.eqb op 139 then Some 2%nat else
  if Z.eqb op 140 then Some 2%nat else
  (* Special opcodes: SWITCH=87, CLOSUREREC=44, GETPUBMET=141 *)
  if Z.eqb op 87 then None else
  if Z.eqb op 44 then None else
  if Z.eqb op 141 then None else
  (* Default: 0 operands *)
  Some 0%nat.

(* Read n signed i32 operands from byte position pos. *)
Fixpoint read_operands (data : list Z) (code_offset : nat)
    (pos : nat) (n : nat) : list Z * nat :=
  match n with
  | O => ([], pos)
  | S n' =>
    let v := read_i32_le data (code_offset + pos)%nat in
    let '(rest, pos') := read_operands data code_offset (pos + 4)%nat n' in
    (v :: rest, pos')
  end.

(* Decode raw instructions from the CODE section.
   data = full file, code_offset = byte offset of CODE section,
   code_length = byte length of CODE section.
   Returns list of raw instructions in order.
   fuel bounds the loop iteration count. *)
Fixpoint decode_raw_aux (data : list Z) (code_offset : nat)
    (code_length : nat) (pos : nat) (fuel : nat) : list raw_instr :=
  match fuel with
  | O => []
  | S fuel' =>
    if Nat.leb code_length pos then [] else
    let word := (pos / 4)%nat in
    let op := read_u32_le data (code_offset + pos)%nat in
    let pos1 := (pos + 4)%nat in
    if Z.eqb op 87 then
      (* SWITCH: read sizes, then (low16 + high16) table entries *)
      let sizes := read_i32_le data (code_offset + pos1)%nat in
      let pos2 := (pos1 + 4)%nat in
      let nc := Z.to_nat (Z.land sizes (Z.ones 16)) in
      let nb := Z.to_nat (Z.shiftr sizes 16) in
      let '(tbl, pos3) := read_operands data code_offset pos2 (nc + nb) in
      mk_raw word op (sizes :: tbl) ::
        decode_raw_aux data code_offset code_length pos3 fuel'
    else if Z.eqb op 44 then
      (* CLOSUREREC: read nfuncs, nvars, then nfuncs code offsets *)
      let nf := read_i32_le data (code_offset + pos1)%nat in
      let pos2 := (pos1 + 4)%nat in
      let nv := read_i32_le data (code_offset + pos2)%nat in
      let pos3 := (pos2 + 4)%nat in
      let '(ofs_list, pos4) := read_operands data code_offset pos3 (Z.to_nat nf) in
      mk_raw word op (nf :: nv :: ofs_list) ::
        decode_raw_aux data code_offset code_length pos4 fuel'
    else if Z.eqb op 141 then
      (* GETPUBMET: tag + cache (cache is discarded) *)
      let tag := read_i32_le data (code_offset + pos1)%nat in
      let pos2 := (pos1 + 4)%nat in
      (* skip cache word *)
      let pos3 := (pos2 + 4)%nat in
      mk_raw word op [tag] ::
        decode_raw_aux data code_offset code_length pos3 fuel'
    else
      match operand_count op with
      | Some n =>
        let '(ops, pos2) := read_operands data code_offset pos1 n in
        mk_raw word op ops ::
          decode_raw_aux data code_offset code_length pos2 fuel'
      | None =>
        (* Should not happen: all special opcodes handled above *)
        []
      end
  end.

Definition decode_raw (data : list Z) (code_offset : nat) (code_length : nat)
    : list raw_instr :=
  decode_raw_aux data code_offset code_length 0 (code_length + 1).

(* ------------------------------------------------------------------ *)
(* Word-offset to instruction-index map (pass 2)                       *)
(* ------------------------------------------------------------------ *)

(* Build an association list from word offsets to instruction indices. *)
Fixpoint build_offset_map_aux (raws : list raw_instr) (idx : nat)
    : list (nat * nat) :=
  match raws with
  | [] => []
  | ri :: rest =>
    (ri.(ri_word_offset), idx) :: build_offset_map_aux rest (S idx)
  end.

Definition build_offset_map (raws : list raw_instr) : list (nat * nat) :=
  build_offset_map_aux raws 0.

Fixpoint lookup_offset (m : list (nat * nat)) (w : nat) : nat :=
  match m with
  | [] => O  (* fallback *)
  | (k, v) :: rest =>
    if Nat.eqb k w then v else lookup_offset rest w
  end.

(* Resolve a relative branch: from word position wpos, relative offset rel,
   target word = wpos + rel, look up instruction index. *)
Definition resolve (omap : list (nat * nat)) (wpos : nat) (rel : Z) : Z :=
  Z.of_nat (lookup_offset omap (wpos + Z.to_nat (Z.max 0 (Z.of_nat wpos + rel - Z.of_nat wpos)) )%nat).

(* A simpler and correct resolve: target_word = wpos + rel (both in words),
   rel is a signed integer. We compute target = Z.of_nat wpos + rel,
   convert to nat, then look up. *)
Definition resolve_branch (omap : list (nat * nat)) (wpos : Z) (rel : Z) : Z :=
  let target := Z.to_nat (wpos + rel) in
  Z.of_nat (lookup_offset omap target).

(* ------------------------------------------------------------------ *)
(* Instruction resolution (pass 2)                                     *)
(* ------------------------------------------------------------------ *)

Definition nat_of_z (z : Z) : nat := Z.to_nat z.

(* Get the nth element from a list Z, defaulting to 0. *)
Definition znth (n : nat) (l : list Z) : Z :=
  match nth_error l n with
  | Some v => v
  | None => 0
  end.

Definition resolve_one (omap : list (nat * nat)) (ri : raw_instr) : instruction :=
  let op := ri.(ri_opcode) in
  let ops := ri.(ri_operands) in
  let w := ri.(ri_word_offset) in
  (* br n: resolve branch at operand position n.
     The word address of operand n is w+1+n (opcode at w, operands at w+1, w+2, ...).
     Target word = (w+1+n) + ops[n]. *)
  let br := fun (n : nat) => resolve_branch omap (Z.of_nat (w + 1 + n)%nat) (znth n ops) in
  (* ACC0-ACC7 *)
  if Z.eqb op 0 then ACC 0 else
  if Z.eqb op 1 then ACC 1 else
  if Z.eqb op 2 then ACC 2 else
  if Z.eqb op 3 then ACC 3 else
  if Z.eqb op 4 then ACC 4 else
  if Z.eqb op 5 then ACC 5 else
  if Z.eqb op 6 then ACC 6 else
  if Z.eqb op 7 then ACC 7 else
  if Z.eqb op 8 then ACC (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 9 then PUSH else
  (* PUSHACC0-PUSHACC7=10..17, PUSHACC=18 *)
  if Z.eqb op 10 then PUSHACC 0 else
  if Z.eqb op 11 then PUSHACC 1 else
  if Z.eqb op 12 then PUSHACC 2 else
  if Z.eqb op 13 then PUSHACC 3 else
  if Z.eqb op 14 then PUSHACC 4 else
  if Z.eqb op 15 then PUSHACC 5 else
  if Z.eqb op 16 then PUSHACC 6 else
  if Z.eqb op 17 then PUSHACC 7 else
  if Z.eqb op 18 then PUSHACC (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 19 then POP (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 20 then ASSIGN (nat_of_z (znth 0%nat ops)) else
  (* ENVACC1-ENVACC4=21..24, ENVACC=25 *)
  if Z.eqb op 21 then ENVACC 1 else
  if Z.eqb op 22 then ENVACC 2 else
  if Z.eqb op 23 then ENVACC 3 else
  if Z.eqb op 24 then ENVACC 4 else
  if Z.eqb op 25 then ENVACC (nat_of_z (znth 0%nat ops)) else
  (* PUSHENVACC1-PUSHENVACC4=26..29, PUSHENVACC=30 *)
  if Z.eqb op 26 then PUSHENVACC 1 else
  if Z.eqb op 27 then PUSHENVACC 2 else
  if Z.eqb op 28 then PUSHENVACC 3 else
  if Z.eqb op 29 then PUSHENVACC 4 else
  if Z.eqb op 30 then PUSHENVACC (nat_of_z (znth 0%nat ops)) else
  (* PUSH_RETADDR=31 *)
  if Z.eqb op 31 then PUSH_RETADDR (br 0%nat) else
  (* APPLY=32, APPLY1=33, APPLY2=34, APPLY3=35 *)
  if Z.eqb op 32 then APPLY (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 33 then APPLY1 else
  if Z.eqb op 34 then APPLY2 else
  if Z.eqb op 35 then APPLY3 else
  (* APPTERM=36 *)
  if Z.eqb op 36 then APPTERM (nat_of_z (znth 0%nat ops)) (nat_of_z (znth 1%nat ops)) else
  if Z.eqb op 37 then APPTERM1 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 38 then APPTERM2 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 39 then APPTERM3 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 40 then RETURN (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 41 then RESTART else
  if Z.eqb op 42 then GRAB (nat_of_z (znth 0%nat ops)) else
  (* CLOSURE=43: nv, code_ptr. Code target = (w+2) + ops[1]. *)
  if Z.eqb op 43 then
    CLOSURE (nat_of_z (znth 0%nat ops))
            (resolve_branch omap (Z.of_nat (w + 2)%nat) (znth 1%nat ops))
  else
  (* CLOSUREREC=44: nf, nv, code offsets. Code target = (w+3) + ofs[i]. *)
  if Z.eqb op 44 then
    let nf := nat_of_z (znth 0%nat ops) in
    let nv := nat_of_z (znth 1%nat ops) in
    let base := Z.of_nat (w + 3)%nat in
    let fix resolve_list (ofs_list : list Z) : list Z :=
      match ofs_list with
      | [] => []
      | o :: rest => resolve_branch omap base o :: resolve_list rest
      end in
    CLOSUREREC nf nv (resolve_list (skipn 2%nat ops))
  else
  (* OFFSETCLOSUREM3=45, OFFSETCLOSURE0=46, OFFSETCLOSURE3=47, OFFSETCLOSURE=48 *)
  if Z.eqb op 45 then OFFSETCLOSURE (-3) else
  if Z.eqb op 46 then OFFSETCLOSURE 0 else
  if Z.eqb op 47 then OFFSETCLOSURE 3 else
  if Z.eqb op 48 then OFFSETCLOSURE (znth 0%nat ops) else
  (* PUSHOFFSETCLOSUREM3=49, PUSHOFFSETCLOSURE0=50, PUSHOFFSETCLOSURE3=51,
     PUSHOFFSETCLOSURE=52 *)
  if Z.eqb op 49 then PUSHOFFSETCLOSURE (-3) else
  if Z.eqb op 50 then PUSHOFFSETCLOSURE 0 else
  if Z.eqb op 51 then PUSHOFFSETCLOSURE 3 else
  if Z.eqb op 52 then PUSHOFFSETCLOSURE (znth 0%nat ops) else
  (* GETGLOBAL=53, PUSHGETGLOBAL=54 *)
  if Z.eqb op 53 then GETGLOBAL (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 54 then PUSHGETGLOBAL (nat_of_z (znth 0%nat ops)) else
  (* GETGLOBALFIELD=55, PUSHGETGLOBALFIELD=56 *)
  if Z.eqb op 55 then GETGLOBALFIELD (nat_of_z (znth 0%nat ops)) (nat_of_z (znth 1%nat ops)) else
  if Z.eqb op 56 then PUSHGETGLOBALFIELD (nat_of_z (znth 0%nat ops)) (nat_of_z (znth 1%nat ops)) else
  (* SETGLOBAL=57 *)
  if Z.eqb op 57 then SETGLOBAL (nat_of_z (znth 0%nat ops)) else
  (* ATOM0=58, ATOM=59, PUSHATOM0=60, PUSHATOM=61 *)
  if Z.eqb op 58 then ATOM 0 else
  if Z.eqb op 59 then ATOM (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 60 then PUSHATOM 0 else
  if Z.eqb op 61 then PUSHATOM (nat_of_z (znth 0%nat ops)) else
  (* MAKEBLOCK=62, MAKEBLOCK1=63, MAKEBLOCK2=64, MAKEBLOCK3=65 *)
  if Z.eqb op 62 then MAKEBLOCK (nat_of_z (znth 1%nat ops)) (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 63 then MAKEBLOCK1 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 64 then MAKEBLOCK2 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 65 then MAKEBLOCK3 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 66 then MAKEFLOATBLOCK (nat_of_z (znth 0%nat ops)) else
  (* GETFIELD0-GETFIELD3=67..70, GETFIELD=71 *)
  if Z.eqb op 67 then GETFIELD 0 else
  if Z.eqb op 68 then GETFIELD 1 else
  if Z.eqb op 69 then GETFIELD 2 else
  if Z.eqb op 70 then GETFIELD 3 else
  if Z.eqb op 71 then GETFIELD (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 72 then GETFLOATFIELD (nat_of_z (znth 0%nat ops)) else
  (* SETFIELD0-SETFIELD3=73..76, SETFIELD=77 *)
  if Z.eqb op 73 then SETFIELD 0 else
  if Z.eqb op 74 then SETFIELD 1 else
  if Z.eqb op 75 then SETFIELD 2 else
  if Z.eqb op 76 then SETFIELD 3 else
  if Z.eqb op 77 then SETFIELD (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 78 then SETFLOATFIELD (nat_of_z (znth 0%nat ops)) else
  (* VECTLENGTH=79, GETVECTITEM=80, SETVECTITEM=81 *)
  if Z.eqb op 79 then VECTLENGTH else
  if Z.eqb op 80 then GETVECTITEM else
  if Z.eqb op 81 then SETVECTITEM else
  (* GETBYTESCHAR=82, SETBYTESCHAR=83 *)
  if Z.eqb op 82 then GETBYTESCHAR else
  if Z.eqb op 83 then SETBYTESCHAR else
  (* BRANCH=84, BRANCHIF=85, BRANCHIFNOT=86 *)
  if Z.eqb op 84 then BRANCH (br 0%nat) else
  if Z.eqb op 85 then BRANCHIF (br 0%nat) else
  if Z.eqb op 86 then BRANCHIFNOT (br 0%nat) else
  (* SWITCH=87 *)
  if Z.eqb op 87 then
    let sizes := znth 0%nat ops in
    let nc := Z.to_nat (Z.land sizes (Z.ones 16)) in
    let nb := Z.to_nat (Z.shiftr sizes 16) in
    let base := Z.of_nat (w + 2)%nat in
    let fix resolve_n (start : nat) (count : nat) : list Z :=
      match count with
      | O => []
      | S count' =>
        resolve_branch omap base (znth (S start) ops) ::
          resolve_n (S start) count'
      end in
    (* table entries start at ops[1]: first nc are consts, next nb are blocks *)
    SWITCH nc nb (resolve_n 0%nat nc) (resolve_n nc nb)
  else
  (* BOOLNOT=88 *)
  if Z.eqb op 88 then BOOLNOT else
  (* PUSHTRAP=89, POPTRAP=90, RAISE=91 *)
  if Z.eqb op 89 then PUSHTRAP (br 0%nat) else
  if Z.eqb op 90 then POPTRAP else
  if Z.eqb op 91 then RAISE else
  (* CHECK_SIGNALS=92 *)
  if Z.eqb op 92 then CHECK_SIGNALS else
  (* C_CALL1-C_CALL5=93..97, C_CALLN=98 *)
  if Z.eqb op 93 then C_CALL 1 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 94 then C_CALL 2 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 95 then C_CALL 3 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 96 then C_CALL 4 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 97 then C_CALL 5 (nat_of_z (znth 0%nat ops)) else
  if Z.eqb op 98 then C_CALL (nat_of_z (znth 0%nat ops)) (nat_of_z (znth 1%nat ops)) else
  (* CONST0-CONST3=99..102, CONSTINT=103 *)
  if Z.eqb op 99 then CONSTINT 0 else
  if Z.eqb op 100 then CONSTINT 1 else
  if Z.eqb op 101 then CONSTINT 2 else
  if Z.eqb op 102 then CONSTINT 3 else
  if Z.eqb op 103 then CONSTINT (znth 0%nat ops) else
  (* PUSHCONST0-PUSHCONST3=104..107, PUSHCONSTINT=108 *)
  if Z.eqb op 104 then PUSHCONSTINT 0 else
  if Z.eqb op 105 then PUSHCONSTINT 1 else
  if Z.eqb op 106 then PUSHCONSTINT 2 else
  if Z.eqb op 107 then PUSHCONSTINT 3 else
  if Z.eqb op 108 then PUSHCONSTINT (znth 0%nat ops) else
  (* NEGINT=109..ASRINT=120 *)
  if Z.eqb op 109 then NEGINT else
  if Z.eqb op 110 then ADDINT else
  if Z.eqb op 111 then SUBINT else
  if Z.eqb op 112 then MULINT else
  if Z.eqb op 113 then DIVINT else
  if Z.eqb op 114 then MODINT else
  if Z.eqb op 115 then ANDINT else
  if Z.eqb op 116 then ORINT else
  if Z.eqb op 117 then XORINT else
  if Z.eqb op 118 then LSLINT else
  if Z.eqb op 119 then LSRINT else
  if Z.eqb op 120 then ASRINT else
  (* EQ=121..GEINT=126 *)
  if Z.eqb op 121 then EQ else
  if Z.eqb op 122 then NEQ else
  if Z.eqb op 123 then LTINT else
  if Z.eqb op 124 then LEINT else
  if Z.eqb op 125 then GTINT else
  if Z.eqb op 126 then GEINT else
  (* OFFSETINT=127, OFFSETREF=128, ISINT=129 *)
  if Z.eqb op 127 then OFFSETINT (znth 0%nat ops) else
  if Z.eqb op 128 then OFFSETREF (znth 0%nat ops) else
  if Z.eqb op 129 then ISINT else
  (* GETMETHOD=130 *)
  if Z.eqb op 130 then GETMETHOD else
  (* BEQ=131..BGEINT=136 *)
  if Z.eqb op 131 then BEQ (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 132 then BNEQ (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 133 then BLTINT (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 134 then BLEINT (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 135 then BGTINT (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 136 then BGEINT (znth 0%nat ops) (br 1%nat) else
  (* ULTINT=137, UGEINT=138 *)
  if Z.eqb op 137 then ULTINT else
  if Z.eqb op 138 then UGEINT else
  (* BULTINT=139, BUGEINT=140 *)
  if Z.eqb op 139 then BULTINT (znth 0%nat ops) (br 1%nat) else
  if Z.eqb op 140 then BUGEINT (znth 0%nat ops) (br 1%nat) else
  (* GETPUBMET=141, GETDYNMET=142 *)
  if Z.eqb op 141 then GETPUBMET (znth 0%nat ops) else
  if Z.eqb op 142 then GETDYNMET else
  (* STOP=143 *)
  if Z.eqb op 143 then STOP else
  (* EVENT=144, BREAK=145: not modeled (debugger-only), decode as STOP *)
  if Z.eqb op 144 then STOP else
  if Z.eqb op 145 then STOP else
  (* RERAISE=146, RAISE_NOTRACE=147 *)
  if Z.eqb op 146 then RERAISE else
  if Z.eqb op 147 then RAISE_NOTRACE else
  (* GETSTRINGCHAR=148 *)
  if Z.eqb op 148 then GETSTRINGCHAR else
  (* 149-152: OCaml 5.x effect handlers, not modeled, decode as STOP *)
  (* Unknown opcode *)
  STOP.

(* ------------------------------------------------------------------ *)
(* Top-level decode: two-pass approach                                 *)
(* ------------------------------------------------------------------ *)

Definition resolve_all (raws : list raw_instr) : list instruction :=
  let omap := build_offset_map raws in
  map (resolve_one omap) raws.

Definition decode_bytecode (data : list Z) (code_offset : nat)
    (code_length : nat) : list instruction :=
  resolve_all (decode_raw data code_offset code_length).

Definition load_code_section (data : list Z) (data_len : nat)
    : option (list instruction) :=
  let secs := parse_sections data data_len in
  match find_section secs CODE_name with
  | Some s => Some (decode_bytecode data s.(sec_offset) s.(sec_length))
  | None => None
  end.
