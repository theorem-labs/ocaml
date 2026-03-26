(* loader.ml - [TRUSTED] Bytecode loader. *)

open Interp_extracted

let read_file filename =
  let ic = open_in_bin filename in
  let n = in_channel_length ic in
  let data = Bytes.create n in
  really_input ic data 0 n; close_in ic; data

let read_u32_le data off =
  Char.code (Bytes.get data off) lor
  (Char.code (Bytes.get data (off+1)) lsl 8) lor
  (Char.code (Bytes.get data (off+2)) lsl 16) lor
  (Char.code (Bytes.get data (off+3)) lsl 24)

let read_i32_le data off =
  let u = read_u32_le data off in
  if u land 0x80000000 <> 0 then u lor (lnot 0xFFFFFFFF) else u

let read_u32_be data off =
  (Char.code (Bytes.get data off) lsl 24) lor
  (Char.code (Bytes.get data (off+1)) lsl 16) lor
  (Char.code (Bytes.get data (off+2)) lsl 8) lor
  Char.code (Bytes.get data (off+3))

type section = { name : string; offset : int; length : int }

let parse_sections data =
  let len = Bytes.length data in
  let num_sections = read_u32_be data (len - 16) in
  let toc_offset = len - 16 - (num_sections * 8) in
  let total_data = ref 0 in
  for i = 0 to num_sections - 1 do
    total_data := !total_data + read_u32_be data (toc_offset + i * 8 + 4)
  done;
  let data_start = toc_offset - !total_data in
  let current = ref data_start in
  Array.init num_sections (fun i ->
    let entry = toc_offset + i * 8 in
    let name = Bytes.sub_string data entry 4 in
    let slen = read_u32_be data (entry + 4) in
    let off = !current in
    current := !current + slen;
    { name; offset = off; length = slen })

let find_section sections name =
  let r = ref None in
  Array.iter (fun s -> if s.name = name then r := Some s) sections; !r

(* === Opcode numbering from opcodes.h (exact) === *)
(* Number of extra operand words for each opcode *)
let operand_count = Array.make 256 0
let () =
  (* 1-operand instructions *)
  List.iter (fun op -> operand_count.(op) <- 1)
    [ 8; 18; 19; 20; 25; 30; 31; 32; 37; 38; 39; 40; 42;
      48; 52; 53; 54; 57; 59; 61; 63; 64; 65; 66; 71; 72; 77; 78;
      84; 85; 86; 89;
      93; 94; 95; 96; 97;
      103; 108;
      127; 128;
      151; 152 (* RESUMETERM, REPERFORMTERM *) ];
  (* 2-operand instructions *)
  List.iter (fun op -> operand_count.(op) <- 2)
    [ 36; 43; 55; 56; 62; 98;
      131; 132; 133; 134; 135; 136;  (* BEQ..BGEINT *)
      139; 140  (* BULTINT, BUGEINT *) ];
  (* Special: SWITCH=87, CLOSUREREC=44, GETPUBMET=141 handled separately *)
  ()

let decode_raw data code_offset code_length =
  let raw = ref [] and offs = ref [] in
  let pos = ref 0 in
  while !pos < code_length do
    let w = !pos / 4 in
    offs := w :: !offs;
    let op = read_u32_le data (code_offset + !pos) in
    pos := !pos + 4;
    let rd () = let v = read_i32_le data (code_offset + !pos) in pos := !pos + 4; v in
    let operands =
      if op = 87 then (* SWITCH *)
        let sizes = rd () in
        let n = (sizes land 0xFFFF) + (sizes lsr 16) in
        sizes :: List.init n (fun _ -> rd ())
      else if op = 44 then (* CLOSUREREC *)
        let nf = rd () in let nv = rd () in
        nf :: nv :: List.init nf (fun _ -> rd ())
      else if op = 141 then (* GETPUBMET: tag + cache *)
        let t = rd () in let _ = rd () in [t]
      else if op < 256 then
        List.init operand_count.(op) (fun _ -> rd ())
      else begin
        Printf.eprintf "Unknown opcode %d at word %d\n" op w; []
      end
    in
    raw := (op, operands) :: !raw
  done;
  (List.rev !raw, Array.of_list (List.rev !offs))

let resolve woffs omap wpos rel =
  let target = wpos + rel in
  match Hashtbl.find_opt omap target with
  | Some i -> i
  | None -> Printf.eprintf "Warn: unresolved branch word %d -> %d\n" wpos target; 0

let decode data code_off code_len =
  let raw, woffs = decode_raw data code_off code_len in
  let omap = Hashtbl.create (Array.length woffs) in
  Array.iteri (fun i w -> Hashtbl.replace omap w i) woffs;
  List.mapi (fun i (op, ops) ->
    let w = woffs.(i) in
    (* For branches: target = position_of_offset + offset value.
       After dispatch, pc = w+1. For opcodes that consume operands with *pc++,
       the offset word is at w+1+n (nth operand position). *)
    let br n = resolve woffs omap (w + 1 + n) (List.nth ops n) in
    match op, ops with
    (* ACC0-7=0..7, ACC=8 *)
    | (0|1|2|3|4|5|6|7), [] -> ACC op
    | 8, [n] -> ACC n
    | 9, [] -> PUSH
    (* PUSHACC0-7=10..17, PUSHACC=18 *)
    | (10|11|12|13|14|15|16|17), [] -> PUSHACC (op - 10)
    | 18, [n] -> PUSHACC n
    | 19, [n] -> POP n | 20, [n] -> ASSIGN n
    (* ENVACC1-4=21..24, ENVACC=25 *)
    | (21|22|23|24), [] -> ENVACC (op - 20)
    | 25, [n] -> ENVACC n
    (* PUSHENVACC1-4=26..29, PUSHENVACC=30 *)
    | (26|27|28|29), [] -> PUSHENVACC (op - 25)
    | 30, [n] -> PUSHENVACC n
    | 31, [_] -> PUSH_RETADDR (br 0)
    | 32, [n] -> APPLY n | 33, [] -> APPLY1 | 34, [] -> APPLY2 | 35, [] -> APPLY3
    | 36, [n; s] -> APPTERM (n, s)
    | 37, [s] -> APPTERM1 s | 38, [s] -> APPTERM2 s | 39, [s] -> APPTERM3 s
    | 40, [n] -> RETURN n | 41, [] -> RESTART | 42, [n] -> GRAB n
    | 43, [nv; _] ->
      (* Code_val = pc + ofs - 1 where pc = w+3; target = (w+2) + ofs *)
      CLOSURE (nv, resolve woffs omap (w + 2) (List.nth ops 1))
    | 44, nf :: nv :: ofs_list ->
      (* Code_val = pc + pc[i] where pc = w+3 after reading nfuncs, nvars *)
      CLOSUREREC (nf, nv, List.map (fun o -> resolve woffs omap (w + 3) o) ofs_list)
    (* OFFSETCLOSUREM3=45, OFFSETCLOSURE0=46, OFFSETCLOSURE3=47, OFFSETCLOSURE=48 *)
    | 45, [] -> OFFSETCLOSURE (-3) | 46, [] -> OFFSETCLOSURE 0
    | 47, [] -> OFFSETCLOSURE 3 | 48, [n] -> OFFSETCLOSURE n
    | 49, [] -> PUSHOFFSETCLOSURE (-3) | 50, [] -> PUSHOFFSETCLOSURE 0
    | 51, [] -> PUSHOFFSETCLOSURE 3 | 52, [n] -> PUSHOFFSETCLOSURE n
    | 53, [n] -> GETGLOBAL n | 54, [n] -> PUSHGETGLOBAL n
    | 55, [n; p] -> GETGLOBALFIELD (n, p) | 56, [n; p] -> PUSHGETGLOBALFIELD (n, p)
    | 57, [n] -> SETGLOBAL n
    | 58, [] -> ATOM 0 | 59, [t] -> ATOM t | 60, [] -> PUSHATOM 0 | 61, [t] -> PUSHATOM t
    | 62, [sz; t] -> MAKEBLOCK (t, sz) | 63, [t] -> MAKEBLOCK1 t
    | 64, [t] -> MAKEBLOCK2 t | 65, [t] -> MAKEBLOCK3 t | 66, [s] -> MAKEFLOATBLOCK s
    | 67, [] -> GETFIELD 0 | 68, [] -> GETFIELD 1 | 69, [] -> GETFIELD 2
    | 70, [] -> GETFIELD 3 | 71, [n] -> GETFIELD n | 72, [n] -> GETFLOATFIELD n
    | 73, [] -> SETFIELD 0 | 74, [] -> SETFIELD 1 | 75, [] -> SETFIELD 2
    | 76, [] -> SETFIELD 3 | 77, [n] -> SETFIELD n | 78, [n] -> SETFLOATFIELD n
    | 79, [] -> VECTLENGTH | 80, [] -> GETVECTITEM | 81, [] -> SETVECTITEM
    | 82, [] -> GETBYTESCHAR | 83, [] -> SETBYTESCHAR
    | 84, [_] -> BRANCH (br 0) | 85, [_] -> BRANCHIF (br 0) | 86, [_] -> BRANCHIFNOT (br 0)
    | 87, sizes :: tbl ->
      let nc = sizes land 0xFFFF in let nb = sizes lsr 16 in
      (* pc points to table start (w+2) after reading sizes; target = (w+2) + entry *)
      let base = w + 2 in
      let ct = List.init nc (fun j -> resolve woffs omap base (List.nth tbl j)) in
      let bt = List.init nb (fun j -> resolve woffs omap base (List.nth tbl (nc + j))) in
      SWITCH (nc, nb, ct, bt)
    | 88, [] -> BOOLNOT
    | 89, [_] -> PUSHTRAP (br 0) | 90, [] -> POPTRAP | 91, [] -> RAISE
    | 92, [] -> CHECK_SIGNALS
    (* C_CALL1=93..C_CALL5=97, C_CALLN=98 *)
    | 93, [p] -> C_CALL (1, p) | 94, [p] -> C_CALL (2, p) | 95, [p] -> C_CALL (3, p)
    | 96, [p] -> C_CALL (4, p) | 97, [p] -> C_CALL (5, p) | 98, [n; p] -> C_CALL (n, p)
    (* CONST0=99, CONST1=100, CONST2=101, CONST3=102, CONSTINT=103 *)
    | 99, [] -> CONSTINT 0 | 100, [] -> CONSTINT 1 | 101, [] -> CONSTINT 2
    | 102, [] -> CONSTINT 3 | 103, [n] -> CONSTINT n
    (* PUSHCONST0=104, ..., PUSHCONSTINT=108 *)
    | 104, [] -> PUSHCONSTINT 0 | 105, [] -> PUSHCONSTINT 1
    | 106, [] -> PUSHCONSTINT 2 | 107, [] -> PUSHCONSTINT 3 | 108, [n] -> PUSHCONSTINT n
    (* NEGINT=109, ADDINT=110, ..., ASRINT=120 *)
    | 109, [] -> NEGINT | 110, [] -> ADDINT | 111, [] -> SUBINT
    | 112, [] -> MULINT | 113, [] -> DIVINT | 114, [] -> MODINT
    | 115, [] -> ANDINT | 116, [] -> ORINT | 117, [] -> XORINT
    | 118, [] -> LSLINT | 119, [] -> LSRINT | 120, [] -> ASRINT
    (* EQ=121, ..., GEINT=126 *)
    | 121, [] -> EQ | 122, [] -> NEQ | 123, [] -> LTINT | 124, [] -> LEINT
    | 125, [] -> GTINT | 126, [] -> GEINT
    (* OFFSETINT=127, OFFSETREF=128, ISINT=129 *)
    | 127, [n] -> OFFSETINT n | 128, [n] -> OFFSETREF n | 129, [] -> ISINT
    (* GETMETHOD=130 *)
    | 130, [] -> GETMETHOD
    (* BEQ=131, ..., BGEINT=136 *)
    | 131, [n; _] -> BEQ (n, br 1) | 132, [n; _] -> BNEQ (n, br 1)
    | 133, [n; _] -> BLTINT (n, br 1) | 134, [n; _] -> BLEINT (n, br 1)
    | 135, [n; _] -> BGTINT (n, br 1) | 136, [n; _] -> BGEINT (n, br 1)
    (* ULTINT=137, UGEINT=138 *)
    | 137, [] -> ULTINT | 138, [] -> UGEINT
    (* BULTINT=139, BUGEINT=140 *)
    | 139, [n; _] -> BULTINT (n, br 1) | 140, [n; _] -> BUGEINT (n, br 1)
    (* GETPUBMET=141, GETDYNMET=142 *)
    | 141, [t] -> GETPUBMET t | 142, [] -> GETDYNMET
    (* STOP=143 *)
    | 143, [] -> STOP
    (* EVENT=144, BREAK=145 *)
    | 144, [] -> EVENT | 145, [] -> BREAK
    (* RERAISE=146, RAISE_NOTRACE=147 *)
    | 146, [] -> RERAISE | 147, [] -> RAISE_NOTRACE
    (* GETSTRINGCHAR=148 *)
    | 148, [] -> GETSTRINGCHAR
    (* PERFORM=149, RESUME=150, RESUMETERM=151, REPERFORMTERM=152 *)
    | 149, [] -> PERFORM | 150, [] -> RESUME
    | 151, [n] -> RESUMETERM n | 152, [n] -> REPERFORMTERM n
    | _ -> Printf.eprintf "Unmatched opcode %d\n" op; STOP
  ) raw

let load_bytecode_from_sections data sections =
  match find_section sections "CODE" with
  | Some s -> decode data s.offset s.length
  | None -> failwith "No CODE section"

let load_bytecode filename =
  let data = read_file filename in
  load_bytecode_from_sections data (parse_sections data)
