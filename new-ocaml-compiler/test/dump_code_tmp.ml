open Interp_extracted

let show_instr = function
  | ACC n -> Printf.sprintf "ACC %d" n
  | PUSH -> "PUSH"
  | PUSHACC n -> Printf.sprintf "PUSHACC %d" n
  | CONSTINT n -> Printf.sprintf "CONSTINT %d" n
  | PUSHCONSTINT n -> Printf.sprintf "PUSHCONSTINT %d" n
  | BULTINT (n,t) -> Printf.sprintf "BULTINT(%d,%d)" n t
  | BUGEINT (n,t) -> Printf.sprintf "BUGEINT(%d,%d)" n t
  | SWITCH (nc,nb,ct,bt) -> Printf.sprintf "SWITCH(nc=%d,nb=%d,ct=%s)" nc nb (String.concat "," (List.map string_of_int ct))
  | OFFSETINT n -> Printf.sprintf "OFFSETINT %d" n
  | BRANCHIF t -> Printf.sprintf "BRANCHIF %d" t
  | BRANCHIFNOT t -> Printf.sprintf "BRANCHIFNOT %d" t
  | BRANCH t -> Printf.sprintf "BRANCH %d" t
  | RETURN n -> Printf.sprintf "RETURN %d" n
  | APPLY n -> Printf.sprintf "APPLY %d" n
  | APPLY1 -> "APPLY1"
  | GRAB n -> Printf.sprintf "GRAB %d" n
  | ULTINT -> "ULTINT"
  | UGEINT -> "UGEINT"
  | EQ -> "EQ"
  | NEQ -> "NEQ"
  | LTINT -> "LTINT"
  | GTINT -> "GTINT"
  | LEINT -> "LEINT"
  | GEINT -> "GEINT"
  | ADDINT -> "ADDINT"
  | SUBINT -> "SUBINT"
  | CONSTINT n -> Printf.sprintf "CONSTINT %d" n
  | CLOSURE (nv,ofs) -> Printf.sprintf "CLOSURE(%d,%d)" nv ofs
  | STOP -> "STOP"
  | _ -> "other"

let () =
  let data = Loader.read_file Sys.argv.(1) in
  let sections = Loader.parse_sections data in
  let code = Loader.load_bytecode_from_sections data sections in
  let start = int_of_string Sys.argv.(2) in
  let len = int_of_string Sys.argv.(3) in
  for i = start to start + len - 1 do
    match List.nth_opt code i with
    | Some instr -> Printf.printf "%d: %s\n" i (show_instr instr)
    | None -> Printf.printf "%d: END\n" i
  done
