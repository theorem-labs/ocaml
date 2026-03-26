open Interp_extracted

let show_instr = function
  | ACC n -> Printf.sprintf "ACC %d" n
  | PUSH -> "PUSH"
  | PUSHACC n -> Printf.sprintf "PUSHACC %d" n
  | CONSTINT n -> Printf.sprintf "CONSTINT %d" n
  | PUSHCONSTINT n -> Printf.sprintf "PUSHCONSTINT %d" n
  | BULTINT (n,t) -> Printf.sprintf "BULTINT(%d,%d)" n t
  | BUGEINT (n,t) -> Printf.sprintf "BUGEINT(%d,%d)" n t
  | SWITCH (nc,nb,ct,_) -> Printf.sprintf "SWITCH(nc=%d,nb=%d,ct=[%s])" nc nb (String.concat "," (List.map string_of_int ct))
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
  | CLOSURE (nv,ofs) -> Printf.sprintf "CLOSURE(%d,%d)" nv ofs
  | STOP -> "STOP"
  | GETFIELD n -> Printf.sprintf "GETFIELD %d" n
  | SETFIELD n -> Printf.sprintf "SETFIELD %d" n
  | GETGLOBAL n -> Printf.sprintf "GETGLOBAL %d" n
  | SETGLOBAL n -> Printf.sprintf "SETGLOBAL %d" n
  | PUSHGETGLOBAL n -> Printf.sprintf "PUSHGETGLOBAL %d" n
  | MAKEBLOCK (t,sz) -> Printf.sprintf "MAKEBLOCK(%d,%d)" t sz
  | MAKEBLOCK1 t -> Printf.sprintf "MAKEBLOCK1 %d" t
  | MAKEBLOCK2 t -> Printf.sprintf "MAKEBLOCK2 %d" t
  | MAKEBLOCK3 t -> Printf.sprintf "MAKEBLOCK3 %d" t
  | GETGLOBALFIELD (n,p) -> Printf.sprintf "GETGLOBALFIELD(%d,%d)" n p
  | PUSHGETGLOBALFIELD (n,p) -> Printf.sprintf "PUSHGETGLOBALFIELD(%d,%d)" n p
  | POP n -> Printf.sprintf "POP %d" n
  | C_CALL (n,p) -> Printf.sprintf "C_CALL(%d,%d)" n p
  | APPTERM (n,s) -> Printf.sprintf "APPTERM(%d,%d)" n s
  | APPTERM1 s -> Printf.sprintf "APPTERM1 %d" s
  | APPTERM2 s -> Printf.sprintf "APPTERM2 %d" s
  | APPTERM3 s -> Printf.sprintf "APPTERM3 %d" s
  | APPLY2 -> "APPLY2"
  | APPLY3 -> "APPLY3"
  | GETMETHOD -> "GETMETHOD"
  | GETPUBMET t -> Printf.sprintf "GETPUBMET %d" t
  | GETDYNMET -> "GETDYNMET"
  | PUSHTRAP t -> Printf.sprintf "PUSHTRAP %d" t
  | POPTRAP -> "POPTRAP"
  | RAISE -> "RAISE"
  | RERAISE -> "RERAISE"
  | RAISE_NOTRACE -> "RAISE_NOTRACE"
  | ISINT -> "ISINT"
  | NEGINT -> "NEGINT"
  | ATOM n -> Printf.sprintf "ATOM %d" n
  | PUSHATOM n -> Printf.sprintf "PUSHATOM %d" n
  | ENVACC n -> Printf.sprintf "ENVACC %d" n
  | PUSHENVACC n -> Printf.sprintf "PUSHENVACC %d" n
  | OFFSETCLOSURE n -> Printf.sprintf "OFFSETCLOSURE %d" n
  | PUSHOFFSETCLOSURE n -> Printf.sprintf "PUSHOFFSETCLOSURE %d" n
  | RESTART -> "RESTART"
  | CLOSUREREC (nf,nv,_) -> Printf.sprintf "CLOSUREREC(%d,%d)" nf nv
  | VECTLENGTH -> "VECTLENGTH"
  | GETVECTITEM -> "GETVECTITEM"
  | SETVECTITEM -> "SETVECTITEM"
  | GETBYTESCHAR -> "GETBYTESCHAR"
  | SETBYTESCHAR -> "SETBYTESCHAR"
  | GETSTRINGCHAR -> "GETSTRINGCHAR"
  | BOOLNOT -> "BOOLNOT"
  | CHECK_SIGNALS -> "CHECK_SIGNALS"
  | GETFLOATFIELD n -> Printf.sprintf "GETFLOATFIELD %d" n
  | SETFLOATFIELD n -> Printf.sprintf "SETFLOATFIELD %d" n
  | MAKEFLOATBLOCK n -> Printf.sprintf "MAKEFLOATBLOCK %d" n
  | OFFSETREF n -> Printf.sprintf "OFFSETREF %d" n
  | PUSH_RETADDR t -> Printf.sprintf "PUSH_RETADDR %d" t
  | ASSIGN n -> Printf.sprintf "ASSIGN %d" n
  | MULINT -> "MULINT"
  | DIVINT -> "DIVINT"
  | MODINT -> "MODINT"
  | ANDINT -> "ANDINT"
  | ORINT -> "ORINT"
  | XORINT -> "XORINT"
  | LSLINT -> "LSLINT"
  | LSRINT -> "LSRINT"
  | ASRINT -> "ASRINT"
  | BLEINT (n,t) -> Printf.sprintf "BLEINT(%d,%d)" n t
  | BLTINT (n,t) -> Printf.sprintf "BLTINT(%d,%d)" n t
  | BGEINT (n,t) -> Printf.sprintf "BGEINT(%d,%d)" n t
  | BGTINT (n,t) -> Printf.sprintf "BGTINT(%d,%d)" n t
  | BEQ (n,t) -> Printf.sprintf "BEQ(%d,%d)" n t
  | BNEQ (n,t) -> Printf.sprintf "BNEQ(%d,%d)" n t
  | ULTINT -> "ULTINT"
  | UGEINT -> "UGEINT"
  | EVENT -> "EVENT"
  | BREAK -> "BREAK"
  | PERFORM -> "PERFORM"
  | RESUME -> "RESUME"
  | RESUMETERM n -> Printf.sprintf "RESUMETERM %d" n
  | REPERFORMTERM n -> Printf.sprintf "REPERFORMTERM %d" n
  | _ -> "truly_other"

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
