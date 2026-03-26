open Test_common

let () =
  let path = "/workspaces/theorem-work/theorem-ocaml/system-ocaml-compiler/testsuite/tests/basic/patmatch_for_multiple.ml" in
  (* Mimic test_file exactly *)
  with_temp_dir (fun dir ->
    let test_dir = Filename.dirname path in
    let header = 
      (* Parse header manually from file *)
      let ic = open_in path in
      let buf = Bytes.create 4096 in
      let n = input ic buf 0 4096 in
      close_in ic;
      Printf.printf "Header bytes 0..50: %S\n" (Bytes.sub_string buf 0 (min 50 n));
      ()
    in
    ignore header;
    let exe = Filename.concat dir "test.byte" in
    let all_files = path in
    let compile_cmd = Printf.sprintf "ocamlc -I %s -o %s %s 2>/dev/null" test_dir exe all_files in
    Printf.printf "compile_cmd: %s\n" compile_cmd;
    let ret = Sys.command compile_cmd in
    Printf.printf "ret=%d exists=%b\n" ret (Sys.file_exists exe);
    if ret <> 0 then
      Printf.printf "Would Skip: compile failed\n"
    else
      Printf.printf "Would proceed to run\n"
  )
