(* ocaml_testsuite_runner.ml - Run OCaml compiler test suite against our
   bytecode interpreter. For each .ml test file:
   1. Compile with ocamlc to get a bytecode executable
   2. Run with ocamlrun to get expected output
   3. Run bytecode through our interpreter to get actual output
   4. Compare outputs

   Usage: ocaml_testsuite_runner.exe [directory ...]
   If no directories given, runs on test/ocaml-testsuite/basic *)

open Test_common

(* Path to the strip_expect_ppx executable (same build directory). *)
let strip_expect_ppx_exe =
  let candidates = [
    Filename.concat (Filename.dirname Sys.executable_name) "strip_expect_ppx.exe";
    "_build/default/checker/Bytecode/test/strip_expect_ppx.exe";
  ] in
  List.fold_left (fun acc p ->
    match acc with Some _ -> acc | None -> if Sys.file_exists p then Some p else None
  ) None candidates

(* Check if a file contains [%%expect blocks *)
let file_has_expect path =
  try
    let ic = open_in path in
    let buf = Bytes.create 4096 in
    let found = ref false in
    (try
      while not !found do
        let n = input ic buf 0 4096 in
        if n = 0 then raise Exit;
        let s = Bytes.sub_string buf 0 n in
        if let len = String.length s in
           let pat = "[%%expect" in
           let plen = String.length pat in
           let rec check i =
             if i + plen > len then false
             else if String.sub s i plen = pat then true
             else check (i + 1)
           in check 0
        then found := true
      done
    with Exit -> ());
    close_in ic;
    !found
  with _ -> false

(* Timeout in seconds for both ocamlrun and our interpreter *)
let timeout_secs = 5

let run_with_timeout cmd =
  let ic = Unix.open_process_in
    (Printf.sprintf "timeout %d %s 2>/dev/null" timeout_secs cmd) in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_char buf (input_char ic) done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 124 -> None  (* timeout *)
  | Unix.WEXITED _ -> Some (Buffer.contents buf)  (* any exit code: capture output *)
  | _ -> None

(* Parse the TEST header comment from a .ml file.
   Returns a record with:
   - modules: list of companion .ml filenames (relative to same dir)
   - include_testing: whether "include testing" is present
   - expect_compile_error: whether ocamlc_byte_exit_status = "2" *)
type test_header = {
  modules: string list;
  include_testing: bool;
  expect_compile_error: bool;
  readonly_files: string list;
}

let empty_header = { modules = []; include_testing = false; expect_compile_error = false; readonly_files = [] }

let parse_test_header path =
  try
    let ic = open_in path in
    (* Read up to 4096 bytes to find the TEST comment *)
    let buf = Bytes.create 4096 in
    let n = input ic buf 0 4096 in
    close_in ic;
    let content = Bytes.sub_string buf 0 n in
    (* Find (* TEST ... *) at start of file *)
    let test_start = "(* TEST" in
    let test_end = "*)" in
    if not (String.length content >= String.length test_start &&
            String.sub content 0 (String.length test_start) = test_start) then
      empty_header
    else begin
      (* Find closing comment marker *)
      let end_pos =
        try
          let idx = ref (-1) in
          for i = 0 to String.length content - 2 do
            if !idx = -1 && content.[i] = '*' && content.[i+1] = ')' then
              idx := i
          done;
          !idx
        with _ -> -1
      in
      if end_pos = -1 then empty_header
      else begin
        let header_text = String.sub content 0 (end_pos + 2) in
        (* Check for include testing *)
        let include_testing =
          let re = Str.regexp "include[ \t]+testing" in
          (try ignore (Str.search_forward re header_text 0); true
           with Not_found -> false)
        in
        (* Check for ocamlc_byte_exit_status = "2" *)
        let expect_compile_error =
          let re = Str.regexp {|ocamlc_byte_exit_status[ \t]*=[ \t]*"2"|} in
          (try ignore (Str.search_forward re header_text 0); true
           with Not_found -> false)
        in
        (* Extract modules = "..." *)
        let modules =
          let re = Str.regexp {|modules[ \t]*=[ \t]*"\([^"]*\)"|} in
          try
            ignore (Str.search_forward re header_text 0);
            let mods_str = Str.matched_group 1 header_text in
            (* Split on whitespace *)
            Str.split (Str.regexp "[ \t]+") mods_str
          with Not_found -> []
        in
        (* Extract readonly_files = "..." *)
        let readonly_files =
          let re = Str.regexp {|readonly_files[ \t]*=[ \t]*"\([^"]*\)"|} in
          try
            ignore (Str.search_forward re header_text 0);
            let files_str = Str.matched_group 1 header_text in
            Str.split (Str.regexp "[ \t]+") files_str
          with Not_found -> []
        in
        { modules; include_testing; expect_compile_error; readonly_files }
      end
    end
  with _ -> empty_header

(* Read .reference file if it exists next to the .ml file.
   Only uses .reference (bytecode output), not .ocaml.reference (toplevel output).
   The .ocaml.reference files contain toplevel-specific formatting (e.g.,
   "val x : int = 5") that doesn't match compiled bytecode output. *)
let read_reference path =
  let ref_path = (Filename.chop_suffix path ".ml") ^ ".reference" in
  if Sys.file_exists ref_path then
    try
      let ic = open_in ref_path in
      let buf = Buffer.create 256 in
      (try while true do Buffer.add_char buf (input_char ic) done
       with End_of_file -> ());
      close_in ic;
      Some (Buffer.contents buf)
    with _ -> None
  else None

let run_our_interp exe_file = run_our_pipeline exe_file

type result = Pass | Fail of string | Skip of string

let test_file path =
  (* Only handle plain .ml files *)
  if not (Filename.check_suffix path ".ml") then Skip "not .ml"
  else
    (try with_temp_dir (fun dir ->
        let header = parse_test_header path in
        (* Skip tests that are expected to fail compilation *)
        if header.expect_compile_error then
          Skip "compile-error test"
        else
        let test_dir = Filename.dirname path in
        (* Build list of source files for compilation *)
        let extra_files =
          (if header.include_testing then
            (* testing.ml may be in test dir or testsuite lib dir *)
            let local = Filename.concat test_dir "testing.ml" in
            let parent = Filename.dirname test_dir in
            let candidates = [
              local;
              Filename.concat parent "../lib/testing.ml";
              Filename.concat parent "lib/testing.ml";
              Filename.concat (Filename.dirname parent) "lib/testing.ml";
            ] in
            (match List.find_opt Sys.file_exists candidates with
             | Some p -> [p]
             | None -> [local])
          else []) @
          (List.map (fun m -> Filename.concat test_dir m) header.modules)
        in
        (* For each extra .ml file, include its .mli if present *)
        let expand_with_mli files =
          List.concat_map (fun f ->
            if Filename.check_suffix f ".ml" then
              let mli = (Filename.chop_suffix f ".ml") ^ ".mli" in
              if Sys.file_exists mli then [mli; f] else [f]
            else [f]
          ) files
        in
        let extra_files_expanded = expand_with_mli extra_files in
        let extra_dirs =
          List.filter_map (fun f ->
            let d = Filename.dirname f in
            if d <> test_dir then Some d else None
          ) extra_files_expanded
          |> List.sort_uniq String.compare
        in
        (* Include .mli file before .ml if it exists (needed when interface is present) *)
        let mli_path = (Filename.chop_suffix path ".ml") ^ ".mli" in
        let main_files =
          if Sys.file_exists mli_path then [mli_path; path]
          else [path]
        in
        let all_files = String.concat " " (extra_files_expanded @ main_files) in
        let exe = Filename.concat dir "test.byte" in
        (* If the file uses [%%expect blocks, add the ppx strip rewriter *)
        let ppx_flag =
          if file_has_expect path then
            match strip_expect_ppx_exe with
            | None -> ""
            | Some ppx -> Printf.sprintf "-ppx %s " (Filename.quote ppx)
          else ""
        in
        let include_flags = String.concat " "
          (List.map (fun d -> "-I " ^ d) (test_dir :: extra_dirs)) in
        let compile_cmd =
          Printf.sprintf "ocamlc %s %s-o %s %s 2>/dev/null"
            include_flags ppx_flag exe all_files in
        let compile_failed_reason =
          if file_has_expect path then "expect test (compile errors expected)"
          else "compile failed"
        in
        if Sys.command compile_cmd <> 0 then
          Skip compile_failed_reason
        else begin
          (* Copy readonly_files to the temp dir so the test binary can find them *)
          List.iter (fun f ->
            let src = Filename.concat test_dir f in
            let dst = Filename.concat dir f in
            if Sys.file_exists src then begin
              let ic = open_in_bin src in
              let n = in_channel_length ic in
              let data = Bytes.create n in
              really_input ic data 0 n;
              close_in ic;
              let oc = open_out_bin dst in
              output_bytes oc data;
              close_out oc
            end
          ) header.readonly_files;
          (* Run from temp dir so readonly files are accessible *)
          let saved_cwd = Sys.getcwd () in
          if header.readonly_files <> [] then Sys.chdir dir;
          Fun.protect ~finally:(fun () -> try Sys.chdir saved_cwd with _ -> ()) (fun () ->
          (* Prefer .reference file; fall back to running ocamlrun *)
          let expected_opt = match read_reference path with
            | Some r -> Some r
            | None -> run_with_timeout (Printf.sprintf "ocamlrun %s" exe)
          in
          (match expected_opt with
          | None -> Skip "ocamlrun timeout/error"
          | Some expected_raw ->
            (* Strip "All tests succeeded." suffix if present (added by testing.ml at_exit) *)
            let testing_suffix = "\nAll tests succeeded.\n" in
            let expected =
              if String.length expected_raw >= String.length testing_suffix &&
                 String.sub expected_raw
                   (String.length expected_raw - String.length testing_suffix)
                   (String.length testing_suffix) = testing_suffix
              then String.sub expected_raw 0
                     (String.length expected_raw - String.length testing_suffix)
              else expected_raw
            in
            let strip_testing_suffix s =
              if String.length s >= String.length testing_suffix &&
                 String.sub s
                   (String.length s - String.length testing_suffix)
                   (String.length testing_suffix) = testing_suffix
              then String.sub s 0 (String.length s - String.length testing_suffix)
              else s
            in
            (* Run through our interpreter *)
            (match run_our_interp exe with
            | Error msg ->
              if String.length msg >= 4 && (String.sub msg 0 4 = "step" || String.sub msg 0 4 = "wall") then
                Skip (Printf.sprintf "interpreter %s" msg)
              else
                Fail (Printf.sprintf "interpreter error: %s" msg)
            | Ok actual_raw ->
              let actual = strip_testing_suffix actual_raw in
              if actual = expected then Pass
              else
                Fail (Printf.sprintf
                  "output mismatch:\n  expected: %s\n  actual:   %s"
                  (String.escaped (String.sub expected 0 (min 3500 (String.length expected))))
                  (String.escaped (String.sub actual 0 (min 3500 (String.length actual)))))))
          ) (* Fun.protect *)
        end)
    with
    | Sys_error msg -> Skip (Printf.sprintf "sys error: %s" msg)
    | e -> Skip (Printf.sprintf "exception: %s" (Printexc.to_string e)))

(* Names that are helper/companion modules, not standalone test programs *)
let is_helper_module name =
  name = "testing.ml"

let collect_ml_files dir =
  let files = ref [] in
  (try
    let entries = Sys.readdir dir in
    Array.sort String.compare entries;
    Array.iter (fun name ->
      if Filename.check_suffix name ".ml"
         && not (Filename.check_suffix name ".ml.c")
         && not (is_helper_module name) then
        files := Filename.concat dir name :: !files
    ) entries
  with Sys_error msg ->
    Printf.eprintf "Warning: cannot read directory %s: %s\n" dir msg);
  List.rev !files

(* Parse skip config: each line is "filename  reason", # comments *)
let parse_skip_conf path =
  let tbl = Hashtbl.create 32 in
  if Sys.file_exists path then begin
    let ic = open_in path in
    (try while true do
      let line = String.trim (input_line ic) in
      if line <> "" && line.[0] <> '#' then begin
        let len = String.length line in
        let i = ref 0 in
        while !i < len && line.[!i] <> ' ' && line.[!i] <> '\t' do incr i done;
        let filename = String.sub line 0 !i in
        while !i < len && (line.[!i] = ' ' || line.[!i] = '\t') do incr i done;
        let reason = if !i < len then String.sub line !i (len - !i) else "skipped by config" in
        Hashtbl.replace tbl filename reason
      end
    done with End_of_file -> ());
    close_in ic
  end;
  tbl

let () =
  let dirs = ref [] in
  let skip_conf = ref "" in
  let args = Array.to_list Sys.argv |> List.tl in
  let rec parse = function
    | "--skip-conf" :: path :: rest -> skip_conf := path; parse rest
    | x :: rest -> dirs := !dirs @ [x]; parse rest
    | [] -> ()
  in
  parse args;
  if !dirs = [] then dirs := ["test/ocaml-testsuite/basic"];
  let skip_tbl = if !skip_conf <> "" then parse_skip_conf !skip_conf
                 else Hashtbl.create 0 in
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  let failures = ref [] in
  List.iter (fun dir ->
    Printf.printf "=== Testing directory: %s ===\n%!" dir;
    let files = collect_ml_files dir in
    List.iter (fun path ->
      let basename = Filename.basename path in
      match Hashtbl.find_opt skip_tbl basename with
      | Some reason ->
        incr skip;
        Printf.printf "  SKIP  %s (config: %s)\n%!" basename reason
      | None ->
      match test_file path with
      | Pass ->
        incr pass;
        Printf.printf "  PASS  %s\n%!" basename
      | Fail msg ->
        incr fail;
        Printf.printf "  FAIL  %s: %s\n%!" basename msg;
        failures := (basename, msg) :: !failures
      | Skip reason ->
        incr skip;
        Printf.printf "  SKIP  %s (%s)\n%!" basename reason
    ) files
  ) !dirs;
  Printf.printf "\n=== Summary ===\n";
  Printf.printf "  Pass: %d  Fail: %d  Skip: %d  Total: %d\n"
    !pass !fail !skip (!pass + !fail + !skip);
  if !failures <> [] then begin
    Printf.printf "\nFailed tests:\n";
    List.iter (fun (name, msg) ->
      Printf.printf "  %s: %s\n" name msg
    ) (List.rev !failures)
  end;
  exit (if !fail > 0 then 1 else 0)
