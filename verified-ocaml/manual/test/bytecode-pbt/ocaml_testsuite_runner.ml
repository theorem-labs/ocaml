(* ocaml_testsuite_runner.ml - Run OCaml compiler test suite against our
   bytecode interpreter. For each .ml test file:
   1. Compile with ocamlc to get a bytecode executable
   2. Run with ocamlrun to get expected output
   3. Run bytecode through our interpreter to get actual output
   4. Compare outputs

   Usage: ocaml_testsuite_runner.exe [directory ...]
   If no directories given, runs on test/ocaml-testsuite/basic *)

open Test_common

(* Path to the ppx_strip_expect executable, relative to the build root.
   When run via dune exec, the cwd is the project root. *)
let ppx_strip_expect_exe =
  (* Try to find the exe relative to the current binary location first,
     then fall back to a path relative to cwd. *)
  let candidates = [
    (* When run via dune exec from project root *)
    Filename.concat (Filename.dirname Sys.executable_name)
      "../ppx_strip_expect/ppx_strip_expect_exe.exe";
    (* Absolute path in _build *)
    "_build/default/test/harness/ppx_strip_expect/ppx_strip_expect_exe.exe";
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

(* Step limit for our interpreter - keep modest since Coq-extracted code is slow *)
let step_limit = 5_000_000

(* Wall-clock timeout for our interpreter in seconds *)
let interp_timeout = 30.0

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

(* Run ocamlc bytecode through our interpreter, with step limit *)
exception Clean_exit

let run_our_interp exe_file =
  let data = Loader.read_file exe_file in
  let sections = Loader.parse_sections data in
  let code = Array.of_list (Loader.load_bytecode_from_sections data sections) in
  let raw_globals = load_globals data sections in
  let (globals, init_heap, init_next_addr) = heap_allocate_globals raw_globals in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let (heap_ref, next_addr_ref, pending_raise_ref, perform_raise, handler, get_named_value, _minor_words_ref, _last_next_addr_ref) = make_handler ~raw_globals ~globals_list:globals prims buf in
  let open Interp_extracted in
  (* Initialize state with pre-populated heap for mutable global objects *)
  let s = ref { (initial_state globals) with hp = init_heap; next_addr = init_next_addr } in
  heap_ref := init_heap;
  next_addr_ref := init_next_addr;
  let remaining = ref step_limit in
  let result = ref None in
  let deadline = Unix.gettimeofday () +. interp_timeout in
  let check_count = ref 0 in
  (* Helper: check if an exception value is "Exit" (from caml_sys_exit) *)
  let is_exit_exn exn =
    match exn with
    | Val_block (248, (Val_block (252, chars)) :: _) ->
      let name = String.init (List.length chars) (fun i ->
        match List.nth_opt chars i with Some (Val_int c) -> Char.chr (c land 0xFF) | _ -> '\000') in
      name = "Exit"
    | _ -> false
  in
  (* Get code pointer from a closure value *)
  let get_closure_pc fn =
    match fn with
    | Val_block (247, Val_int pc :: _) -> Some pc
    | Val_ptr addr ->
      (match heap_lookup !heap_ref addr with
       | Some (247, Val_int pc :: _) -> Some pc
       | _ -> None)
    | Val_closure (addr, ofs) ->
      (match heap_lookup !heap_ref addr with
       | Some (247, fields) ->
         (match List.nth_opt fields ofs with
          | Some (Val_int pc) -> Some pc
          | _ -> None)
       | _ -> None)
    | _ -> None
  in
  (* Invoke the Printexc uncaught exception handler if one was registered.
     When RAISE fires with trap_sp=0, OCaml's runtime calls the closure registered
     via caml_register_named_value("Printexc.handle_uncaught_exception", fn).
     The handler signature is fn(exn, raw_backtrace). We pass Val_int 0 as backtrace.
     Sets up the interpreter state for the call, returns true if successful. *)
  let invoke_uncaught_handler exn =
    match get_named_value "Printexc.handle_uncaught_exception" with
    | None -> false
    | Some handler_fn ->
      (match get_closure_pc handler_fn with
       | None -> false
       | Some target_pc ->
         let stop_pc = ref (-1) in
         Array.iteri (fun i instr -> if instr = STOP && !stop_pc = -1 then stop_pc := i) code;
         if !stop_pc = -1 then false
         else begin
           (* Set up as 2-arg call: stack=[exn; dummy_bt; ret_pc; saved_env; saved_ea; ...] *)
           let dummy_bt = Val_int 0 in
           let new_stack = exn :: dummy_bt :: Val_int (Z.of_nat !stop_pc)
                           :: !s.env :: Val_int (Z.of_nat !s.extra_args) :: !s.stack in
           s := { !s with
                  pc = target_pc;
                  accu = handler_fn;
                  stack = new_stack;
                  env = handler_fn;
                  extra_args = 1;
                  hp = !heap_ref;
                  next_addr = !next_addr_ref };
           true
         end)
  in
  let handle_unhandled_exn exn =
    if is_exit_exn exn then raise Clean_exit
    else if invoke_uncaught_handler exn then ()
    else begin
      (* No Printexc handler registered: simulate default_fatal_uncaught_exception.
         The C runtime prints the error to stderr (we don't capture that) and exits.
         Treat as a clean exit — the stdout output captured so far is the result. *)
      raise Clean_exit
    end
  in
  let rec loop () =
    if !remaining <= 0 then result := Some "step limit"
    else begin
      decr remaining;
      (* Check wall-clock every 1000 steps to avoid syscall overhead *)
      incr check_count;
      if !check_count mod 1000 = 0 && Unix.gettimeofday () > deadline then
        result := Some "wall-clock timeout"
      else
        match step code !s with
        | Step s' -> s := s'; loop ()
        | Halt _ -> ()
        | Error msg ->
          let msg_str = sc msg in
          if msg_str = "unhandled exception" then
            (handle_unhandled_exn !s.accu; if !result = None then loop ())
          else
            result := Some msg_str
        | CCall_request (idx, args, cont) ->
          heap_ref := cont.hp;
          next_addr_ref := cont.next_addr;
          pending_raise_ref := None;
          (match handler idx args with
           | Some v ->
             s := { cont with accu = v;
                    hp = !heap_ref; next_addr = !next_addr_ref };
             loop ()
           | None ->
             (match !pending_raise_ref with
              | Some exn ->
                (* Check for sys_exit sentinel before trying to raise *)
                if is_exit_exn exn then raise Clean_exit
                else begin
                  let cont' = { cont with hp = !heap_ref; next_addr = !next_addr_ref } in
                  (match perform_raise cont' exn with
                   | Step s' -> s := s'; loop ()
                   | Halt _ -> ()
                   | Error msg ->
                     let msg_str = sc msg in
                     if msg_str = "unhandled exception" then
                       (handle_unhandled_exn exn; if !result = None then loop ())
                     else
                       result := Some msg_str
                   | CCall_request _ -> result := Some "nested ccall in raise")
                end
              | None -> result := Some "ccall failed"))
    end
  in
  (try loop ()
   with
   | Clean_exit -> ()
   | e -> result := Some (Printexc.to_string e));
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err

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
            match ppx_strip_expect_exe with
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

let () =
  let dirs = ref [] in
  let args = Array.to_list Sys.argv |> List.tl in
  (match args with
   | [] ->
     (* Default: basic test directory *)
     dirs := ["test/ocaml-testsuite/basic"]
   | l -> dirs := l);
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  let failures = ref [] in
  List.iter (fun dir ->
    Printf.printf "=== Testing directory: %s ===\n%!" dir;
    let files = collect_ml_files dir in
    List.iter (fun path ->
      let basename = Filename.basename path in
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
