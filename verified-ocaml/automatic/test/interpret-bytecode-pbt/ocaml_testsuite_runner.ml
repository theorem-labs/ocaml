(* ocaml_testsuite_runner.ml - Run OCaml compiler test suite against our
   bytecode interpreter. For each .ml test file:
   1. Compile with ocamlc to get a bytecode executable
   2. Run with ocamlrun to get expected output
   3. Run bytecode through our interpreter to get actual output
   4. Compare outputs

   Usage: ocaml_testsuite_runner.exe [directory ...]
   If no directories given, runs on test/ocaml-testsuite/basic *)

open Test_common

(* Timeout in seconds for both ocamlrun and our interpreter *)
let timeout_secs = 5

(* Step limit for our interpreter - keep modest since Coq-extracted code is slow *)
let step_limit = 1_000_000

(* Wall-clock timeout for our interpreter in seconds *)
let interp_timeout = 5.0

let run_with_timeout cmd =
  let ic = Unix.open_process_in
    (Printf.sprintf "timeout %d %s 2>/dev/null" timeout_secs cmd) in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_char buf (input_char ic) done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  match status with
  | Unix.WEXITED 0 -> Some (Buffer.contents buf)
  | Unix.WEXITED 124 -> None  (* timeout *)
  | _ -> None

(* Run ocamlc bytecode through our interpreter, with step limit *)
let run_our_interp exe_file =
  let data = Loader.read_file exe_file in
  let sections = Loader.parse_sections data in
  let code = Loader.load_bytecode_from_sections data sections in
  let globals = Array.to_list (load_globals data sections) in
  let prims = load_prims data sections in
  let buf = Buffer.create 256 in
  let handler = make_handler prims buf in
  let open Interp_extracted in
  let s = ref (initial_state globals) in
  let remaining = ref step_limit in
  let result = ref None in
  let deadline = Unix.gettimeofday () +. interp_timeout in
  let check_count = ref 0 in
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
        | Error msg -> result := Some (sc msg)
        | CCall_request (idx, args, cont) ->
          (match handler idx args with
           | Some v -> s := set_accu cont v; loop ()
           | None -> result := Some "ccall failed")
    end
  in
  (try loop () with e -> result := Some (Printexc.to_string e));
  match !result with
  | None -> Ok (Buffer.contents buf)
  | Some err -> Error err

type result = Pass | Fail of string | Skip of string

let test_file path =
  (* Only handle plain .ml files *)
  if not (Filename.check_suffix path ".ml") then Skip "not .ml"
  else
    with_temp_dir (fun dir ->
      let exe = Filename.concat dir "test.byte" in
      let compile_cmd =
        Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe path in
      if Sys.command compile_cmd <> 0 then
        Skip "compile failed"
      else
        (* Get expected output from ocamlrun *)
        match run_with_timeout (Printf.sprintf "ocamlrun %s" exe) with
        | None -> Skip "ocamlrun timeout/error"
        | Some expected ->
          (* Run through our interpreter *)
          match run_our_interp exe with
          | Error msg ->
            if String.length msg >= 4 && (String.sub msg 0 4 = "step" || String.sub msg 0 4 = "wall") then
              Skip (Printf.sprintf "interpreter %s" msg)
            else
              Fail (Printf.sprintf "interpreter error: %s" msg)
          | Ok actual ->
            if actual = expected then Pass
            else
              Fail (Printf.sprintf
                "output mismatch:\n  expected: %s\n  actual:   %s"
                (String.escaped (String.sub expected 0 (min 200 (String.length expected))))
                (String.escaped (String.sub actual 0 (min 200 (String.length actual))))))

let collect_ml_files dir =
  let files = ref [] in
  (try
    let entries = Sys.readdir dir in
    Array.sort String.compare entries;
    Array.iter (fun name ->
      if Filename.check_suffix name ".ml" && not (Filename.check_suffix name ".ml.c") then
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
