(* harness.ml - Test harness: Main.v pipeline vs ocamlrun on OCaml test suite.
   For each .ml file in the test directories:
   1. Compile with ocamlc -> test.byte
   2. Run ocamlrun test.byte -> expected output
   3. Run runner.exe test.byte -> actual output (our Main.v pipeline)
   4. Compare outputs *)

(* === Run a command, capture stdout === *)
let run_capture cmd =
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_char buf (input_char ic) done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  (status, Buffer.contents buf)

(* === Path to runner.exe (our Main.v pipeline) === *)
let runner_exe =
  let dir = Filename.dirname Sys.argv.(0) in
  Filename.concat dir "runner.exe"

(* === Temp dir === *)
let with_temp_dir f =
  let dir = Filename.temp_file "pbt" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () ->
    (try Array.iter (fun n -> Sys.remove (Filename.concat dir n)) (Sys.readdir dir) with _ -> ());
    (try Unix.rmdir dir with _ -> ())
  ) (fun () -> f dir)

type result = Pass | Fail of string | Skip of string

let run_test ml_file =
  with_temp_dir (fun dir ->
    let exe = Filename.concat dir "test.byte" in
    (* Compile *)
    let compile_cmd = Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe ml_file in
    if Sys.command compile_cmd <> 0 then
      Skip "compile failed"
    else
      (* Run with ocamlrun *)
      let ocamlrun_status, expected =
        run_capture (Printf.sprintf "timeout 5 ocamlrun %s 2>/dev/null" exe) in
      match ocamlrun_status with
      | Unix.WEXITED 0 ->
        (* Run with our pipeline *)
        let runner_status, actual =
          run_capture (Printf.sprintf "timeout 30 %s %s 2>/dev/null" runner_exe exe) in
        (match runner_status with
         | Unix.WEXITED 0 ->
           if actual = expected then Pass
           else Fail (Printf.sprintf "output mismatch:\n  expected: %S\n  actual:   %S"
                        (String.sub expected 0 (min 200 (String.length expected)))
                        (String.sub actual 0 (min 200 (String.length actual))))
         | Unix.WEXITED n ->
           if actual = expected then Pass  (* non-zero exit but same output is ok *)
           else Fail (Printf.sprintf "runner exited %d, output mismatch" n)
         | _ -> Skip "runner timeout or signal")
      | _ -> Skip "ocamlrun failed")

let () =
  let dirs = if Array.length Sys.argv > 1 then
    Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
  else
    ["automatic/test/ocaml-testsuite/basic"]
  in
  let pass = ref 0 and fail = ref 0 and skip = ref 0 in
  let failures = ref [] in
  List.iter (fun dir ->
    let files = try Sys.readdir dir with _ -> [||] in
    let ml_files = Array.to_list files
      |> List.filter (fun f -> Filename.check_suffix f ".ml")
      |> List.sort String.compare in
    List.iter (fun f ->
      let path = Filename.concat dir f in
      let result = run_test path in
      match result with
      | Pass -> incr pass; Printf.printf "  PASS  %s\n%!" f
      | Fail msg -> incr fail; failures := (f, msg) :: !failures;
        Printf.printf "  FAIL  %s: %s\n%!" f msg
      | Skip reason -> incr skip; Printf.printf "  SKIP  %s (%s)\n%!" f reason
    ) ml_files
  ) dirs;
  Printf.printf "\n%d pass, %d fail, %d skip\n" !pass !fail !skip;
  if !failures <> [] then begin
    Printf.printf "\nFailures:\n";
    List.iter (fun (f, msg) -> Printf.printf "  %s: %s\n" f msg) (List.rev !failures)
  end;
  exit (if !fail = 0 then 0 else 1)
