(* test_common.ml - Shared utilities for all PBT test files. *)

open Interp_extracted

let with_temp_dir f =
  let dir = Filename.temp_file "pbt" "" in
  Sys.remove dir; Unix.mkdir dir 0o700;
  Fun.protect ~finally:(fun () ->
    (try Array.iter (fun n -> Sys.remove (Filename.concat dir n)) (Sys.readdir dir) with _ -> ());
    (try Unix.rmdir dir with _ -> ())
  ) (fun () -> f dir)

let compile_and_run_ocamlc dir source =
  let src = Filename.concat dir "test.ml" in
  let exe = Filename.concat dir "test.byte" in
  let oc = open_out src in output_string oc source; close_out oc;
  if Sys.command (Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe src) <> 0 then None
  else begin
    let ic = Unix.open_process_in (Printf.sprintf "timeout 5 ocamlrun %s 2>/dev/null" exe) in
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_char buf (input_char ic) done with End_of_file -> ());
    ignore (Unix.close_process_in ic);
    Some (Buffer.contents buf)
  end

let compile_ocamlc dir source =
  let src = Filename.concat dir "test.ml" in
  let exe = Filename.concat dir "test.byte" in
  let oc = open_out src in output_string oc source; close_out oc;
  if Sys.command (Printf.sprintf "ocamlc -o %s %s 2>/dev/null" exe src) <> 0 then None
  else Some exe

let cl s = List.init (String.length s) (fun i -> s.[i])
let sc l = let buf = Buffer.create (List.length l) in List.iter (Buffer.add_char buf) l; Buffer.contents buf

let events_to_string events =
  let buf = Buffer.create 64 in
  List.iter (fun c -> Buffer.add_char buf (Char.chr (c land 0xFF))) events;
  Buffer.contents buf

(* Helper: build "print_int(e); print_newline()" *)
let print_int_nl e =
  Exp_seq (Exp_app (Exp_var (cl "print_int"), e),
           Exp_app (Exp_var (cl "print_newline"), Exp_unit))

(* Result type for source interpreter / compiler test helpers. *)
type interp_result = Interp_ok of string | Interp_err of string
