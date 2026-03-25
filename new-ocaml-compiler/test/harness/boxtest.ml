(* Use run_ocamlc_bytecode to run a bytecode file and print output *)
let () =
  let file = if Array.length Sys.argv > 1 then Sys.argv.(1) else "/tmp/dbg_box.byte" in
  match Test_common.run_ocamlc_bytecode file with
  | Ok output -> print_string output
  | Error e -> Printf.printf "ERROR: %s\n" e
