(* runner.ml - Standalone runner for the extracted Main.v pipeline.
   Usage: runner.exe <file.byte>
   Runs the full pipeline: read file -> decode -> interpret -> print output. *)

let () =
  let _exit_code = Interp_extracted.main0 in
  flush stdout
