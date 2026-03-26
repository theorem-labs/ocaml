(* runner.ml - Standalone runner for the extracted Main.v pipeline.
   Usage: runner.exe <file.byte>
   Runs the full pipeline: read file -> decode -> interpret -> print output.
   Note: after extraction, main is available as Interp_extracted.main0
   because Coq appends '0' to avoid clashing with module-level let () = ... *)

let () =
  let _exit_code = Interp_extracted.main0 in
  flush stdout
