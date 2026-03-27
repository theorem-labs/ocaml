(* strip_expect_ppx.ml - Standalone PPX that strips [%%expect ...] blocks.
   Used by ocaml_testsuite_runner to compile expect-test files. *)
open Ppxlib

let () =
  Driver.register_transformation "strip_expect"
    ~impl:(fun structure ->
      List.filter (fun item ->
        match item.pstr_desc with
        | Pstr_extension (({ txt = "expect"; _ }, _), _) -> false
        | _ -> true
      ) structure)

let () = Driver.standalone ()
