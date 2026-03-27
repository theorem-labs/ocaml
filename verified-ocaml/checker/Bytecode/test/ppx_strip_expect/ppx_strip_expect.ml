(* ppx_strip_expect.ml - PPX rewriter that strips [%%expect{| ... |}] blocks *)
open Ppxlib

let () =
  Driver.register_transformation "strip_expect"
    ~impl:(fun structure ->
      List.filter (fun item ->
        match item.pstr_desc with
        | Pstr_extension (({ txt = "expect"; _ }, _), _) -> false
        | _ -> true
      ) structure
    )
