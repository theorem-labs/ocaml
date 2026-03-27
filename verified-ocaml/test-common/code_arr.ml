(* code_arr.ml - Thin wrapper around OCaml arrays for extracted PrimArray.
   Provides persistent-array semantics (set returns a copy) matching Rocq's
   PrimArray contract. Used only during list_to_code_array; after that the
   array is read-only via get/length. *)
type 'a t = 'a array
let make = Array.make
let get = Array.get
let set a i v = let a' = Array.copy a in a'.(i) <- v; a'
let length = Array.length
