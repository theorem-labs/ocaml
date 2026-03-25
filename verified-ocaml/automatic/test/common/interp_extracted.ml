
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n0

  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    (<=) (Stdlib.Int.succ n0) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

module Pos =
 struct
  (** val succ : int -> int **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->2*p) (succ p))
      (fun p -> (fun p->1+2*p) p)
      (fun _ -> (fun p->2*p) 1)
      x

  (** val add : int -> int -> int **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun q -> (fun p->2*p) (add p q))
        (fun _ -> (fun p->1+2*p) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (succ q))
        (fun q -> (fun p->1+2*p) q)
        (fun _ -> (fun p->2*p) 1)
        y)
      x

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  type mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : int -> int -> int **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> add y ((fun p->2*p) (mul p y)))
      (fun p -> (fun p->2*p) (mul p y))
      (fun _ -> y)
      x

  (** val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1 **)

  let rec iter f x n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n0

  (** val div2 : int -> int **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val div2_up : int -> int **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> 1)
      p

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : int -> int -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val coq_Nsucc_double : int -> int **)

  let coq_Nsucc_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val coq_Ndouble : int -> int **)

  let coq_Ndouble n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val coq_lor : int -> int -> int **)

  let rec coq_lor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun _ -> p)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> (fun p->1+2*p) (coq_lor p0 q0))
        (fun q0 -> (fun p->2*p) (coq_lor p0 q0))
        (fun _ -> (fun p->1+2*p) p0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> q)
        (fun q0 -> (fun p->1+2*p) q0)
        (fun _ -> q)
        q)
      p

  (** val coq_land : int -> int -> int **)

  let rec coq_land p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 1)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun q0 -> coq_Ndouble (coq_land p0 q0))
        (fun _ -> 0)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 1)
        (fun _ -> 0)
        (fun _ -> 1)
        q)
      p

  (** val ldiff : int -> int -> int **)

  let rec ldiff p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Nsucc_double (ldiff p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun q0 -> coq_Ndouble (ldiff p0 q0))
        (fun _ -> p)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> 0)
        (fun _ -> 1)
        (fun _ -> 0)
        q)
      p

  (** val coq_lxor : int -> int -> int **)

  let rec coq_lxor p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun _ -> ((fun p->2*p) p0))
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> coq_Nsucc_double (coq_lxor p0 q0))
        (fun q0 -> coq_Ndouble (coq_lxor p0 q0))
        (fun _ -> ((fun p->1+2*p) p0))
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> ((fun p->2*p) q0))
        (fun q0 -> ((fun p->1+2*p) q0))
        (fun _ -> 0)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Stdlib.Int.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  (** val pred_N : int -> int **)

  let pred_N x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> ((fun p->2*p) p))
      (fun p -> (pred_double p))
      (fun _ -> 0)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val testbit : int -> int -> bool **)

  let rec testbit p n0 =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun p0 ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun n1 -> testbit p0 (pred_N n1))
        n0)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        n0)
      p
 end

module N =
 struct
  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val succ_pos : int -> int **)

  let succ_pos n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> Pos.succ p)
      n0

  (** val sub : int -> int -> int **)

  let sub n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun n' ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun m' -> match Pos.sub_mask n' m' with
                   | Pos.IsPos p -> p
                   | _ -> 0)
        m)
      n0

  (** val compare : int -> int -> comparison **)

  let compare n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> Eq)
        (fun _ -> Lt)
        m)
      (fun n' ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> Gt)
        (fun m' -> Pos.compare n' m')
        m)
      n0

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val coq_lor : int -> int -> int **)

  let coq_lor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> (Pos.coq_lor p q))
        m)
      n0

  (** val coq_land : int -> int -> int **)

  let coq_land n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> 0)
        (fun q -> Pos.coq_land p q)
        m)
      n0

  (** val ldiff : int -> int -> int **)

  let ldiff n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.ldiff p q)
        m)
      n0

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> n0)
        (fun q -> Pos.coq_lxor p q)
        m)
      n0
 end

module Coq_N =
 struct
  (** val add : int -> int -> int **)

  let add = (+)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val testbit : int -> int -> bool **)

  let testbit a n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> false)
      (fun p -> Coq_Pos.testbit p n0)
      a

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

module Z =
 struct
  (** val double : int -> int **)

  let double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      (fun p -> (~-) ((fun p->2*p) p))
      x

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      (fun p -> (~-) (Pos.pred_double p))
      x

  (** val pred_double : int -> int **)

  let pred_double x =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (~-) 1)
      (fun p -> (Pos.pred_double p))
      (fun p -> (~-) ((fun p->1+2*p) p))
      x

  (** val pos_sub : int -> int -> int **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (~-) ((fun p->2*p) q))
        (fun q -> (~-) (Pos.pred_double q))
        (fun _ -> 0)
        y)
      x

  (** val add : int -> int -> int **)

  let add = (+)

  (** val opp : int -> int **)

  let opp = (~-)

  (** val sub : int -> int -> int **)

  let sub = (-)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : int -> int -> bool **)

  let eqb x y =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val to_nat : int -> int **)

  let to_nat z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p -> Pos.to_nat p)
      (fun _ -> 0)
      z0

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun n1 -> (Pos.of_succ_nat n1))
      n0

  (** val of_N : int -> int **)

  let of_N = fun p -> p

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul ((fun p->2*p) 1) r) 1 in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun p->2*p) 1) r in
      if ltb r' b
      then ((mul ((fun p->2*p) 1) q), r')
      else ((add (mul ((fun p->2*p) 1) q) 1), (sub r' b)))
      (fun _ -> if leb ((fun p->2*p) 1) b then (0, 1) else (1, 0))
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (add b r)))
           (fun _ -> ((opp (add q 1)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
           (fun _ -> ((opp q), 0))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           (fun _ -> ((opp (add q 1)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val div : int -> int -> int **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : int -> int -> int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val quotrem : int -> int -> int * int **)

  let quotrem a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> (0, 0))
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (of_N r)))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (of_N r)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> (0, a))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((opp (of_N q)), (opp (of_N r))))
        (fun b0 ->
        let (q, r) = N.pos_div_eucl a0 b0 in ((of_N q), (opp (of_N r))))
        b)
      a

  (** val quot : int -> int -> int **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : int -> int -> int **)

  let rem a b =
    snd (quotrem a b)

  (** val div2 : int -> int **)

  let div2 z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> (Pos.div2 p))
        (fun _ -> (Pos.div2 p))
        (fun _ -> 0)
        p)
      (fun p -> (~-) (Pos.div2_up p))
      z0

  (** val shiftl : int -> int -> int **)

  let shiftl a n0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> a)
      (fun p -> Pos.iter (mul ((fun p->2*p) 1)) a p)
      (fun p -> Pos.iter div2 a p)
      n0

  (** val shiftr : int -> int -> int **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : int -> int -> int **)

  let coq_lor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (Pos.coq_lor a0 b0))
        (fun b0 -> (~-) (N.succ_pos (N.ldiff (Pos.pred_N b0) a0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-) (N.succ_pos (N.ldiff (Pos.pred_N a0) b0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_land : int -> int -> int **)

  let coq_land a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> 0)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (Pos.coq_land a0 b0))
        (fun b0 -> of_N (N.ldiff a0 (Pos.pred_N b0)))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> 0)
        (fun b0 -> of_N (N.ldiff b0 (Pos.pred_N a0)))
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
        b)
      a

  (** val coq_lxor : int -> int -> int **)

  let coq_lxor a b =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> of_N (Pos.coq_lxor a0 b0))
        (fun b0 -> (~-) (N.succ_pos (N.coq_lxor a0 (Pos.pred_N b0))))
        b)
      (fun a0 ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> a)
        (fun b0 -> (~-)
        (N.succ_pos (N.coq_lxor (Pos.pred_N a0) b0)))
        (fun b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))
        b)
      a

  (** val pred : int -> int **)

  let pred = Stdlib.Int.pred

  (** val geb : int -> int -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true

  (** val gtb : int -> int -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val odd : int -> bool **)

  let odd z0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      z0

  (** val testbit : int -> int -> bool **)

  let testbit a n0 =
    (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
      (fun _ -> odd a)
      (fun p ->
      (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
        (fun _ -> false)
        (fun a0 -> Coq_Pos.testbit a0 p)
        (fun a0 -> negb (Coq_N.testbit (Coq_Pos.pred_N a0) p))
        a)
      (fun _ -> false)
      n0

  (** val lnot : int -> int **)

  let lnot a =
    pred (opp a)

  (** val ones : int -> int **)

  let ones n0 =
    pred (shiftl 1 n0)
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n1 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n1 l0))
    n0

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l)
    (fun n1 -> match l with
               | [] -> []
               | _ :: l0 -> skipn n1 l0)
    n0

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n1 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n1)
    n0

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: l0 -> app (f x) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : int -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun p' -> shift true (loop n' p'))
        (fun p' -> shift false (loop n' p'))
        (fun _ -> one)
        p)
      n0
  in loop (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))

(** val ascii_of_N : int -> char **)

let ascii_of_N n0 =
  (fun f0 fp n -> if n=0 then f0 () else fp n)
    (fun _ -> zero)
    (fun p -> ascii_of_pos p)
    n0

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (Coq_N.of_nat a)

(** val n_of_digits : bool list -> int **)

let rec n_of_digits = function
| [] -> 0
| b :: l' ->
  Coq_N.add (if b then 1 else 0) (Coq_N.mul ((fun p->2*p) 1) (n_of_digits l'))

(** val n_of_ascii : char -> int **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits
      (a0 :: (a1 :: (a2 :: (a3 :: (a4 :: (a5 :: (a6 :: (a7 :: [])))))))))
    a

(** val nat_of_ascii : char -> int **)

let nat_of_ascii a =
  Coq_N.to_nat (n_of_ascii a)

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type value =
| Val_int of int
| Val_block of int * value list
| Val_ptr of int
| Val_closure of int * int

(** val closure_tag : int **)

let closure_tag =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val infix_tag : int **)

let infix_tag =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val string_tag : int **)

let string_tag =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val val_unit : value **)

let val_unit =
  Val_int 0

(** val val_true : value **)

let val_true =
  Val_int 1

(** val val_false : value **)

let val_false =
  Val_int 0

(** val val_bool : bool -> value **)

let val_bool = function
| true -> val_true
| false -> val_false

(** val is_int : value -> bool **)

let is_int = function
| Val_int _ -> true
| _ -> false

(** val set_nth : 'a1 list -> int -> 'a1 -> 'a1 list option **)

let rec set_nth l n0 x =
  match l with
  | [] -> None
  | h :: rest ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some (x :: rest))
       (fun n' ->
       match set_nth rest n' x with
       | Some rest' -> Some (h :: rest')
       | None -> None)
       n0)

(** val value_eqb : value -> value -> bool **)

let rec value_eqb v1 v2 =
  match v1 with
  | Val_int n1 -> (match v2 with
                   | Val_int n2 -> Z.eqb n1 n2
                   | _ -> false)
  | Val_block (t1, fs1) ->
    (match v2 with
     | Val_block (t2, fs2) ->
       (&&) ((=) t1 t2)
         (let rec list_eqb l1 l2 =
            match l1 with
            | [] -> (match l2 with
                     | [] -> true
                     | _ :: _ -> false)
            | v3 :: r1 ->
              (match l2 with
               | [] -> false
               | v4 :: r2 -> (&&) (value_eqb v3 v4) (list_eqb r1 r2))
          in list_eqb fs1 fs2)
     | _ -> false)
  | Val_ptr a1 -> (match v2 with
                   | Val_ptr a2 -> (=) a1 a2
                   | _ -> false)
  | Val_closure (a1, o1) ->
    (match v2 with
     | Val_closure (a2, o2) -> (&&) ((=) a1 a2) ((=) o1 o2)
     | _ -> false)

type instruction =
| ACC of int
| PUSH
| PUSHACC of int
| POP of int
| ASSIGN of int
| ENVACC of int
| PUSHENVACC of int
| PUSH_RETADDR of int
| APPLY of int
| APPLY1
| APPLY2
| APPLY3
| APPTERM of int * int
| APPTERM1 of int
| APPTERM2 of int
| APPTERM3 of int
| RETURN of int
| RESTART
| GRAB of int
| CLOSURE of int * int
| CLOSUREREC of int * int * int list
| OFFSETCLOSURE of int
| PUSHOFFSETCLOSURE of int
| GETGLOBAL of int
| PUSHGETGLOBAL of int
| GETGLOBALFIELD of int * int
| PUSHGETGLOBALFIELD of int * int
| SETGLOBAL of int
| ATOM of int
| PUSHATOM of int
| MAKEBLOCK of int * int
| MAKEBLOCK1 of int
| MAKEBLOCK2 of int
| MAKEBLOCK3 of int
| MAKEFLOATBLOCK of int
| GETFIELD of int
| GETFLOATFIELD of int
| SETFIELD of int
| SETFLOATFIELD of int
| VECTLENGTH
| GETVECTITEM
| SETVECTITEM
| GETBYTESCHAR
| SETBYTESCHAR
| GETSTRINGCHAR
| BRANCH of int
| BRANCHIF of int
| BRANCHIFNOT of int
| SWITCH of int * int * int list * int list
| BOOLNOT
| PUSHTRAP of int
| POPTRAP
| RAISE
| RERAISE
| RAISE_NOTRACE
| CHECK_SIGNALS
| C_CALL of int * int
| CONSTINT of int
| PUSHCONSTINT of int
| NEGINT
| ADDINT
| SUBINT
| MULINT
| DIVINT
| MODINT
| ANDINT
| ORINT
| XORINT
| LSLINT
| LSRINT
| ASRINT
| EQ
| NEQ
| LTINT
| LEINT
| GTINT
| GEINT
| OFFSETINT of int
| OFFSETREF of int
| ISINT
| GETMETHOD
| GETPUBMET of int
| GETDYNMET
| BEQ of int * int
| BNEQ of int * int
| BLTINT of int * int
| BLEINT of int * int
| BGTINT of int * int
| BGEINT of int * int
| ULTINT
| UGEINT
| BULTINT of int * int
| BUGEINT of int * int
| STOP
| EVENT
| BREAK
| PERFORM
| RESUME
| RESUMETERM of int
| REPERFORMTERM of int

type trap_frame = { trap_pc : int; trap_sp_offset : int; trap_env : value;
                    trap_extra_args : int }

type heap = (int * (int * value list)) list

type state = { pc : int; accu : value; stack : value list; env : value;
               extra_args : int; global : value list;
               trap_stack : trap_frame list; hp : heap; next_addr : int }

type step_result =
| Step of state
| Halt of value
| Error of char list
| CCall_request of int * value list * state

type run_result =
| Finished of value
| Run_error of char list
| Out_of_fuel of state

(** val set_accu : state -> value -> state **)

let set_accu s v =
  { pc = s.pc; accu = v; stack = s.stack; env = s.env; extra_args =
    s.extra_args; global = s.global; trap_stack = s.trap_stack; hp = s.hp;
    next_addr = s.next_addr }

(** val heap_lookup : heap -> int -> (int * value list) option **)

let rec heap_lookup h addr =
  match h with
  | [] -> None
  | p :: rest ->
    let (a, p0) = p in if (=) a addr then Some p0 else heap_lookup rest addr

(** val heap_alloc : state -> int -> value list -> state * value **)

let heap_alloc s tag fields =
  let addr = s.next_addr in
  let s' = { pc = s.pc; accu = s.accu; stack = s.stack; env = s.env;
    extra_args = s.extra_args; global = s.global; trap_stack = s.trap_stack;
    hp = ((addr, (tag, fields)) :: s.hp); next_addr = (Stdlib.Int.succ addr) }
  in
  (s', (Val_ptr addr))

(** val heap_update : heap -> int -> value list -> heap **)

let rec heap_update h addr fields =
  match h with
  | [] -> []
  | p :: rest ->
    let (a, p0) = p in
    let (t, fs) = p0 in
    if (=) a addr
    then (a, (t, fields)) :: rest
    else (a, (t, fs)) :: (heap_update rest addr fields)

(** val field_or_heap : state -> value -> int -> value option **)

let field_or_heap s v n0 =
  match v with
  | Val_int _ -> None
  | Val_block (_, fields) -> nth_error fields n0
  | Val_ptr addr ->
    (match heap_lookup s.hp addr with
     | Some p -> let (_, fields) = p in nth_error fields n0
     | None -> None)
  | Val_closure (addr, ofs) ->
    (match heap_lookup s.hp addr with
     | Some p -> let (_, fields) = p in nth_error fields (add ofs n0)
     | None -> None)

(** val tag_or_heap : state -> value -> int option **)

let tag_or_heap s = function
| Val_int _ -> None
| Val_block (t, _) -> Some t
| Val_ptr addr ->
  (match heap_lookup s.hp addr with
   | Some p -> let (t, _) = p in Some t
   | None -> None)
| Val_closure (addr, _) ->
  (match heap_lookup s.hp addr with
   | Some p -> let (t, _) = p in Some t
   | None -> None)

(** val size_or_heap : state -> value -> int option **)

let size_or_heap s = function
| Val_block (_, fields) -> Some (length fields)
| Val_ptr addr ->
  (match heap_lookup s.hp addr with
   | Some p -> let (_, fields) = p in Some (length fields)
   | None -> None)
| _ -> None

(** val initial_state : value list -> state **)

let initial_state global_data =
  { pc = 0; accu = val_unit; stack = []; env = val_unit; extra_args = 0;
    global = global_data; trap_stack = []; hp = []; next_addr = 0 }

(** val word_bits : int **)

let word_bits =
  ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->1+2*p) 1)))))

(** val z_unsigned : int -> int **)

let z_unsigned a =
  Z.coq_land a (Z.ones word_bits)

(** val z_lsr : int -> int -> int **)

let z_lsr a b =
  Z.shiftr (z_unsigned a) b

(** val get_code_ptr_from : value list -> int -> int option **)

let get_code_ptr_from fields ofs =
  match nth_error fields ofs with
  | Some v -> (match v with
               | Val_int pc0 -> Some pc0
               | _ -> None)
  | None -> None

(** val get_code_ptr_s : state -> value -> int option **)

let get_code_ptr_s s = function
| Val_block (t, fields) ->
  if (=) t closure_tag
  then (match fields with
        | [] -> None
        | v0 :: _ -> (match v0 with
                      | Val_int pc0 -> Some pc0
                      | _ -> None))
  else None
| Val_closure (addr, ofs) ->
  (match heap_lookup s.hp addr with
   | Some p ->
     let (t, fields) = p in
     if (=) t closure_tag then get_code_ptr_from fields ofs else None
   | None -> None)
| _ -> None

(** val st :
    state -> int -> value -> value list -> value -> int -> value list ->
    trap_frame list -> state **)

let st s pc0 accu0 stack0 env1 ea glob ts =
  { pc = pc0; accu = accu0; stack = stack0; env = env1; extra_args = ea;
    global = glob; trap_stack = ts; hp = s.hp; next_addr = s.next_addr }

(** val step : instruction list -> state -> step_result **)

let step code s =
  match nth_error code (Z.to_nat s.pc) with
  | Some instr ->
    let pc' = Z.add s.pc 1 in
    (match instr with
     | ACC n0 ->
       (match nth_error s.stack n0 with
        | Some v ->
          Step (st s pc' v s.stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('A'::('C'::('C'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))
     | PUSH ->
       Step
         (st s pc' s.accu (s.accu :: s.stack) s.env s.extra_args s.global
           s.trap_stack)
     | PUSHACC n0 ->
       let new_stack = s.accu :: s.stack in
       (match nth_error new_stack n0 with
        | Some v ->
          Step (st s pc' v new_stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('A'::('C'::('C'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
     | POP n0 ->
       Step
         (st s pc' s.accu (skipn n0 s.stack) s.env s.extra_args s.global
           s.trap_stack)
     | ASSIGN n0 ->
       (match set_nth s.stack n0 s.accu with
        | Some new_stack ->
          Step
            (st s pc' val_unit new_stack s.env s.extra_args s.global
              s.trap_stack)
        | None ->
          Error
            ('A'::('S'::('S'::('I'::('G'::('N'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))
     | ENVACC n0 ->
       (match field_or_heap s s.env n0 with
        | Some v ->
          Step (st s pc' v s.stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('E'::('N'::('V'::('A'::('C'::('C'::(':'::(' '::('e'::('n'::('v'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))
     | PUSHENVACC n0 ->
       let new_stack = s.accu :: s.stack in
       (match field_or_heap s s.env n0 with
        | Some v ->
          Step (st s pc' v new_stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('E'::('N'::('V'::('A'::('C'::('C'::(':'::(' '::('e'::('n'::('v'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))))
     | PUSH_RETADDR ret_addr ->
       let frame = (Val_int ret_addr) :: (s.env :: ((Val_int
         (Z.of_nat s.extra_args)) :: s.stack))
       in
       Step (st s pc' s.accu frame s.env s.extra_args s.global s.trap_stack)
     | APPLY n0 ->
       (match get_code_ptr_s s s.accu with
        | Some target_pc ->
          Step
            (st s target_pc s.accu s.stack s.accu
              (Nat.sub n0 (Stdlib.Int.succ 0)) s.global s.trap_stack)
        | None ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))
     | APPLY1 ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::('1'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
        | arg1 :: rest ->
          (match get_code_ptr_s s s.accu with
           | Some target_pc ->
             let new_stack = arg1 :: ((Val_int pc') :: (s.env :: ((Val_int
               (Z.of_nat s.extra_args)) :: rest)))
             in
             Step
             (st s target_pc s.accu new_stack s.accu 0 s.global s.trap_stack)
           | None ->
             Error
               ('A'::('P'::('P'::('L'::('Y'::('1'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))
     | APPLY2 ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
        | arg1 :: l ->
          (match l with
           | [] ->
             Error
               ('A'::('P'::('P'::('L'::('Y'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
           | arg2 :: rest ->
             (match get_code_ptr_s s s.accu with
              | Some target_pc ->
                let new_stack = arg1 :: (arg2 :: ((Val_int
                  pc') :: (s.env :: ((Val_int
                  (Z.of_nat s.extra_args)) :: rest))))
                in
                Step
                (st s target_pc s.accu new_stack s.accu (Stdlib.Int.succ 0)
                  s.global s.trap_stack)
              | None ->
                Error
                  ('A'::('P'::('P'::('L'::('Y'::('2'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))))
     | APPLY3 ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
        | arg1 :: l ->
          (match l with
           | [] ->
             Error
               ('A'::('P'::('P'::('L'::('Y'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
           | arg2 :: l0 ->
             (match l0 with
              | [] ->
                Error
                  ('A'::('P'::('P'::('L'::('Y'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
              | arg3 :: rest ->
                (match get_code_ptr_s s s.accu with
                 | Some target_pc ->
                   let new_stack = arg1 :: (arg2 :: (arg3 :: ((Val_int
                     pc') :: (s.env :: ((Val_int
                     (Z.of_nat s.extra_args)) :: rest)))))
                   in
                   Step
                   (st s target_pc s.accu new_stack s.accu (Stdlib.Int.succ
                     (Stdlib.Int.succ 0)) s.global s.trap_stack)
                 | None ->
                   Error
                     ('A'::('P'::('P'::('L'::('Y'::('3'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))))
     | APPTERM (nargs, slotsize) ->
       let args = firstn nargs s.stack in
       let base = skipn slotsize s.stack in
       (match get_code_ptr_s s s.accu with
        | Some target_pc ->
          Step
            (st s target_pc s.accu (app args base) s.accu
              (Nat.add s.extra_args (Nat.sub nargs (Stdlib.Int.succ 0)))
              s.global s.trap_stack)
        | None ->
          Error
            ('A'::('P'::('P'::('T'::('E'::('R'::('M'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))
     | APPTERM1 slotsize ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('1'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
        | arg1 :: _ ->
          let base = skipn slotsize s.stack in
          (match get_code_ptr_s s s.accu with
           | Some target_pc ->
             Step
               (st s target_pc s.accu (arg1 :: base) s.accu s.extra_args
                 s.global s.trap_stack)
           | None ->
             Error
               ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('1'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))))
     | APPTERM2 slotsize ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
        | arg1 :: l ->
          (match l with
           | [] ->
             Error
               ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
           | arg2 :: _ ->
             let base = skipn slotsize s.stack in
             (match get_code_ptr_s s s.accu with
              | Some target_pc ->
                Step
                  (st s target_pc s.accu (arg1 :: (arg2 :: base)) s.accu
                    (Nat.add s.extra_args (Stdlib.Int.succ 0)) s.global
                    s.trap_stack)
              | None ->
                Error
                  ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('2'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))))))
     | APPTERM3 slotsize ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
        | arg1 :: l ->
          (match l with
           | [] ->
             Error
               ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
           | arg2 :: l0 ->
             (match l0 with
              | [] ->
                Error
                  ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
              | arg3 :: _ ->
                let base = skipn slotsize s.stack in
                (match get_code_ptr_s s s.accu with
                 | Some target_pc ->
                   Step
                     (st s target_pc s.accu
                       (arg1 :: (arg2 :: (arg3 :: base))) s.accu
                       (Nat.add s.extra_args (Stdlib.Int.succ
                         (Stdlib.Int.succ 0)))
                       s.global s.trap_stack)
                 | None ->
                   Error
                     ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('3'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))))))
     | RETURN stacksize ->
       let stk = skipn stacksize s.stack in
       if Nat.ltb 0 s.extra_args
       then (match get_code_ptr_s s s.accu with
             | Some target_pc ->
               Step
                 (st s target_pc s.accu stk s.accu
                   (Nat.sub s.extra_args (Stdlib.Int.succ 0)) s.global
                   s.trap_stack)
             | None ->
               Error
                 ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))
       else (match stk with
             | [] ->
               Error
                 ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))
             | v :: l ->
               (match v with
                | Val_int ret_pc ->
                  (match l with
                   | [] ->
                     Error
                       ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))
                   | saved_env :: l0 ->
                     (match l0 with
                      | [] ->
                        Error
                          ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))
                      | v0 :: rest ->
                        (match v0 with
                         | Val_int saved_ea ->
                           Step
                             (st s ret_pc s.accu rest saved_env
                               (Z.to_nat saved_ea) s.global s.trap_stack)
                         | _ ->
                           Error
                             ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))))
                | _ ->
                  Error
                    ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))))
     | RESTART ->
       let restart_fields = fun all_fields ofs ->
         let fields = skipn ofs all_fields in
         let num_args =
           Nat.sub (length fields) (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0)))
         in
         let args =
           skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
             fields
         in
         let new_stack = app args s.stack in
         (match nth_error fields (Stdlib.Int.succ (Stdlib.Int.succ 0)) with
          | Some saved_env ->
            Step
              (st s pc' s.accu new_stack saved_env
                (Nat.add s.extra_args num_args) s.global s.trap_stack)
          | None ->
            Error
              ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))
       in
       (match s.env with
        | Val_block (t, fields) ->
          if (=) t closure_tag
          then restart_fields fields 0
          else Error
                 ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('e'::('n'::('v'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))
        | Val_closure (addr, ofs) ->
          (match heap_lookup s.hp addr with
           | Some p ->
             let (t, all_fields) = p in
             if (=) t closure_tag
             then restart_fields all_fields ofs
             else Error
                    ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('e'::('n'::('v'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))
           | None ->
             Error
               ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('d'::('a'::('n'::('g'::('l'::('i'::('n'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))))))))
        | _ ->
          Error
            ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('e'::('n'::('v'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('b'::('l'::('o'::('c'::('k'::[]))))))))))))))))))))))))))))
     | GRAB required ->
       if (<=) required s.extra_args
       then Step
              (st s pc' s.accu s.stack s.env (Nat.sub s.extra_args required)
                s.global s.trap_stack)
       else let num_args = Stdlib.Int.succ s.extra_args in
            let saved_args = firstn num_args s.stack in
            let rest_stack = skipn num_args s.stack in
            let closinfo = Val_int 0 in
            let fields = (Val_int
              (Z.sub s.pc 1)) :: (closinfo :: (s.env :: saved_args))
            in
            let (s', base_ptr) = heap_alloc s closure_tag fields in
            let addr = match base_ptr with
                       | Val_ptr a -> a
                       | _ -> 0 in
            let closure = Val_closure (addr, 0) in
            (match rest_stack with
             | [] ->
               Error
                 ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))
             | v :: l ->
               (match v with
                | Val_int ret_pc ->
                  (match l with
                   | [] ->
                     Error
                       ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))
                   | saved_env :: l0 ->
                     (match l0 with
                      | [] ->
                        Error
                          ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))
                      | v0 :: rest ->
                        (match v0 with
                         | Val_int saved_ea ->
                           Step
                             (st s' ret_pc closure rest saved_env
                               (Z.to_nat saved_ea) s.global s.trap_stack)
                         | _ ->
                           Error
                             ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))
                | _ ->
                  Error
                    ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))
     | CLOSURE (nvars, code_ofs) ->
       let stk = if Nat.ltb 0 nvars then s.accu :: s.stack else s.stack in
       let vars = firstn nvars stk in
       let rest = skipn nvars stk in
       let closinfo = Val_int 0 in
       let fields = (Val_int code_ofs) :: (closinfo :: vars) in
       let (s', base_ptr) = heap_alloc s closure_tag fields in
       let addr = match base_ptr with
                  | Val_ptr a -> a
                  | _ -> 0 in
       let closure = Val_closure (addr, 0) in
       Step (st s' pc' closure rest s.env s.extra_args s.global s.trap_stack)
     | CLOSUREREC (nfuncs, nvars, code_offsets) ->
       let stk = if Nat.ltb 0 nvars then s.accu :: s.stack else s.stack in
       let vars = firstn nvars stk in
       let rest = skipn nvars stk in
       (match code_offsets with
        | [] ->
          Error
            ('C'::('L'::('O'::('S'::('U'::('R'::('E'::('R'::('E'::('C'::(':'::(' '::('n'::('o'::(' '::('c'::('o'::('d'::('e'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::('s'::[])))))))))))))))))))))))))))
        | _ :: _ ->
          let closinfo = Val_int 0 in
          let infix_hdr = Val_block (infix_tag, []) in
          let build_closure_fields =
            let rec build_closure_fields i = function
            | [] -> vars
            | ofs :: rest_ofs ->
              if (=) i 0
              then (Val_int
                     ofs) :: (closinfo :: (build_closure_fields
                                            (Stdlib.Int.succ 0) rest_ofs))
              else infix_hdr :: ((Val_int
                     ofs) :: (closinfo :: (build_closure_fields
                                            (Stdlib.Int.succ i) rest_ofs)))
            in build_closure_fields
          in
          let fields = build_closure_fields 0 code_offsets in
          let (s', base_ptr) = heap_alloc s closure_tag fields in
          let addr = match base_ptr with
                     | Val_ptr a -> a
                     | _ -> 0 in
          let closure_at = fun i ->
            if (=) i 0
            then Val_closure (addr, 0)
            else Val_closure (addr,
                   (mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     0))) i))
          in
          let push_closures =
            let rec push_closures i stk0 =
              (fun fO fS n -> if n=0 then fO () else fS (n-1))
                (fun _ -> stk0)
                (fun i' ->
                let stk' = push_closures i' stk0 in (closure_at i') :: stk')
                i
            in push_closures
          in
          let new_stack = push_closures nfuncs rest in
          Step
          (st s' pc' (closure_at 0) new_stack s.env s.extra_args s.global
            s.trap_stack))
     | OFFSETCLOSURE ofs ->
       (match s.env with
        | Val_block (_, _) ->
          if Z.eqb ofs 0
          then Step
                 (st s pc' s.env s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Error
                 ('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('n'::('o'::('n'::('-'::('z'::('e'::('r'::('o'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('o'::('n'::(' '::('n'::('o'::('n'::('-'::('c'::('l'::('o'::('s'::('u'::('r'::('e'::(' '::('e'::('n'::('v'::[])))))))))))))))))))))))))))))))))))))))))))))))))
        | Val_closure (addr, base_ofs) ->
          let new_ofs = Z.to_nat (Z.add (Z.of_nat base_ofs) ofs) in
          let clos = Val_closure (addr, new_ofs) in
          Step
          (st s pc' clos s.stack s.env s.extra_args s.global s.trap_stack)
        | _ ->
          Error
            ('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('e'::('n'::('v'::[])))))))))))))))))))))))))))
     | PUSHOFFSETCLOSURE ofs ->
       let new_stack = s.accu :: s.stack in
       (match s.env with
        | Val_block (_, _) ->
          if Z.eqb ofs 0
          then Step
                 (st s pc' s.env new_stack s.env s.extra_args s.global
                   s.trap_stack)
          else Error
                 ('P'::('U'::('S'::('H'::('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('n'::('o'::('n'::('-'::('z'::('e'::('r'::('o'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('o'::('n'::(' '::('n'::('o'::('n'::('-'::('c'::('l'::('o'::('s'::('u'::('r'::('e'::(' '::('e'::('n'::('v'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))
        | Val_closure (addr, base_ofs) ->
          let new_ofs = Z.to_nat (Z.add (Z.of_nat base_ofs) ofs) in
          let clos = Val_closure (addr, new_ofs) in
          Step
          (st s pc' clos new_stack s.env s.extra_args s.global s.trap_stack)
        | _ ->
          Error
            ('P'::('U'::('S'::('H'::('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('i'::('n'::('v'::('a'::('l'::('i'::('d'::(' '::('e'::('n'::('v'::[])))))))))))))))))))))))))))))))
     | GETGLOBAL n0 ->
       (match nth_error s.global n0 with
        | Some v ->
          Step (st s pc' v s.stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))
     | PUSHGETGLOBAL n0 ->
       let new_stack = s.accu :: s.stack in
       (match nth_error s.global n0 with
        | Some v ->
          Step (st s pc' v new_stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
     | GETGLOBALFIELD (n0, p) ->
       (match nth_error s.global n0 with
        | Some glob ->
          (match field_or_heap s glob p with
           | Some v ->
             Step
               (st s pc' v s.stack s.env s.extra_args s.global s.trap_stack)
           | None ->
             Error
               ('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))
        | None ->
          Error
            ('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))))))
     | PUSHGETGLOBALFIELD (n0, p) ->
       let new_stack = s.accu :: s.stack in
       (match nth_error s.global n0 with
        | Some glob ->
          (match field_or_heap s glob p with
           | Some v ->
             Step
               (st s pc' v new_stack s.env s.extra_args s.global s.trap_stack)
           | None ->
             Error
               ('P'::('U'::('S'::('H'::('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('f'::('i'::('e'::('l'::('d'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))))))))))
     | SETGLOBAL n0 ->
       let new_global =
         match set_nth s.global n0 s.accu with
         | Some g -> g
         | None -> s.global
       in
       Step
       (st s pc' val_unit s.stack s.env s.extra_args new_global s.trap_stack)
     | ATOM t ->
       let (s', ptr) = heap_alloc s t [] in
       Step (st s' pc' ptr s.stack s.env s.extra_args s.global s.trap_stack)
     | PUSHATOM t ->
       let new_stack = s.accu :: s.stack in
       let (s', ptr) = heap_alloc s t [] in
       Step (st s' pc' ptr new_stack s.env s.extra_args s.global s.trap_stack)
     | MAKEBLOCK (t, size) ->
       let fields =
         s.accu :: (firstn (Nat.sub size (Stdlib.Int.succ 0)) s.stack)
       in
       let new_stack = skipn (Nat.sub size (Stdlib.Int.succ 0)) s.stack in
       let (s', ptr) = heap_alloc s t fields in
       Step (st s' pc' ptr new_stack s.env s.extra_args s.global s.trap_stack)
     | MAKEBLOCK1 t ->
       let (s', ptr) = heap_alloc s t (s.accu :: []) in
       Step (st s' pc' ptr s.stack s.env s.extra_args s.global s.trap_stack)
     | MAKEBLOCK2 t ->
       (match s.stack with
        | [] ->
          Error
            ('M'::('A'::('K'::('E'::('B'::('L'::('O'::('C'::('K'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))
        | v1 :: rest ->
          let (s', ptr) = heap_alloc s t (s.accu :: (v1 :: [])) in
          Step (st s' pc' ptr rest s.env s.extra_args s.global s.trap_stack))
     | MAKEBLOCK3 t ->
       (match s.stack with
        | [] ->
          Error
            ('M'::('A'::('K'::('E'::('B'::('L'::('O'::('C'::('K'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))
        | v1 :: l ->
          (match l with
           | [] ->
             Error
               ('M'::('A'::('K'::('E'::('B'::('L'::('O'::('C'::('K'::('3'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))
           | v2 :: rest ->
             let (s', ptr) = heap_alloc s t (s.accu :: (v1 :: (v2 :: []))) in
             Step
             (st s' pc' ptr rest s.env s.extra_args s.global s.trap_stack)))
     | MAKEFLOATBLOCK _ ->
       Error
         ('M'::('A'::('K'::('E'::('F'::('L'::('O'::('A'::('T'::('B'::('L'::('O'::('C'::('K'::(':'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))
     | GETFIELD n0 ->
       (match field_or_heap s s.accu n0 with
        | Some v ->
          Step (st s pc' v s.stack s.env s.extra_args s.global s.trap_stack)
        | None ->
          Error
            ('G'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))))))))))
     | GETFLOATFIELD _ ->
       Error
         ('G'::('E'::('T'::('F'::('L'::('O'::('A'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))
     | SETFIELD n0 ->
       (match s.stack with
        | [] ->
          Error
            ('S'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
        | newval :: rest ->
          (match s.accu with
           | Val_ptr addr ->
             (match heap_lookup s.hp addr with
              | Some p ->
                let (_, fields) = p in
                (match set_nth fields n0 newval with
                 | Some new_fields ->
                   let new_hp = heap_update s.hp addr new_fields in
                   Step { pc = pc'; accu = val_unit; stack = rest; env =
                   s.env; extra_args = s.extra_args; global = s.global;
                   trap_stack = s.trap_stack; hp = new_hp; next_addr =
                   s.next_addr }
                 | None ->
                   Error
                     ('S'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))
              | None ->
                Error
                  ('S'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('d'::('a'::('n'::('g'::('l'::('i'::('n'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[])))))))))))))))))))))))))))
           | _ ->
             Error
               ('S'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('m'::('u'::('t'::('a'::('b'::('l'::('e'::(' '::('b'::('l'::('o'::('c'::('k'::[])))))))))))))))))))))))))))))))
     | SETFLOATFIELD _ ->
       Error
         ('S'::('E'::('T'::('F'::('L'::('O'::('A'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))
     | VECTLENGTH ->
       (match size_or_heap s s.accu with
        | Some n0 ->
          Step
            (st s pc' (Val_int (Z.of_nat n0)) s.stack s.env s.extra_args
              s.global s.trap_stack)
        | None ->
          Error
            ('V'::('E'::('C'::('T'::('L'::('E'::('N'::('G'::('T'::('H'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('b'::('l'::('o'::('c'::('k'::[]))))))))))))))))))))))))
     | GETVECTITEM ->
       (match s.stack with
        | [] ->
          Error
            ('G'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('b'::('a'::('d'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))))
        | v :: rest ->
          (match v with
           | Val_int idx ->
             (match field_or_heap s s.accu (Z.to_nat idx) with
              | Some v0 ->
                Step
                  (st s pc' v0 rest s.env s.extra_args s.global s.trap_stack)
              | None ->
                Error
                  ('G'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))
           | _ ->
             Error
               ('G'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('b'::('a'::('d'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))))))
     | SETVECTITEM ->
       (match s.stack with
        | [] ->
          Error
            ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))
        | v :: l ->
          (match v with
           | Val_int idx ->
             (match l with
              | [] ->
                Error
                  ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))
              | newval :: rest ->
                (match s.accu with
                 | Val_ptr addr ->
                   (match heap_lookup s.hp addr with
                    | Some p ->
                      let (_, fields) = p in
                      (match set_nth fields (Z.to_nat idx) newval with
                       | Some new_fields ->
                         let new_hp = heap_update s.hp addr new_fields in
                         Step { pc = pc'; accu = val_unit; stack = rest;
                         env = s.env; extra_args = s.extra_args; global =
                         s.global; trap_stack = s.trap_stack; hp = new_hp;
                         next_addr = s.next_addr }
                       | None ->
                         Error
                           ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))
                    | None ->
                      Error
                        ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('d'::('a'::('n'::('g'::('l'::('i'::('n'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))))))))))))
                 | _ ->
                   Error
                     ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('h'::('e'::('a'::('p'::(' '::('b'::('l'::('o'::('c'::('k'::[])))))))))))))))))))))))))))))))
           | _ ->
             Error
               ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))
     | GETBYTESCHAR ->
       (match s.stack with
        | [] ->
          Error
            ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))
        | v :: rest ->
          (match v with
           | Val_int idx ->
             (match field_or_heap s s.accu (Z.to_nat idx) with
              | Some v0 ->
                (match v0 with
                 | Val_int c ->
                   Step
                     (st s pc' (Val_int c) rest s.env s.extra_args s.global
                       s.trap_stack)
                 | _ ->
                   Error
                     ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
              | None ->
                Error
                  ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
           | _ ->
             Error
               ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))
     | SETBYTESCHAR ->
       (match s.stack with
        | [] ->
          Error
            ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))
        | v :: l ->
          (match v with
           | Val_int idx ->
             (match l with
              | [] ->
                Error
                  ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))
              | v0 :: rest ->
                (match v0 with
                 | Val_int newchar ->
                   (match s.accu with
                    | Val_ptr addr ->
                      (match heap_lookup s.hp addr with
                       | Some p ->
                         let (_, fields) = p in
                         (match set_nth fields (Z.to_nat idx) (Val_int
                                  newchar) with
                          | Some new_fields ->
                            let new_hp = heap_update s.hp addr new_fields in
                            Step { pc = pc'; accu = val_unit; stack = rest;
                            env = s.env; extra_args = s.extra_args; global =
                            s.global; trap_stack = s.trap_stack; hp = new_hp;
                            next_addr = s.next_addr }
                          | None ->
                            Error
                              ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[]))))))))))))))))))))))))))))))))))
                       | None ->
                         Error
                           ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('d'::('a'::('n'::('g'::('l'::('i'::('n'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[])))))))))))))))))))))))))))))))
                    | _ ->
                      Error
                        ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('h'::('e'::('a'::('p'::(' '::('b'::('y'::('t'::('e'::('s'::[])))))))))))))))))))))))))))))))
                 | _ ->
                   Error
                     ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))
           | _ ->
             Error
               ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))
     | GETSTRINGCHAR ->
       (match s.stack with
        | [] ->
          Error
            ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))
        | v :: rest ->
          (match v with
           | Val_int idx ->
             (match field_or_heap s s.accu (Z.to_nat idx) with
              | Some v0 ->
                (match v0 with
                 | Val_int c ->
                   Step
                     (st s pc' (Val_int c) rest s.env s.extra_args s.global
                       s.trap_stack)
                 | _ ->
                   Error
                     ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
              | None ->
                Error
                  ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
           | _ ->
             Error
               ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))
     | BRANCH target ->
       Step
         (st s target s.accu s.stack s.env s.extra_args s.global s.trap_stack)
     | BRANCHIF target ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step
             (st s pc' s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s target s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s target s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             z0)
        | _ ->
          Step
            (st s target s.accu s.stack s.env s.extra_args s.global
              s.trap_stack))
     | BRANCHIFNOT target ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step
             (st s target s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s pc' s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s pc' s.accu s.stack s.env s.extra_args s.global
               s.trap_stack))
             z0)
        | _ ->
          Step
            (st s pc' s.accu s.stack s.env s.extra_args s.global s.trap_stack))
     | SWITCH (_, _, const_targets, block_targets) ->
       (match s.accu with
        | Val_int n0 ->
          (match nth_error const_targets (Z.to_nat n0) with
           | Some target ->
             Step
               (st s target s.accu s.stack s.env s.extra_args s.global
                 s.trap_stack)
           | None ->
             Error
               ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('r'::('a'::('n'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))
        | Val_block (t, _) ->
          (match nth_error block_targets t with
           | Some target ->
             Step
               (st s target s.accu s.stack s.env s.extra_args s.global
                 s.trap_stack)
           | None ->
             Error
               ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('b'::('l'::('o'::('c'::('k'::(' '::('t'::('a'::('g'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('r'::('a'::('n'::('g'::('e'::[])))))))))))))))))))))))))))))))
        | _ ->
          (match tag_or_heap s s.accu with
           | Some t ->
             (match nth_error block_targets t with
              | Some target ->
                Step
                  (st s target s.accu s.stack s.env s.extra_args s.global
                    s.trap_stack)
              | None ->
                Error
                  ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('b'::('l'::('o'::('c'::('k'::(' '::('t'::('a'::('g'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('r'::('a'::('n'::('g'::('e'::[])))))))))))))))))))))))))))))))
           | None ->
             Error
               ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('d'::('a'::('n'::('g'::('l'::('i'::('n'::('g'::(' '::('p'::('o'::('i'::('n'::('t'::('e'::('r'::[]))))))))))))))))))))))))))
     | BOOLNOT ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step
             (st s pc' val_true s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s pc' val_false s.stack s.env s.extra_args s.global
               s.trap_stack))
             (fun _ -> Step
             (st s pc' val_false s.stack s.env s.extra_args s.global
               s.trap_stack))
             z0)
        | _ ->
          Step
            (st s pc' val_false s.stack s.env s.extra_args s.global
              s.trap_stack))
     | PUSHTRAP handler_pc ->
       let trap_frame0 = (Val_int handler_pc) :: ((Val_int
         0) :: (s.env :: ((Val_int (Z.of_nat s.extra_args)) :: s.stack)))
       in
       let tf = { trap_pc = handler_pc; trap_sp_offset =
         (length trap_frame0); trap_env = s.env; trap_extra_args =
         s.extra_args }
       in
       Step
       (st s pc' s.accu trap_frame0 s.env s.extra_args s.global
         (tf :: s.trap_stack))
     | POPTRAP ->
       (match s.trap_stack with
        | [] ->
          Error
            ('P'::('O'::('P'::('T'::('R'::('A'::('P'::(':'::(' '::('n'::('o'::(' '::('t'::('r'::('a'::('p'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))
        | _ :: rest ->
          Step
            (st s pc' s.accu
              (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ 0)))) s.stack)
              s.env s.extra_args s.global rest))
     | RAISE ->
       (match s.trap_stack with
        | [] ->
          Error
            ('u'::('n'::('h'::('a'::('n'::('d'::('l'::('e'::('d'::(' '::('e'::('x'::('c'::('e'::('p'::('t'::('i'::('o'::('n'::[])))))))))))))))))))
        | tf :: rest ->
          let stack_depth = tf.trap_sp_offset in
          let restored = skipn (Nat.sub (length s.stack) stack_depth) s.stack
          in
          (match restored with
           | [] ->
             Step
               (st s tf.trap_pc s.accu
                 (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ 0)))) restored)
                 tf.trap_env tf.trap_extra_args s.global rest)
           | _ :: l ->
             (match l with
              | [] ->
                Step
                  (st s tf.trap_pc s.accu
                    (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ 0)))) restored)
                    tf.trap_env tf.trap_extra_args s.global rest)
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step
                     (st s tf.trap_pc s.accu
                       (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                       tf.trap_env tf.trap_extra_args s.global rest)
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step
                        (st s tf.trap_pc s.accu
                          (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                          tf.trap_env tf.trap_extra_args s.global rest)
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step
                           (st s tf.trap_pc s.accu real_stack saved_env
                             (Z.to_nat saved_ea) s.global rest)
                       | _ ->
                         Step
                           (st s tf.trap_pc s.accu
                             (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                               restored)
                             tf.trap_env tf.trap_extra_args s.global rest)))))))
     | RERAISE ->
       (match s.trap_stack with
        | [] ->
          Error
            ('u'::('n'::('h'::('a'::('n'::('d'::('l'::('e'::('d'::(' '::('e'::('x'::('c'::('e'::('p'::('t'::('i'::('o'::('n'::[])))))))))))))))))))
        | tf :: rest ->
          let stack_depth = tf.trap_sp_offset in
          let restored = skipn (Nat.sub (length s.stack) stack_depth) s.stack
          in
          (match restored with
           | [] ->
             Step
               (st s tf.trap_pc s.accu
                 (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ 0)))) restored)
                 tf.trap_env tf.trap_extra_args s.global rest)
           | _ :: l ->
             (match l with
              | [] ->
                Step
                  (st s tf.trap_pc s.accu
                    (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ 0)))) restored)
                    tf.trap_env tf.trap_extra_args s.global rest)
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step
                     (st s tf.trap_pc s.accu
                       (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                       tf.trap_env tf.trap_extra_args s.global rest)
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step
                        (st s tf.trap_pc s.accu
                          (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                          tf.trap_env tf.trap_extra_args s.global rest)
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step
                           (st s tf.trap_pc s.accu real_stack saved_env
                             (Z.to_nat saved_ea) s.global rest)
                       | _ ->
                         Step
                           (st s tf.trap_pc s.accu
                             (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                               restored)
                             tf.trap_env tf.trap_extra_args s.global rest)))))))
     | RAISE_NOTRACE ->
       (match s.trap_stack with
        | [] ->
          Error
            ('u'::('n'::('h'::('a'::('n'::('d'::('l'::('e'::('d'::(' '::('e'::('x'::('c'::('e'::('p'::('t'::('i'::('o'::('n'::[])))))))))))))))))))
        | tf :: rest ->
          let stack_depth = tf.trap_sp_offset in
          let restored = skipn (Nat.sub (length s.stack) stack_depth) s.stack
          in
          (match restored with
           | [] ->
             Step
               (st s tf.trap_pc s.accu
                 (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ 0)))) restored)
                 tf.trap_env tf.trap_extra_args s.global rest)
           | _ :: l ->
             (match l with
              | [] ->
                Step
                  (st s tf.trap_pc s.accu
                    (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                      (Stdlib.Int.succ 0)))) restored)
                    tf.trap_env tf.trap_extra_args s.global rest)
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step
                     (st s tf.trap_pc s.accu
                       (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                         (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                       tf.trap_env tf.trap_extra_args s.global rest)
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step
                        (st s tf.trap_pc s.accu
                          (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored)
                          tf.trap_env tf.trap_extra_args s.global rest)
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step
                           (st s tf.trap_pc s.accu real_stack saved_env
                             (Z.to_nat saved_ea) s.global rest)
                       | _ ->
                         Step
                           (st s tf.trap_pc s.accu
                             (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                               (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                               restored)
                             tf.trap_env tf.trap_extra_args s.global rest)))))))
     | C_CALL (nargs, prim_idx) ->
       let args =
         s.accu :: (firstn (Nat.sub nargs (Stdlib.Int.succ 0)) s.stack)
       in
       let new_stack = skipn (Nat.sub nargs (Stdlib.Int.succ 0)) s.stack in
       let cont =
         st s pc' val_unit new_stack s.env s.extra_args s.global s.trap_stack
       in
       CCall_request (prim_idx, args, cont)
     | CONSTINT n0 ->
       Step
         (st s pc' (Val_int n0) s.stack s.env s.extra_args s.global
           s.trap_stack)
     | PUSHCONSTINT n0 ->
       let new_stack = s.accu :: s.stack in
       Step
       (st s pc' (Val_int n0) new_stack s.env s.extra_args s.global
         s.trap_stack)
     | NEGINT ->
       (match s.accu with
        | Val_int n0 ->
          Step
            (st s pc' (Val_int (Z.opp n0)) s.stack s.env s.extra_args
              s.global s.trap_stack)
        | _ ->
          Error
            ('N'::('E'::('G'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | ADDINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('A'::('D'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.add a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('A'::('D'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('A'::('D'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | SUBINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('S'::('U'::('B'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.sub a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('S'::('U'::('B'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('S'::('U'::('B'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | MULINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('M'::('U'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.mul a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('M'::('U'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('M'::('U'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | DIVINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('D'::('I'::('V'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                if Z.eqb b 0
                then Error
                       ('D'::('I'::('V'::('I'::('N'::('T'::(':'::(' '::('d'::('i'::('v'::('i'::('s'::('i'::('o'::('n'::(' '::('b'::('y'::(' '::('z'::('e'::('r'::('o'::[]))))))))))))))))))))))))
                else Step
                       (st s pc' (Val_int (Z.quot a b)) rest s.env
                         s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('D'::('I'::('V'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('D'::('I'::('V'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | MODINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('M'::('O'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                if Z.eqb b 0
                then Error
                       ('M'::('O'::('D'::('I'::('N'::('T'::(':'::(' '::('d'::('i'::('v'::('i'::('s'::('i'::('o'::('n'::(' '::('b'::('y'::(' '::('z'::('e'::('r'::('o'::[]))))))))))))))))))))))))
                else Step
                       (st s pc' (Val_int (Z.rem a b)) rest s.env
                         s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('M'::('O'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('M'::('O'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | ANDINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('A'::('N'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.coq_land a b)) rest s.env
                    s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('A'::('N'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('A'::('N'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | ORINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.coq_lor a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | XORINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('X'::('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.coq_lxor a b)) rest s.env
                    s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('X'::('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('X'::('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | LSLINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('L'::('S'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.shiftl a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('L'::('S'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('L'::('S'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | LSRINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('L'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (z_lsr a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('L'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('L'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | ASRINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('A'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (Val_int (Z.shiftr a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('A'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('A'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | EQ ->
       (match s.stack with
        | [] ->
          Error
            ('E'::('Q'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))
        | b :: rest ->
          Step
            (st s pc' (if value_eqb s.accu b then val_true else val_false)
              rest s.env s.extra_args s.global s.trap_stack))
     | NEQ ->
       (match s.stack with
        | [] ->
          Error
            ('N'::('E'::('Q'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))
        | b :: rest ->
          Step
            (st s pc' (if value_eqb s.accu b then val_false else val_true)
              rest s.env s.extra_args s.global s.trap_stack))
     | LTINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.ltb a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | LEINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('L'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.leb a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('L'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('L'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | GTINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('G'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.gtb a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('G'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('G'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | GEINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.geb a b)) rest s.env s.extra_args
                    s.global s.trap_stack)
              | _ ->
                Error
                  ('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | OFFSETINT n0 ->
       (match s.accu with
        | Val_int a ->
          Step
            (st s pc' (Val_int (Z.add a n0)) s.stack s.env s.extra_args
              s.global s.trap_stack)
        | _ ->
          Error
            ('O'::('F'::('F'::('S'::('E'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))))
     | OFFSETREF n0 ->
       (match s.accu with
        | Val_ptr addr ->
          (match heap_lookup s.hp addr with
           | Some p ->
             let (_, l) = p in
             (match l with
              | [] ->
                Error
                  ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[]))))))))))))))))))))
              | v :: rest ->
                (match v with
                 | Val_int old ->
                   let new_hp =
                     heap_update s.hp addr ((Val_int (Z.add old n0)) :: rest)
                   in
                   Step { pc = pc'; accu = val_unit; stack = s.stack; env =
                   s.env; extra_args = s.extra_args; global = s.global;
                   trap_stack = s.trap_stack; hp = new_hp; next_addr =
                   s.next_addr }
                 | _ ->
                   Error
                     ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[]))))))))))))))))))))))
           | None ->
             Error
               ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[])))))))))))))))))))))
        | _ ->
          Error
            ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[])))))))))))))))))))))
     | ISINT ->
       Step
         (st s pc' (if is_int s.accu then val_true else val_false) s.stack
           s.env s.extra_args s.global s.trap_stack)
     | GETMETHOD ->
       Error
         ('G'::('E'::('T'::('M'::('E'::('T'::('H'::('O'::('D'::(':'::(' '::('O'::('O'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))
     | GETPUBMET _ ->
       Error
         ('G'::('E'::('T'::('P'::('U'::('B'::('M'::('E'::('T'::(':'::(' '::('O'::('O'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))
     | GETDYNMET ->
       Error
         ('G'::('E'::('T'::('D'::('Y'::('N'::('M'::('E'::('T'::(':'::(' '::('O'::('O'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))
     | BEQ (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.eqb a n0
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('E'::('Q'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))
     | BNEQ (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.eqb a n0
          then Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('N'::('E'::('Q'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))
     | BLTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.ltb n0 a
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BLEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.leb n0 a
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('L'::('E'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BGTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.gtb n0 a
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('G'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BGEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.geb n0 a
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | ULTINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.ltb (z_unsigned a) (z_unsigned b)))
                    rest s.env s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | UGEINT ->
       (match s.accu with
        | Val_int a ->
          (match s.stack with
           | [] ->
             Error
               ('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
           | v :: rest ->
             (match v with
              | Val_int b ->
                Step
                  (st s pc' (val_bool (Z.geb (z_unsigned a) (z_unsigned b)))
                    rest s.env s.extra_args s.global s.trap_stack)
              | _ ->
                Error
                  ('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | _ ->
          Error
            ('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | BULTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.ltb (z_unsigned n0) (z_unsigned a)
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))
     | BUGEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.geb (z_unsigned n0) (z_unsigned a)
          then Step
                 (st s target s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
          else Step
                 (st s pc' s.accu s.stack s.env s.extra_args s.global
                   s.trap_stack)
        | _ ->
          Error
            ('B'::('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))
     | STOP -> Halt s.accu
     | PERFORM ->
       Error
         ('P'::('E'::('R'::('F'::('O'::('R'::('M'::(':'::(' '::('e'::('f'::('f'::('e'::('c'::('t'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))
     | RESUME ->
       Error
         ('R'::('E'::('S'::('U'::('M'::('E'::(':'::(' '::('e'::('f'::('f'::('e'::('c'::('t'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))
     | RESUMETERM _ ->
       Error
         ('R'::('E'::('S'::('U'::('M'::('E'::('T'::('E'::('R'::('M'::(':'::(' '::('e'::('f'::('f'::('e'::('c'::('t'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))
     | REPERFORMTERM _ ->
       Error
         ('R'::('E'::('P'::('E'::('R'::('F'::('O'::('R'::('M'::('T'::('E'::('R'::('M'::(':'::(' '::('e'::('f'::('f'::('e'::('c'::('t'::('s'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))
     | _ ->
       Step (st s pc' s.accu s.stack s.env s.extra_args s.global s.trap_stack))
  | None ->
    Error
      ('p'::('c'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[]))))))))))))))))

(** val run :
    int -> instruction list -> state -> (int -> value list -> value option)
    -> run_result **)

let rec run fuel code s handle_ccall =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Out_of_fuel s)
    (fun fuel' ->
    match step code s with
    | Step s' -> run fuel' code s' handle_ccall
    | Halt v -> Finished v
    | Error msg -> Run_error msg
    | CCall_request (prim_idx, args, cont) ->
      (match handle_ccall prim_idx args with
       | Some result0 -> run fuel' code (set_accu cont result0) handle_ccall
       | None ->
         Run_error
           ('C'::(' '::('c'::('a'::('l'::('l'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))))
    fuel

(** val run_pure : int -> instruction list -> value list -> run_result **)

let run_pure fuel code global_data =
  run fuel code (initial_state global_data) (fun _ _ -> None)

(** val instr_word_size : instruction -> int **)

let instr_word_size = function
| ACC _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHACC _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| POP _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| ASSIGN _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| ENVACC _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHENVACC _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSH_RETADDR _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| APPLY _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| APPTERM (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| APPTERM1 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| APPTERM2 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| APPTERM3 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| RETURN _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GRAB _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| CLOSURE (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| CLOSUREREC (_, _, ofs) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (length ofs)
| OFFSETCLOSURE _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHOFFSETCLOSURE _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GETGLOBAL _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHGETGLOBAL _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GETGLOBALFIELD (_, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| PUSHGETGLOBALFIELD (_, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| SETGLOBAL _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| ATOM _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHATOM _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| MAKEBLOCK (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| MAKEBLOCK1 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| MAKEBLOCK2 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| MAKEBLOCK3 _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| MAKEFLOATBLOCK _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GETFIELD _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GETFLOATFIELD _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| SETFIELD _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| SETFLOATFIELD _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| BRANCH _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| BRANCHIF _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| BRANCHIFNOT _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| SWITCH (_, _, ct, bt) ->
  add (add (Stdlib.Int.succ (Stdlib.Int.succ 0)) (length ct)) (length bt)
| PUSHTRAP _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| C_CALL (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| CONSTINT _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| PUSHCONSTINT _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| OFFSETINT _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| OFFSETREF _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| GETPUBMET _ -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BEQ (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BNEQ (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BLTINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BLEINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BGTINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BGEINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BULTINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| BUGEINT (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))
| RESUMETERM _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| REPERFORMTERM _ -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| _ -> Stdlib.Int.succ 0

(** val build_offset_list : instruction list -> int -> int list **)

let rec build_offset_list code acc =
  match code with
  | [] -> []
  | i :: rest -> acc :: (build_offset_list rest (add acc (instr_word_size i)))

(** val offset_map : instruction list -> int list **)

let offset_map code =
  build_offset_list code 0

(** val lookup_offset : int list -> int -> int **)

let lookup_offset omap idx =
  match nth_error omap (Z.to_nat idx) with
  | Some n0 -> Z.of_nat n0
  | None -> 0

(** val encode_word_le : int -> int list **)

let encode_word_le v =
  let u =
    Z.coq_land v ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      1)))))))))))))))))))))))))))))))
  in
  let b0 =
    Z.coq_land u ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
  in
  let b1 =
    Z.coq_land (Z.shiftr u ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
  in
  let b2 =
    Z.coq_land
      (Z.shiftr u ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        1)))))
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
  in
  let b3 =
    Z.coq_land
      (Z.shiftr u ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
        1)))))
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))))
  in
  b0 :: (b1 :: (b2 :: (b3 :: [])))

(** val emit_words : int list -> int list **)

let emit_words ws =
  flat_map encode_word_le ws

(** val rel_offset : int list -> int -> int -> int **)

let rel_offset omap from_word target_idx =
  Z.sub (lookup_offset omap target_idx) from_word

(** val encode_instr : int list -> int -> instruction -> int list **)

let encode_instr omap idx i =
  let w = Z.of_nat (match nth_error omap idx with
                    | Some n0 -> n0
                    | None -> 0)
  in
  (match i with
   | ACC n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))) :: ((Z.of_nat n0) :: []))
   | PUSH ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))) :: [])
   | PUSHACC n0 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1)))) :: ((Z.of_nat n0) :: []))
   | POP n0 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1)))) :: ((Z.of_nat n0) :: []))
   | ASSIGN n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       1)))) :: ((Z.of_nat n0) :: []))
   | ENVACC n0 ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       1)))) :: ((Z.of_nat n0) :: []))
   | PUSHENVACC n0 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1)))) :: ((Z.of_nat n0) :: []))
   | PUSH_RETADDR t ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1)))) :: ((rel_offset omap (Z.add w 1) t) :: []))
   | APPLY n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | APPLY1 ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: [])
   | APPLY2 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: [])
   | APPLY3 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: [])
   | APPTERM (n0, s) ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat n0) :: ((Z.of_nat s) :: [])))
   | APPTERM1 s ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat s) :: []))
   | APPTERM2 s ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat s) :: []))
   | APPTERM3 s ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) 1))))) :: ((Z.of_nat s) :: []))
   | RETURN n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | RESTART ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) 1))))) :: [])
   | GRAB n0 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | CLOSURE (nv, codeptr) ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p)
       1))))) :: ((Z.of_nat nv) :: ((rel_offset omap
                                      (Z.add w ((fun p->2*p) 1)) codeptr) :: [])))
   | CLOSUREREC (nf, nv, ofs_list) ->
     emit_words
       (app (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p) 1))))) :: ((Z.of_nat nf) :: ((Z.of_nat nv) :: [])))
         (map (fun t -> rel_offset omap (Z.add w ((fun p->1+2*p) 1)) t)
           ofs_list))
   | OFFSETCLOSURE n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) 1))))) :: (n0 :: []))
   | PUSHOFFSETCLOSURE n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) 1))))) :: (n0 :: []))
   | GETGLOBAL n0 ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | PUSHGETGLOBAL n0 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | GETGLOBALFIELD (n0, p) ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->1+2*p)
       1))))) :: ((Z.of_nat n0) :: ((Z.of_nat p) :: [])))
   | PUSHGETGLOBALFIELD (n0, p) ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1))))) :: ((Z.of_nat n0) :: ((Z.of_nat p) :: [])))
   | SETGLOBAL n0 ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1))))) :: ((Z.of_nat n0) :: []))
   | ATOM t ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1))))) :: ((Z.of_nat t) :: []))
   | PUSHATOM t ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1))))) :: ((Z.of_nat t) :: []))
   | MAKEBLOCK (tag, sz) ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p)
       1))))) :: ((Z.of_nat sz) :: ((Z.of_nat tag) :: [])))
   | MAKEBLOCK1 t ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1))))) :: ((Z.of_nat t) :: []))
   | MAKEBLOCK2 t ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) 1)))))) :: ((Z.of_nat t) :: []))
   | MAKEBLOCK3 t ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) 1)))))) :: ((Z.of_nat t) :: []))
   | MAKEFLOATBLOCK s ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) 1)))))) :: ((Z.of_nat s) :: []))
   | GETFIELD n0 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1)))))) :: ((Z.of_nat n0) :: []))
   | GETFLOATFIELD n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) 1)))))) :: ((Z.of_nat n0) :: []))
   | SETFIELD n0 ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1)))))) :: ((Z.of_nat n0) :: []))
   | SETFLOATFIELD n0 ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1)))))) :: ((Z.of_nat n0) :: []))
   | VECTLENGTH ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))) :: [])
   | GETVECTITEM ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | SETVECTITEM ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | GETBYTESCHAR ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | SETBYTESCHAR ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | GETSTRINGCHAR ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | BRANCH t ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p)
       1)))))) :: ((rel_offset omap (Z.add w 1) t) :: []))
   | BRANCHIF t ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p)
       1)))))) :: ((rel_offset omap (Z.add w 1) t) :: []))
   | BRANCHIFNOT t ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p)
       1)))))) :: ((rel_offset omap (Z.add w 1) t) :: []))
   | SWITCH (nc, nb, ct, bt) ->
     let sizes =
       Z.coq_lor (Z.of_nat nc)
         (Z.shiftl (Z.of_nat nb) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) 1)))))
     in
     let base = Z.add w ((fun p->2*p) 1) in
     let ct_rels = map (fun t -> rel_offset omap base t) ct in
     let bt_rels = map (fun t -> rel_offset omap base t) bt in
     emit_words
       (app (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
         ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: (sizes :: []))
         (app ct_rels bt_rels))
   | BOOLNOT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | PUSHTRAP t ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p)
       1)))))) :: ((rel_offset omap (Z.add w 1) t) :: []))
   | POPTRAP ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | RAISE ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | RERAISE ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | RAISE_NOTRACE ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | CHECK_SIGNALS ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) 1)))))) :: [])
   | C_CALL (narg, prim) ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->1+2*p)
       1)))))) :: ((Z.of_nat narg) :: ((Z.of_nat prim) :: [])))
   | CONSTINT n0 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))) :: (n0 :: []))
   | PUSHCONSTINT n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->1+2*p) 1)))))) :: (n0 :: []))
   | NEGINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))) :: [])
   | ADDINT ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))) :: [])
   | SUBINT ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) 1)))))) :: [])
   | MULINT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | DIVINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | MODINT ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | ANDINT ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | ORINT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | XORINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | LSLINT ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | LSRINT ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | ASRINT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | EQ ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | NEQ ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | LTINT ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | LEINT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | GTINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | GEINT ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: [])
   | OFFSETINT n0 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) 1)))))) :: (n0 :: []))
   | OFFSETREF n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: (n0 :: []))
   | ISINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | GETMETHOD ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | GETPUBMET t ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (t :: (0 :: [])))
   | GETDYNMET ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: [])
   | BEQ (n0, t) ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BNEQ (n0, t) ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BLTINT (n0, t) ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BLEINT (n0, t) ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BGTINT (n0, t) ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BGEINT (n0, t) ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | ULTINT ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | UGEINT ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | BULTINT (n0, t) ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | BUGEINT (n0, t) ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: (n0 :: ((rel_offset omap (Z.add w ((fun p->2*p) 1)) t) :: [])))
   | STOP ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: [])
   | EVENT ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | BREAK ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | PERFORM ->
     emit_words (((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | RESUME ->
     emit_words (((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1))))))) :: [])
   | RESUMETERM n0 ->
     emit_words (((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: ((Z.of_nat n0) :: []))
   | REPERFORMTERM n0 ->
     emit_words (((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
       1))))))) :: ((Z.of_nat n0) :: [])))

(** val encode_instrs : int list -> int -> instruction list -> int list **)

let rec encode_instrs omap idx = function
| [] -> []
| i :: rest ->
  app (encode_instr omap idx i)
    (encode_instrs omap (Stdlib.Int.succ idx) rest)

(** val encode_bytecode : instruction list -> int list **)

let encode_bytecode code =
  let omap = offset_map code in encode_instrs omap 0 code

type byte_string = bytes

(** val read_file : int list -> byte_string **)

let read_file = 
  fun cs ->
    let buf = Buffer.create 256 in
    let rec to_chars = function
      | [] -> ()
      | c :: rest -> Buffer.add_char buf (Char.chr c); to_chars rest
    in
    to_chars cs;
    let filename = Buffer.contents buf in
    let ic = open_in_bin filename in
    let n = in_channel_length ic in
    let data = Bytes.create n in
    really_input ic data 0 n;
    close_in ic;
    data


(** val byte_string_to_list : byte_string -> int list **)

let byte_string_to_list = 
  fun bs ->
    let n = Bytes.length bs in
    let rec build i acc =
      if i < 0 then acc
      else build (i - 1) (Char.code (Bytes.get bs i) :: acc)
    in
    build (n - 1) []


(** val byte_string_length : byte_string -> int **)

let byte_string_length = 
  fun bs -> Bytes.length bs


(** val sys_argv : int list list **)

let sys_argv = 
  let argv = Array.to_list Sys.argv in
  List.map (fun s ->
    let n = String.length s in
    let rec build i acc =
      if i < 0 then acc
      else build (i - 1) (Char.code s.[i] :: acc)
    in
    build (n - 1) []
  ) argv


(** val unmarshal_globals : byte_string -> int -> int -> int list list **)

let unmarshal_globals = 
  fun bs ofs len ->
    let sub = Bytes.sub bs ofs len in
    let obj : Obj.t = Marshal.from_bytes sub 0 in
    let arr : Obj.t array = Obj.obj obj in
    let rec obj_to_encoding (o : Obj.t) : int list =
      if Obj.is_int o then [0; (Obj.obj o : int)]
      else
        let tag = Obj.tag o in
        if tag = Obj.string_tag then
          let s : string = Obj.obj o in
          let n = String.length s in
          let rec chars i acc =
            if i < 0 then acc
            else chars (i - 1) (Char.code s.[i] :: acc)
          in
          2 :: n :: chars (n - 1) []
        else if tag < Obj.no_scan_tag then
          let size = Obj.size o in
          let fields = List.concat_map (fun i ->
            obj_to_encoding (Obj.field o i)
          ) (List.init size Fun.id) in
          1 :: tag :: size :: fields
        else
          [1; tag; 0]
    in
    Array.to_list (Array.map obj_to_encoding arr)


(** val load_primitives : byte_string -> int -> int -> int list list **)

let load_primitives = 
  fun bs ofs len ->
    let raw = Bytes.sub_string bs ofs len in
    let prims = List.filter (fun s -> String.length s > 0)
                  (String.split_on_char '\000' raw) in
    List.map (fun s ->
      let n = String.length s in
      let rec build i acc =
        if i < 0 then acc
        else build (i - 1) (Char.code s.[i] :: acc)
      in
      build (n - 1) []
    ) prims


(** val byte_at : int list -> int -> int **)

let rec byte_at data off =
  match data with
  | [] -> 0
  | b :: rest ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> b)
       (fun n0 -> byte_at rest n0)
       off)

(** val read_u32_le : int list -> int -> int **)

let read_u32_le data off =
  let b0 = byte_at data off in
  let b1 = byte_at data (Stdlib.Int.succ off) in
  let b2 = byte_at data (Stdlib.Int.succ (Stdlib.Int.succ off)) in
  let b3 =
    byte_at data (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ off)))
  in
  Z.coq_lor b0
    (Z.coq_lor (Z.shiftl b1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
      (Z.coq_lor
        (Z.shiftl b2 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          1)))))
        (Z.shiftl b3 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->1+2*p) 1)))))))

(** val read_i32_le : int list -> int -> int **)

let read_i32_le data off =
  let u = read_u32_le data off in
  if Z.testbit u ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1))))
  then Z.coq_lor u
         (Z.lnot
           (Z.ones ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
             ((fun p->2*p) 1)))))))
  else u

(** val read_u32_be : int list -> int -> int **)

let read_u32_be data off =
  let b0 = byte_at data off in
  let b1 = byte_at data (Stdlib.Int.succ off) in
  let b2 = byte_at data (Stdlib.Int.succ (Stdlib.Int.succ off)) in
  let b3 =
    byte_at data (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ off)))
  in
  Z.coq_lor
    (Z.shiftl b0 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
      1)))))
    (Z.coq_lor
      (Z.shiftl b1 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        1)))))
      (Z.coq_lor (Z.shiftl b2 ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))
        b3))

type section = { sec_name : int; sec_offset : int; sec_length : int }

(** val sum_section_lengths : int list -> int -> int -> int **)

let rec sum_section_lengths data toc_offset n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun n' ->
    let len =
      Z.to_nat
        (read_u32_be data
          (add
            (add toc_offset
              (mul n' (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0))))))
    in
    add len (sum_section_lengths data toc_offset n'))
    n0

(** val build_sections :
    int list -> int -> int -> int -> int -> section list **)

let rec build_sections data toc_offset current i count =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun count' ->
    let entry =
      add toc_offset
        (mul i (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))))))
    in
    let name = read_u32_be data entry in
    let slen =
      Z.to_nat
        (read_u32_be data
          (add entry (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0))))))
    in
    { sec_name = name; sec_offset = current; sec_length =
    slen } :: (build_sections data toc_offset (add current slen)
                (Stdlib.Int.succ i) count'))
    count

(** val parse_sections : int list -> int -> section list **)

let parse_sections data data_len =
  let num_sections =
    Z.to_nat
      (read_u32_be data
        (sub data_len (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0))))))))))))))))))
  in
  let toc_offset =
    sub
      (sub data_len (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))))
      (mul num_sections (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))
  in
  let total_data = sum_section_lengths data toc_offset num_sections in
  let data_start = sub toc_offset total_data in
  build_sections data toc_offset data_start 0 num_sections

(** val cODE_name : int **)

let cODE_name =
  Z.coq_lor
    (Z.shiftl ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1)))))
    (Z.coq_lor
      (Z.shiftl ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
        ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))))
      (Z.coq_lor
        (Z.shiftl ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
        ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1))))))))

(** val find_section : section list -> int -> section option **)

let rec find_section secs name =
  match secs with
  | [] -> None
  | s :: rest ->
    if Z.eqb s.sec_name name then Some s else find_section rest name

type raw_instr = { ri_word_offset : int; ri_opcode : int;
                   ri_operands : int list }

(** val operand_count : int -> int option **)

let operand_count op =
  if Z.eqb op ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1)))
  then Some (Stdlib.Int.succ 0)
  else if Z.eqb op ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
            1))))
       then Some (Stdlib.Int.succ 0)
       else if Z.eqb op ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->2*p)
                 ((fun p->2*p) 1))))
            then Some (Stdlib.Int.succ 0)
            else if Z.eqb op ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
                      ((fun p->2*p) 1))))
                 then Some (Stdlib.Int.succ 0)
                 else if Z.eqb op ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
                           ((fun p->1+2*p) 1))))
                      then Some (Stdlib.Int.succ 0)
                      else if Z.eqb op ((fun p->2*p) ((fun p->1+2*p)
                                ((fun p->1+2*p) ((fun p->1+2*p) 1))))
                           then Some (Stdlib.Int.succ 0)
                           else if Z.eqb op ((fun p->1+2*p) ((fun p->1+2*p)
                                     ((fun p->1+2*p) ((fun p->1+2*p) 1))))
                                then Some (Stdlib.Int.succ 0)
                                else if Z.eqb op ((fun p->2*p) ((fun p->2*p)
                                          ((fun p->2*p) ((fun p->2*p)
                                          ((fun p->2*p) 1)))))
                                     then Some (Stdlib.Int.succ 0)
                                     else if Z.eqb op ((fun p->1+2*p)
                                               ((fun p->2*p) ((fun p->1+2*p)
                                               ((fun p->2*p) ((fun p->2*p)
                                               1)))))
                                          then Some (Stdlib.Int.succ 0)
                                          else if Z.eqb op ((fun p->2*p)
                                                    ((fun p->1+2*p)
                                                    ((fun p->1+2*p)
                                                    ((fun p->2*p)
                                                    ((fun p->2*p) 1)))))
                                               then Some (Stdlib.Int.succ 0)
                                               else if Z.eqb op
                                                         ((fun p->1+2*p)
                                                         ((fun p->1+2*p)
                                                         ((fun p->1+2*p)
                                                         ((fun p->2*p)
                                                         ((fun p->2*p) 1)))))
                                                    then Some
                                                           (Stdlib.Int.succ 0)
                                                    else if Z.eqb op
                                                              ((fun p->2*p)
                                                              ((fun p->2*p)
                                                              ((fun p->2*p)
                                                              ((fun p->1+2*p)
                                                              ((fun p->2*p)
                                                              1)))))
                                                         then Some
                                                                (Stdlib.Int.succ
                                                                0)
                                                         else if Z.eqb op
                                                                   ((fun p->2*p)
                                                                   ((fun p->1+2*p)
                                                                   ((fun p->2*p)
                                                                   ((fun p->1+2*p)
                                                                   ((fun p->2*p)
                                                                   1)))))
                                                              then Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                              else if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                   then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                   else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    Some
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then None
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then None
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then None
                                                                    else 
                                                                    Some 0

(** val read_operands : int list -> int -> int -> int -> int list * int **)

let rec read_operands data code_offset pos n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ([], pos))
    (fun n' ->
    let v = read_i32_le data (add code_offset pos) in
    let (rest, pos') =
      read_operands data code_offset
        (add pos (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0)))))
        n'
    in
    ((v :: rest), pos'))
    n0

(** val decode_raw_aux :
    int list -> int -> int -> int -> int -> raw_instr list **)

let rec decode_raw_aux data code_offset code_length pos fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun fuel' ->
    if (<=) code_length pos
    then []
    else let word =
           Nat.div pos (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0))))
         in
         let op = read_u32_le data (add code_offset pos) in
         let pos1 =
           add pos (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
             (Stdlib.Int.succ 0))))
         in
         if Z.eqb op ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
              ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))))
         then let sizes = read_i32_le data (add code_offset pos1) in
              let pos2 =
                add pos1 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                  (Stdlib.Int.succ 0))))
              in
              let nc =
                Z.to_nat
                  (Z.coq_land sizes
                    (Z.ones ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                      ((fun p->2*p) 1))))))
              in
              let nb =
                Z.to_nat
                  (Z.shiftr sizes ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
                    ((fun p->2*p) 1)))))
              in
              let (tbl, pos3) =
                read_operands data code_offset pos2 (add nc nb)
              in
              { ri_word_offset = word; ri_opcode = op; ri_operands =
              (sizes :: tbl) } :: (decode_raw_aux data code_offset
                                    code_length pos3 fuel')
         else if Z.eqb op ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
                   ((fun p->1+2*p) ((fun p->2*p) 1)))))
              then let nf = read_i32_le data (add code_offset pos1) in
                   let pos2 =
                     add pos1 (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                   in
                   let nv = read_i32_le data (add code_offset pos2) in
                   let pos3 =
                     add pos2 (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                   in
                   let (ofs_list, pos4) =
                     read_operands data code_offset pos3 (Z.to_nat nf)
                   in
                   { ri_word_offset = word; ri_opcode = op; ri_operands =
                   (nf :: (nv :: ofs_list)) } :: (decode_raw_aux data
                                                   code_offset code_length
                                                   pos4 fuel')
              else if Z.eqb op ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p)
                        ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
                        ((fun p->2*p) 1)))))))
                   then let tag = read_i32_le data (add code_offset pos1) in
                        let pos2 =
                          add pos1 (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                        in
                        let pos3 =
                          add pos2 (Stdlib.Int.succ (Stdlib.Int.succ
                            (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                        in
                        { ri_word_offset = word; ri_opcode = op;
                        ri_operands =
                        (tag :: []) } :: (decode_raw_aux data code_offset
                                           code_length pos3 fuel')
                   else (match operand_count op with
                         | Some n0 ->
                           let (ops, pos2) =
                             read_operands data code_offset pos1 n0
                           in
                           { ri_word_offset = word; ri_opcode = op;
                           ri_operands =
                           ops } :: (decode_raw_aux data code_offset
                                      code_length pos2 fuel')
                         | None -> []))
    fuel

(** val decode_raw : int list -> int -> int -> raw_instr list **)

let decode_raw data code_offset code_length =
  decode_raw_aux data code_offset code_length 0
    (add code_length (Stdlib.Int.succ 0))

(** val build_offset_map_aux : raw_instr list -> int -> (int * int) list **)

let rec build_offset_map_aux raws idx =
  match raws with
  | [] -> []
  | ri :: rest ->
    (ri.ri_word_offset,
      idx) :: (build_offset_map_aux rest (Stdlib.Int.succ idx))

(** val build_offset_map : raw_instr list -> (int * int) list **)

let build_offset_map raws =
  build_offset_map_aux raws 0

(** val lookup_offset0 : (int * int) list -> int -> int **)

let rec lookup_offset0 m w =
  match m with
  | [] -> 0
  | p :: rest ->
    let (k, v) = p in if (=) k w then v else lookup_offset0 rest w

(** val resolve_branch : (int * int) list -> int -> int -> int **)

let resolve_branch omap wpos rel =
  let target = Z.to_nat (Z.add wpos rel) in
  Z.of_nat (lookup_offset0 omap target)

(** val nat_of_z : int -> int **)

let nat_of_z =
  Z.to_nat

(** val znth : int -> int list -> int **)

let znth n0 l =
  match nth_error l n0 with
  | Some v -> v
  | None -> 0

(** val resolve_one : (int * int) list -> raw_instr -> instruction **)

let resolve_one omap ri =
  let op = ri.ri_opcode in
  let ops = ri.ri_operands in
  let w = ri.ri_word_offset in
  let br = fun n0 ->
    resolve_branch omap (Z.of_nat (add (add w (Stdlib.Int.succ 0)) n0))
      (znth n0 ops)
  in
  if Z.eqb op 0
  then ACC 0
  else if Z.eqb op 1
       then ACC (Stdlib.Int.succ 0)
       else if Z.eqb op ((fun p->2*p) 1)
            then ACC (Stdlib.Int.succ (Stdlib.Int.succ 0))
            else if Z.eqb op ((fun p->1+2*p) 1)
                 then ACC (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                        0)))
                 else if Z.eqb op ((fun p->2*p) ((fun p->2*p) 1))
                      then ACC (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0))))
                      else if Z.eqb op ((fun p->1+2*p) ((fun p->2*p) 1))
                           then ACC (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ (Stdlib.Int.succ
                                  (Stdlib.Int.succ 0)))))
                           else if Z.eqb op ((fun p->2*p) ((fun p->1+2*p) 1))
                                then ACC (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       (Stdlib.Int.succ (Stdlib.Int.succ
                                       0))))))
                                else if Z.eqb op ((fun p->1+2*p)
                                          ((fun p->1+2*p) 1))
                                     then ACC (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            (Stdlib.Int.succ (Stdlib.Int.succ
                                            0)))))))
                                     else if Z.eqb op ((fun p->2*p)
                                               ((fun p->2*p) ((fun p->2*p)
                                               1)))
                                          then ACC (nat_of_z (znth 0 ops))
                                          else if Z.eqb op ((fun p->1+2*p)
                                                    ((fun p->2*p)
                                                    ((fun p->2*p) 1)))
                                               then PUSH
                                               else if Z.eqb op ((fun p->2*p)
                                                         ((fun p->1+2*p)
                                                         ((fun p->2*p) 1)))
                                                    then PUSHACC 0
                                                    else if Z.eqb op
                                                              ((fun p->1+2*p)
                                                              ((fun p->1+2*p)
                                                              ((fun p->2*p)
                                                              1)))
                                                         then PUSHACC
                                                                (Stdlib.Int.succ
                                                                0)
                                                         else if Z.eqb op
                                                                   ((fun p->2*p)
                                                                   ((fun p->2*p)
                                                                   ((fun p->1+2*p)
                                                                   1)))
                                                              then PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                              else if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))
                                                                   then 
                                                                    PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                   else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))
                                                                    then 
                                                                    PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))
                                                                    then 
                                                                    PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHACC
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    POP
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    ASSIGN
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    ENVACC
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    ENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))
                                                                    then 
                                                                    ENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    ENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    ENVACC
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHENVACC
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHENVACC
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSHENVACC
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))
                                                                    then 
                                                                    PUSH_RETADDR
                                                                    (br 0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPLY
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPLY1
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPLY2
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPLY3
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPTERM
                                                                    ((nat_of_z
                                                                    (znth 0
                                                                    ops)),
                                                                    (nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPTERM1
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPTERM2
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    APPTERM3
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    RETURN
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    RESTART
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    GRAB
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    CLOSURE
                                                                    ((nat_of_z
                                                                    (znth 0
                                                                    ops)),
                                                                    (resolve_branch
                                                                    omap
                                                                    (Z.of_nat
                                                                    (add w
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    let nf =
                                                                    nat_of_z
                                                                    (znth 0
                                                                    ops)
                                                                    in
                                                                    let nv =
                                                                    nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)
                                                                    in
                                                                    let base =
                                                                    Z.of_nat
                                                                    (add w
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))
                                                                    in
                                                                    let resolve_list =
                                                                    let rec resolve_list = function
                                                                    | [] -> []
                                                                    | o :: rest ->
                                                                    (resolve_branch
                                                                    omap base
                                                                    o) :: 
                                                                    (resolve_list
                                                                    rest)
                                                                    in resolve_list
                                                                    in
                                                                    CLOSUREREC
                                                                    (nf, nv,
                                                                    (resolve_list
                                                                    (skipn
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    OFFSETCLOSURE
                                                                    ((~-)
                                                                    ((fun p->1+2*p)
                                                                    1))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    OFFSETCLOSURE
                                                                    0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    then 
                                                                    OFFSETCLOSURE
                                                                    ((fun p->1+2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    OFFSETCLOSURE
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHOFFSETCLOSURE
                                                                    ((~-)
                                                                    ((fun p->1+2*p)
                                                                    1))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHOFFSETCLOSURE
                                                                    0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHOFFSETCLOSURE
                                                                    ((fun p->1+2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHOFFSETCLOSURE
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    GETGLOBAL
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHGETGLOBAL
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    GETGLOBALFIELD
                                                                    ((nat_of_z
                                                                    (znth 0
                                                                    ops)),
                                                                    (nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHGETGLOBALFIELD
                                                                    ((nat_of_z
                                                                    (znth 0
                                                                    ops)),
                                                                    (nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    SETGLOBAL
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    ATOM 0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    ATOM
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHATOM 0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    PUSHATOM
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    MAKEBLOCK
                                                                    ((nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1)))))
                                                                    then 
                                                                    MAKEBLOCK1
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    MAKEBLOCK2
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    MAKEBLOCK3
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    MAKEFLOATBLOCK
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFIELD 0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFIELD
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFIELD
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFIELD
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFIELD
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETFLOATFIELD
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFIELD 0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFIELD
                                                                    (Stdlib.Int.succ
                                                                    0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFIELD
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFIELD
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFIELD
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETFLOATFIELD
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    VECTLENGTH
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETVECTITEM
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETVECTITEM
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    GETBYTESCHAR
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    SETBYTESCHAR
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    BRANCH
                                                                    (br 0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    BRANCHIF
                                                                    (br 0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    BRANCHIFNOT
                                                                    (br 0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    let sizes =
                                                                    znth 0 ops
                                                                    in
                                                                    let nc =
                                                                    Z.to_nat
                                                                    (Z.coq_land
                                                                    sizes
                                                                    (Z.ones
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    in
                                                                    let nb =
                                                                    Z.to_nat
                                                                    (Z.shiftr
                                                                    sizes
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))
                                                                    in
                                                                    let base =
                                                                    Z.of_nat
                                                                    (add w
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    in
                                                                    let resolve_n =
                                                                    let rec resolve_n start count =
                                                                      
                                                                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                                                                    (fun _ ->
                                                                    [])
                                                                    (fun count' ->
                                                                    (resolve_branch
                                                                    omap base
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    start)
                                                                    ops)) :: 
                                                                    (resolve_n
                                                                    (Stdlib.Int.succ
                                                                    start)
                                                                    count'))
                                                                    count
                                                                    in resolve_n
                                                                    in
                                                                    SWITCH
                                                                    (nc, nb,
                                                                    (resolve_n
                                                                    0 nc),
                                                                    (resolve_n
                                                                    nc nb))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    BOOLNOT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHTRAP
                                                                    (br 0)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    POPTRAP
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then RAISE
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    CHECK_SIGNALS
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((Stdlib.Int.succ
                                                                    0),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0)))),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    (Stdlib.Int.succ
                                                                    0))))),
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    C_CALL
                                                                    ((nat_of_z
                                                                    (znth 0
                                                                    ops)),
                                                                    (nat_of_z
                                                                    (znth
                                                                    (Stdlib.Int.succ
                                                                    0) ops)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    CONSTINT 0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    CONSTINT 1
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    CONSTINT
                                                                    ((fun p->2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    CONSTINT
                                                                    ((fun p->1+2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    CONSTINT
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHCONSTINT
                                                                    0
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHCONSTINT
                                                                    1
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHCONSTINT
                                                                    ((fun p->2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHCONSTINT
                                                                    ((fun p->1+2*p)
                                                                    1)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    PUSHCONSTINT
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    NEGINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    ADDINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    SUBINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    MULINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    DIVINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    MODINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    ANDINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then ORINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    XORINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    LSLINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    LSRINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    ASRINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then EQ
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then NEQ
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then LTINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then LEINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then GTINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then GEINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    1))))))
                                                                    then 
                                                                    OFFSETINT
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    OFFSETREF
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then ISINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    GETMETHOD
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BEQ
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BNEQ
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BLTINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BLEINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BGTINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BGEINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    ULTINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    UGEINT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BULTINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    BUGEINT
                                                                    ((znth 0
                                                                    ops),
                                                                    (br
                                                                    (Stdlib.Int.succ
                                                                    0)))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    GETPUBMET
                                                                    (znth 0
                                                                    ops)
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    GETDYNMET
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then STOP
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then EVENT
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then BREAK
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    RERAISE
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    RAISE_NOTRACE
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    GETSTRINGCHAR
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    PERFORM
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    RESUME
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    RESUMETERM
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else 
                                                                    if 
                                                                    Z.eqb op
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->1+2*p)
                                                                    ((fun p->2*p)
                                                                    ((fun p->2*p)
                                                                    1)))))))
                                                                    then 
                                                                    REPERFORMTERM
                                                                    (nat_of_z
                                                                    (znth 0
                                                                    ops))
                                                                    else STOP

(** val resolve_all : raw_instr list -> instruction list **)

let resolve_all raws =
  let omap = build_offset_map raws in map (resolve_one omap) raws

(** val decode_bytecode : int list -> int -> int -> instruction list **)

let decode_bytecode data code_offset code_length =
  resolve_all (decode_raw data code_offset code_length)

(** val load_code_section : int list -> int -> instruction list option **)

let load_code_section data data_len =
  let secs = parse_sections data data_len in
  (match find_section secs cODE_name with
   | Some s -> Some (decode_bytecode data s.sec_offset s.sec_length)
   | None -> None)

(** val decode_value_aux : int list -> int -> value * int list **)

let rec decode_value_aux data fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((Val_int 0), data))
    (fun fuel' ->
    match data with
    | [] -> ((Val_int 0), [])
    | z0 :: l ->
      ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
         (fun _ ->
         match l with
         | [] -> ((Val_int 0), [])
         | n0 :: rest -> ((Val_int n0), rest))
         (fun p ->
         (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
           (fun _ -> ((Val_int 0), []))
           (fun p0 ->
           (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
             (fun _ -> ((Val_int 0), []))
             (fun _ -> ((Val_int 0), []))
             (fun _ ->
             match l with
             | [] -> ((Val_int 0), [])
             | len :: rest ->
               let chars = firstn (Z.to_nat len) rest in
               let rest' = skipn (Z.to_nat len) rest in
               ((Val_block (string_tag, (map (fun x -> Val_int x) chars))),
               rest'))
             p0)
           (fun _ ->
           match l with
           | [] -> ((Val_int 0), [])
           | tag :: l0 ->
             (match l0 with
              | [] -> ((Val_int 0), [])
              | size :: rest ->
                let (fields, rest') =
                  let rec read_fields r n0 =
                    (fun fO fS n -> if n=0 then fO () else fS (n-1))
                      (fun _ -> ([], r))
                      (fun n' ->
                      let (v, r') = decode_value_aux r fuel' in
                      let (vs, r'') = read_fields r' n' in ((v :: vs), r''))
                      n0
                  in read_fields rest (Z.to_nat size)
                in
                ((Val_block ((Z.to_nat tag), fields)), rest')))
           p)
         (fun _ -> ((Val_int 0), []))
         z0))
    fuel

(** val decode_value : int list -> value **)

let decode_value data =
  fst
    (decode_value_aux data (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val decode_globals : int list list -> value list **)

let decode_globals encodings =
  map decode_value encodings

(** val dATA_name : int **)

let dATA_name =
  Z.coq_lor
    (Z.shiftl ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1)))))
    (Z.coq_lor
      (Z.shiftl ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1)))))
      (Z.coq_lor
        (Z.shiftl ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
          ((fun p->1+2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
        ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1))))))))

(** val pRIM_name : int **)

let pRIM_name =
  Z.coq_lor
    (Z.shiftl ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->1+2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->1+2*p) 1)))))
    (Z.coq_lor
      (Z.shiftl ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->1+2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1)))))
      (Z.coq_lor
        (Z.shiftl ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) 1))))
        ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
        ((fun p->2*p) ((fun p->2*p) 1))))))))

(** val list_z_eqb : int list -> int list -> bool **)

let rec list_z_eqb a b =
  match a with
  | [] -> (match b with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match b with
     | [] -> false
     | y :: ys -> (&&) (Z.eqb x y) (list_z_eqb xs ys))

(** val str_to_codes : char list -> int list **)

let rec str_to_codes = function
| [] -> []
| c::rest -> (Z.of_nat (nat_of_ascii c)) :: (str_to_codes rest)

(** val z_to_string_aux : int -> int -> int list -> int list **)

let rec z_to_string_aux n0 fuel acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun fuel' ->
    if Z.eqb n0 0
    then (match acc with
          | [] ->
            ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
              ((fun p->1+2*p) 1))))) :: []
          | _ :: _ -> acc)
    else z_to_string_aux
           (Z.div n0 ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1)))) fuel'
           ((Z.add
              (Z.modulo n0 ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p) 1))))
              ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
              ((fun p->1+2*p) 1)))))) :: acc))
    fuel

(** val z_to_string_codes : int -> int list **)

let z_to_string_codes n0 =
  if Z.ltb n0 0
  then ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
         ((fun p->2*p)
         1))))) :: (z_to_string_aux (Z.opp n0) (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                     (Stdlib.Int.succ (Stdlib.Int.succ
                     0)))))))))))))))))))))))))))))) [])
  else z_to_string_aux n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0)))))))))))))))))))))))))))))) []

(** val mk_zeros : int -> value list **)

let rec mk_zeros n0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n' -> (Val_int 0) :: (mk_zeros n'))
    n0

(** val handle_output_char : value list -> value option **)

let handle_output_char _ =
  Some (Val_int 0)

(** val handle_output_bytes : value list -> value option **)

let handle_output_bytes _ =
  Some (Val_int 0)

(** val handle_format_int : value list -> value option **)

let handle_format_int = function
| [] -> Some (Val_int 0)
| _ :: l ->
  (match l with
   | [] -> Some (Val_int 0)
   | v0 :: _ ->
     (match v0 with
      | Val_int n0 ->
        Some (Val_block (string_tag,
          (map (fun x -> Val_int x) (z_to_string_codes n0))))
      | _ -> Some (Val_int 0)))

(** val handle_open_descriptor : value list -> value option **)

let handle_open_descriptor = function
| [] ->
  Some (Val_block ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    ((Val_int 0) :: [])))
| v :: _ ->
  (match v with
   | Val_int fd ->
     Some (Val_block ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
       ((Val_int fd) :: [])))
   | _ ->
     Some (Val_block ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
       ((Val_int 0) :: []))))

(** val handle_obj_tag : value list -> value option **)

let handle_obj_tag = function
| [] -> Some (Val_int 0)
| v :: _ ->
  (match v with
   | Val_int _ ->
     Some (Val_int ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->1+2*p)
       ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) 1))))))))))
   | Val_block (t, _) -> Some (Val_int (Z.of_nat t))
   | _ -> Some (Val_int 0))

(** val handle_string_length : value list -> value option **)

let handle_string_length = function
| [] -> Some (Val_int 0)
| v :: _ ->
  (match v with
   | Val_block (_, cs) -> Some (Val_int (Z.of_nat (length cs)))
   | _ -> Some (Val_int 0))

(** val handle_create_bytes : value list -> value option **)

let handle_create_bytes = function
| [] -> Some (Val_int 0)
| v :: _ ->
  (match v with
   | Val_int n0 -> Some (Val_block (string_tag, (mk_zeros (Z.to_nat n0))))
   | _ -> Some (Val_int 0))

(** val handle_string_equal : value list -> value option **)

let handle_string_equal = function
| [] -> Some (Val_int 0)
| v :: l ->
  (match v with
   | Val_block (_, a) ->
     (match l with
      | [] -> Some (Val_int 0)
      | v0 :: _ ->
        (match v0 with
         | Val_block (_, b) ->
           let veqb =
             let rec veqb l1 l2 =
               match l1 with
               | [] -> (match l2 with
                        | [] -> true
                        | _ :: _ -> false)
               | v1 :: r1 ->
                 (match v1 with
                  | Val_int x ->
                    (match l2 with
                     | [] -> false
                     | v2 :: r2 ->
                       (match v2 with
                        | Val_int y -> (&&) (Z.eqb x y) (veqb r1 r2)
                        | _ -> false))
                  | _ -> false)
             in veqb
           in
           Some (Val_int (if veqb a b then 1 else 0))
         | _ -> Some (Val_int 0)))
   | _ -> Some (Val_int 0))

(** val handle_int_compare : value list -> value option **)

let handle_int_compare = function
| [] -> Some (Val_int 0)
| v :: l ->
  (match v with
   | Val_int a ->
     (match l with
      | [] -> Some (Val_int 0)
      | v0 :: _ ->
        (match v0 with
         | Val_int b ->
           Some (Val_int
             (if Z.ltb a b then (~-) 1 else if Z.ltb b a then 1 else 0))
         | _ -> Some (Val_int 0)))
   | _ -> Some (Val_int 0))

(** val handle_string_concat : value list -> value option **)

let handle_string_concat = function
| [] -> Some (Val_int 0)
| v :: l ->
  (match v with
   | Val_block (_, a) ->
     (match l with
      | [] -> Some (Val_int 0)
      | v0 :: _ ->
        (match v0 with
         | Val_block (_, b) -> Some (Val_block (string_tag, (app a b)))
         | _ -> Some (Val_int 0)))
   | _ -> Some (Val_int 0))

(** val handle_identity : value list -> value option **)

let handle_identity = function
| [] -> Some (Val_int 0)
| v :: _ -> Some v

(** val handle_string_get : value list -> value option **)

let handle_string_get = function
| [] -> Some (Val_int 0)
| v :: l ->
  (match v with
   | Val_block (_, cs) ->
     (match l with
      | [] -> Some (Val_int 0)
      | v0 :: _ ->
        (match v0 with
         | Val_int i ->
           (match nth_error cs (Z.to_nat i) with
            | Some v1 -> Some v1
            | None -> Some (Val_int 0))
         | _ -> Some (Val_int 0)))
   | _ -> Some (Val_int 0))

(** val make_ccall_handler :
    int list list -> int -> value list -> value option **)

let make_ccall_handler prims idx args =
  let name = match nth_error prims idx with
             | Some n0 -> n0
             | None -> [] in
  if list_z_eqb name
       (str_to_codes
         ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('h'::('a'::('r'::[]))))))))))))))))))))
  then handle_output_char args
  else if (||)
            (list_z_eqb name
              (str_to_codes
                ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('b'::('y'::('t'::('e'::('s'::[]))))))))))))))))))))))
            (list_z_eqb name
              (str_to_codes
                ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))
       then handle_output_bytes args
       else if list_z_eqb name
                 (str_to_codes
                   ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('f'::('l'::('u'::('s'::('h'::[]))))))))))))))
            then Some (Val_int 0)
            else if list_z_eqb name
                      (str_to_codes
                        ('c'::('a'::('m'::('l'::('_'::('f'::('o'::('r'::('m'::('a'::('t'::('_'::('i'::('n'::('t'::[]))))))))))))))))
                 then handle_format_int args
                 else if list_z_eqb name
                           (str_to_codes
                             ('c'::('a'::('m'::('l'::('_'::('r'::('e'::('g'::('i'::('s'::('t'::('e'::('r'::('_'::('n'::('a'::('m'::('e'::('d'::('_'::('v'::('a'::('l'::('u'::('e'::[]))))))))))))))))))))))))))
                      then Some (Val_int 0)
                      else if list_z_eqb name
                                (str_to_codes
                                  ('c'::('a'::('m'::('l'::('_'::('f'::('r'::('e'::('s'::('h'::('_'::('o'::('o'::('_'::('i'::('d'::[])))))))))))))))))
                           then Some (Val_int 0)
                           else if (||)
                                     (list_z_eqb name
                                       (str_to_codes
                                         ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('o'::('p'::('e'::('n'::('_'::('d'::('e'::('s'::('c'::('r'::('i'::('p'::('t'::('o'::('r'::('_'::('i'::('n'::[]))))))))))))))))))))))))))))
                                     (list_z_eqb name
                                       (str_to_codes
                                         ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('o'::('p'::('e'::('n'::('_'::('d'::('e'::('s'::('c'::('r'::('i'::('p'::('t'::('o'::('r'::('_'::('o'::('u'::('t'::[])))))))))))))))))))))))))))))
                                then handle_open_descriptor args
                                else if list_z_eqb name
                                          (str_to_codes
                                            ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('s'::('e'::('t'::('_'::('c'::('h'::('a'::('n'::('n'::('e'::('l'::('_'::('n'::('a'::('m'::('e'::[])))))))))))))))))))))))))
                                     then Some (Val_int 0)
                                     else if list_z_eqb name
                                               (str_to_codes
                                                 ('c'::('a'::('m'::('l'::('_'::('s'::('y'::('s'::('_'::('c'::('o'::('n'::('s'::('t'::('_'::('m'::('a'::('x'::('_'::('w'::('o'::('s'::('i'::('z'::('e'::[]))))))))))))))))))))))))))
                                          then Some (Val_int
                                                 (Z.sub
                                                   (Z.shiftl 1
                                                     ((fun p->1+2*p)
                                                     ((fun p->2*p)
                                                     ((fun p->2*p)
                                                     ((fun p->1+2*p)
                                                     ((fun p->1+2*p) 1))))))
                                                   1))
                                          else if list_z_eqb name
                                                    (str_to_codes
                                                      ('c'::('a'::('m'::('l'::('_'::('s'::('y'::('s'::('_'::('c'::('o'::('n'::('s'::('t'::('_'::('i'::('n'::('t'::('_'::('s'::('i'::('z'::('e'::[]))))))))))))))))))))))))
                                               then Some (Val_int
                                                      ((fun p->1+2*p)
                                                      ((fun p->1+2*p)
                                                      ((fun p->1+2*p)
                                                      ((fun p->1+2*p)
                                                      ((fun p->1+2*p) 1))))))
                                               else if list_z_eqb name
                                                         (str_to_codes
                                                           ('c'::('a'::('m'::('l'::('_'::('o'::('b'::('j'::('_'::('t'::('a'::('g'::[])))))))))))))
                                                    then handle_obj_tag args
                                                    else if (||)
                                                              (list_z_eqb
                                                                name
                                                                (str_to_codes
                                                                  ('c'::('a'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('l'::('e'::('n'::('g'::('t'::('h'::[]))))))))))))))))))))
                                                              (list_z_eqb
                                                                name
                                                                (str_to_codes
                                                                  ('c'::('a'::('m'::('l'::('_'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('l'::('e'::('n'::('g'::('t'::('h'::[])))))))))))))))))))))))
                                                         then handle_string_length
                                                                args
                                                         else if list_z_eqb
                                                                   name
                                                                   (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('c'::('r'::('e'::('a'::('t'::('e'::('_'::('b'::('y'::('t'::('e'::('s'::[]))))))))))))))))))
                                                              then handle_create_bytes
                                                                    args
                                                              else if 
                                                                    (||)
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('b'::('l'::('i'::('t'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))))))))
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('b'::('l'::('i'::('t'::('_'::('b'::('y'::('t'::('e'::('s'::[])))))))))))))))))
                                                                   then 
                                                                    Some
                                                                    (Val_int
                                                                    0)
                                                                   else 
                                                                    if 
                                                                    list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('e'::('q'::('u'::('a'::('l'::[]))))))))))))))))))
                                                                    then 
                                                                    handle_string_equal
                                                                    args
                                                                    else 
                                                                    if 
                                                                    (||)
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('i'::('n'::('t'::('_'::('c'::('o'::('m'::('p'::('a'::('r'::('e'::[]))))))))))))))))))
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('c'::('o'::('m'::('p'::('a'::('r'::('e'::[]))))))))))))))
                                                                    then 
                                                                    handle_int_compare
                                                                    args
                                                                    else 
                                                                    if 
                                                                    list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('c'::('o'::('n'::('c'::('a'::('t'::[])))))))))))))))))))
                                                                    then 
                                                                    handle_string_concat
                                                                    args
                                                                    else 
                                                                    if 
                                                                    (||)
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('o'::('f'::('_'::('b'::('y'::('t'::('e'::('s'::[]))))))))))))))))))))))
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('b'::('y'::('t'::('e'::('s'::('_'::('o'::('f'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))))))))))))
                                                                    then 
                                                                    handle_identity
                                                                    args
                                                                    else 
                                                                    if 
                                                                    (||)
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::('_'::('g'::('e'::('t'::[])))))))))))))))))
                                                                    (list_z_eqb
                                                                    name
                                                                    (str_to_codes
                                                                    ('c'::('a'::('m'::('l'::('_'::('b'::('y'::('t'::('e'::('s'::('_'::('g'::('e'::('t'::[]))))))))))))))))
                                                                    then 
                                                                    handle_string_get
                                                                    args
                                                                    else 
                                                                    Some
                                                                    (Val_int
                                                                    0)

(** val main : int **)

let main =
  match nth_error sys_argv (Stdlib.Int.succ 0) with
  | Some filename_codes ->
    let raw_bytes = read_file filename_codes in
    let data = byte_string_to_list raw_bytes in
    let data_len = Z.to_nat (byte_string_length raw_bytes) in
    (match load_code_section data data_len with
     | Some code ->
       let secs = parse_sections data data_len in
       let globals =
         match find_section secs dATA_name with
         | Some s ->
           let encodings =
             unmarshal_globals raw_bytes (Z.of_nat s.sec_offset)
               (Z.of_nat s.sec_length)
           in
           decode_globals encodings
         | None -> []
       in
       let prims =
         match find_section secs pRIM_name with
         | Some s ->
           load_primitives raw_bytes (Z.of_nat s.sec_offset)
             (Z.of_nat s.sec_length)
         | None -> []
       in
       let handler = make_ccall_handler prims in
       let init = initial_state globals in
       let fuel =
         Z.to_nat ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->1+2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
           ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
           ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
           ((fun p->1+2*p) ((fun p->2*p) 1))))))))))))))))))))))))))
       in
       (match run fuel code init handler with
        | Finished _ -> 0
        | _ -> 1)
     | None -> 1)
  | None -> 1

type event = int
  (* singleton inductive, whose constructor was Out_char *)

type termination =
| Term_normal of value
| Term_error of char list
| Term_timeout

type behavior = { trace : event list; result : termination }

type ident = char list

type binop =
| Op_add
| Op_sub
| Op_mul
| Op_div
| Op_mod
| Op_eq
| Op_neq
| Op_lt
| Op_le
| Op_gt
| Op_ge
| Op_and
| Op_or

type unop =
| Op_neg
| Op_not

type pattern =
| Pat_var of ident
| Pat_int of int
| Pat_bool of bool
| Pat_unit
| Pat_tuple of pattern list
| Pat_constr of ident * pattern option
| Pat_wild

type type_expr =
| Ty_int
| Ty_bool
| Ty_unit
| Ty_arrow of type_expr * type_expr
| Ty_tuple of type_expr list
| Ty_constr of ident * type_expr list

type expr =
| Exp_int of int
| Exp_bool of bool
| Exp_unit
| Exp_var of ident
| Exp_binop of binop * expr * expr
| Exp_unop of unop * expr
| Exp_if of expr * expr * expr
| Exp_let of ident * expr * expr
| Exp_letrec of ident * expr * expr
| Exp_fun of ident * expr
| Exp_app of expr * expr
| Exp_tuple of expr list
| Exp_constr of ident * expr option
| Exp_match of expr * (pattern * expr) list
| Exp_seq of expr * expr

type decl =
| Decl_let of ident * expr
| Decl_letrec of ident * expr
| Decl_type of ident * ident list * type_def
| Decl_expr of expr
and type_def =
| Td_variant of (ident * type_expr option) list
| Td_alias of type_expr

type program = decl list

(** val nat_to_string_aux : int -> int -> char list -> char list **)

let rec nat_to_string_aux fuel n0 acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun fuel' ->
    let digit =
      (ascii_of_nat
        (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
          (Nat.modulo n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0)))))))))))))::[]
    in
    let rest =
      Nat.div n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
    in
    if (=) rest 0
    then append digit acc
    else nat_to_string_aux fuel' rest (append digit acc))
    fuel

(** val nat_to_string : int -> char list **)

let nat_to_string n0 =
  if (=) n0 0
  then '0'::[]
  else nat_to_string_aux (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))))))) n0 []

(** val z_to_string : int -> char list **)

let z_to_string z0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> '0'::[])
    (fun p -> nat_to_string (Coq_Pos.to_nat p))
    (fun p ->
    append ('('::('-'::[]))
      (append (nat_to_string (Coq_Pos.to_nat p)) (')'::[])))
    z0

(** val intercalate : char list -> char list list -> char list **)

let rec intercalate sep = function
| [] -> []
| x :: rest ->
  (match rest with
   | [] -> x
   | _ :: _ -> append x (append sep (intercalate sep rest)))

(** val pp_binop : binop -> char list **)

let pp_binop = function
| Op_add -> ' '::('+'::(' '::[]))
| Op_sub -> ' '::('-'::(' '::[]))
| Op_mul -> ' '::('*'::(' '::[]))
| Op_div -> ' '::('/'::(' '::[]))
| Op_mod -> ' '::('m'::('o'::('d'::(' '::[]))))
| Op_eq -> ' '::('='::(' '::[]))
| Op_neq -> ' '::('<'::('>'::(' '::[])))
| Op_lt -> ' '::('<'::(' '::[]))
| Op_le -> ' '::('<'::('='::(' '::[])))
| Op_gt -> ' '::('>'::(' '::[]))
| Op_ge -> ' '::('>'::('='::(' '::[])))
| Op_and -> ' '::('&'::('&'::(' '::[])))
| Op_or -> ' '::('|'::('|'::(' '::[])))

(** val pp_pattern : pattern -> char list **)

let rec pp_pattern = function
| Pat_var x -> x
| Pat_int n0 -> z_to_string n0
| Pat_bool b ->
  if b
  then 't'::('r'::('u'::('e'::[])))
  else 'f'::('a'::('l'::('s'::('e'::[]))))
| Pat_unit -> '('::(')'::[])
| Pat_tuple ps ->
  append ('('::[])
    (append (intercalate (','::(' '::[])) (map pp_pattern ps)) (')'::[]))
| Pat_constr (c, o) ->
  (match o with
   | Some p0 ->
     append ('('::[])
       (append c (append (' '::[]) (append (pp_pattern p0) (')'::[]))))
   | None -> c)
| Pat_wild -> '_'::[]

(** val pp_type_expr : type_expr -> char list **)

let rec pp_type_expr = function
| Ty_int -> 'i'::('n'::('t'::[]))
| Ty_bool -> 'b'::('o'::('o'::('l'::[])))
| Ty_unit -> 'u'::('n'::('i'::('t'::[])))
| Ty_arrow (t1, t2) ->
  append ('('::[])
    (append (pp_type_expr t1)
      (append (' '::('-'::('>'::(' '::[]))))
        (append (pp_type_expr t2) (')'::[]))))
| Ty_tuple ts ->
  append ('('::[])
    (append (intercalate (' '::('*'::(' '::[]))) (map pp_type_expr ts))
      (')'::[]))
| Ty_constr (name, args) ->
  (match args with
   | [] -> name
   | t0 :: l ->
     (match l with
      | [] ->
        append ('('::[])
          (append (pp_type_expr t0)
            (append (' '::[]) (append name (')'::[]))))
      | _ :: _ ->
        append ('('::('('::[]))
          (append (intercalate (','::(' '::[])) (map pp_type_expr args))
            (append (')'::(' '::[])) (append name (')'::[]))))))

(** val pp_expr : expr -> char list **)

let rec pp_expr = function
| Exp_int n0 -> z_to_string n0
| Exp_bool b ->
  if b
  then 't'::('r'::('u'::('e'::[])))
  else 'f'::('a'::('l'::('s'::('e'::[]))))
| Exp_unit -> '('::(')'::[])
| Exp_var x -> x
| Exp_binop (op, e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (pp_binop op) (append (pp_expr e2) (')'::[]))))
| Exp_unop (u, e0) ->
  (match u with
   | Op_neg -> append ('('::('-'::(' '::[]))) (append (pp_expr e0) (')'::[]))
   | Op_not ->
     append ('('::('n'::('o'::('t'::(' '::[])))))
       (append (pp_expr e0) (')'::[])))
| Exp_if (e1, e2, e3) ->
  append ('('::('i'::('f'::(' '::[]))))
    (append (pp_expr e1)
      (append (' '::('t'::('h'::('e'::('n'::(' '::[]))))))
        (append (pp_expr e2)
          (append (' '::('e'::('l'::('s'::('e'::(' '::[]))))))
            (append (pp_expr e3) (')'::[]))))))
| Exp_let (x, e1, e2) ->
  append ('('::('l'::('e'::('t'::(' '::[])))))
    (append x
      (append (' '::('='::(' '::[])))
        (append (pp_expr e1)
          (append (' '::('i'::('n'::(' '::[]))))
            (append (pp_expr e2) (')'::[]))))))
| Exp_letrec (f, e1, e2) ->
  append ('('::('l'::('e'::('t'::(' '::('r'::('e'::('c'::(' '::[])))))))))
    (append f
      (append (' '::('='::(' '::[])))
        (append (pp_expr e1)
          (append (' '::('i'::('n'::(' '::[]))))
            (append (pp_expr e2) (')'::[]))))))
| Exp_fun (x, body) ->
  append ('('::('f'::('u'::('n'::(' '::[])))))
    (append x
      (append (' '::('-'::('>'::(' '::[]))))
        (append (pp_expr body) (')'::[]))))
| Exp_app (f, arg) ->
  append ('('::[])
    (append (pp_expr f) (append (' '::[]) (append (pp_expr arg) (')'::[]))))
| Exp_tuple es ->
  append ('('::[])
    (append (intercalate (','::(' '::[])) (map pp_expr es)) (')'::[]))
| Exp_constr (c, o) ->
  (match o with
   | Some e0 ->
     append ('('::[])
       (append c (append (' '::[]) (append (pp_expr e0) (')'::[]))))
   | None -> c)
| Exp_match (e0, cases) ->
  let pp_case = fun c ->
    let (p, body) = c in
    append ('|'::(' '::[]))
      (append (pp_pattern p)
        (append (' '::('-'::('>'::(' '::[])))) (pp_expr body)))
  in
  append ('('::('m'::('a'::('t'::('c'::('h'::(' '::[])))))))
    (append (pp_expr e0)
      (append (' '::('w'::('i'::('t'::('h'::(' '::[]))))))
        (append (intercalate (' '::[]) (map pp_case cases)) (')'::[]))))
| Exp_seq (e1, e2) ->
  append ('('::[])
    (append (pp_expr e1)
      (append (';'::(' '::[])) (append (pp_expr e2) (')'::[]))))

(** val pp_type_def : type_def -> char list **)

let pp_type_def = function
| Td_variant constrs ->
  intercalate (' '::('|'::(' '::[])))
    (map (fun cd ->
      let (name, y) = cd in
      (match y with
       | Some t ->
         append name (append (' '::('o'::('f'::(' '::[])))) (pp_type_expr t))
       | None -> name))
      constrs)
| Td_alias t -> pp_type_expr t

(** val pp_decl : decl -> char list **)

let pp_decl = function
| Decl_let (x, e) ->
  append ('l'::('e'::('t'::(' '::[]))))
    (append x (append (' '::('='::(' '::[]))) (pp_expr e)))
| Decl_letrec (f, e) ->
  append ('l'::('e'::('t'::(' '::('r'::('e'::('c'::(' '::[]))))))))
    (append f (append (' '::('='::(' '::[]))) (pp_expr e)))
| Decl_type (name, params, td) ->
  let params_str =
    match params with
    | [] -> []
    | p :: l ->
      (match l with
       | [] -> append ('\''::[]) (append p (' '::[]))
       | _ :: _ ->
         append ('('::[])
           (append
             (intercalate (','::(' '::[]))
               (map (fun p0 -> append ('\''::[]) p0) params))
             (')'::(' '::[]))))
  in
  append ('t'::('y'::('p'::('e'::(' '::[])))))
    (append params_str
      (append name (append (' '::('='::(' '::[]))) (pp_type_def td))))
| Decl_expr e -> pp_expr e

(** val pp_program : program -> char list **)

let pp_program prog =
  intercalate ('\n'::[])
    (map (fun d -> append (pp_decl d) (';'::(';'::[]))) prog)

type builtin =
| Bi_print_int
| Bi_print_string
| Bi_print_newline
| Bi_print_char
| Bi_compare
| Bi_fst
| Bi_snd

type svalue =
| SVal_int of int
| SVal_bool of bool
| SVal_unit
| SVal_tuple of svalue list
| SVal_constr of ident * svalue option
| SVal_closure of ident * expr * env0
| SVal_recclosure of ident * ident * expr * env0
| SVal_builtin of builtin
and env0 =
| Env_nil
| Env_cons of ident * svalue * env0

(** val env_lookup : env0 -> ident -> svalue option **)

let rec env_lookup e x =
  match e with
  | Env_nil -> None
  | Env_cons (y, v, rest) -> if eqb0 x y then Some v else env_lookup rest x

(** val env_extend : env0 -> ident -> svalue -> env0 **)

let env_extend e x v =
  Env_cons (x, v, e)

(** val env_append : env0 -> env0 -> env0 **)

let rec env_append e1 e2 =
  match e1 with
  | Env_nil -> e2
  | Env_cons (x, v, rest) -> Env_cons (x, v, (env_append rest e2))

(** val match_pattern : pattern -> svalue -> env0 option **)

let rec match_pattern p v =
  match p with
  | Pat_var x -> Some (Env_cons (x, v, Env_nil))
  | Pat_int n0 ->
    (match v with
     | SVal_int m -> if Z.eqb n0 m then Some Env_nil else None
     | _ -> None)
  | Pat_bool b ->
    (match v with
     | SVal_bool c -> if eqb b c then Some Env_nil else None
     | _ -> None)
  | Pat_unit -> (match v with
                 | SVal_unit -> Some Env_nil
                 | _ -> None)
  | Pat_tuple ps ->
    (match v with
     | SVal_tuple vs ->
       if (=) (length ps) (length vs)
       then let rec match_list ps0 vs0 =
              match ps0 with
              | [] -> (match vs0 with
                       | [] -> Some Env_nil
                       | _ :: _ -> None)
              | p1 :: pr ->
                (match vs0 with
                 | [] -> None
                 | v1 :: vr ->
                   (match match_pattern p1 v1 with
                    | Some e1 ->
                      (match match_list pr vr with
                       | Some e2 -> Some (env_append e1 e2)
                       | None -> None)
                    | None -> None))
            in match_list ps vs
       else None
     | _ -> None)
  | Pat_constr (c, o) ->
    (match o with
     | Some p' ->
       (match v with
        | SVal_constr (d, o0) ->
          (match o0 with
           | Some v' -> if eqb0 c d then match_pattern p' v' else None
           | None -> None)
        | _ -> None)
     | None ->
       (match v with
        | SVal_constr (d, o0) ->
          (match o0 with
           | Some _ -> None
           | None -> if eqb0 c d then Some Env_nil else None)
        | _ -> None))
  | Pat_wild -> Some Env_nil

(** val try_cases :
    (pattern * expr) list -> svalue -> (expr * env0) option **)

let rec try_cases cases v =
  match cases with
  | [] -> None
  | p0 :: rest ->
    let (p, body) = p0 in
    (match match_pattern p v with
     | Some bindings -> Some (body, bindings)
     | None -> try_cases rest v)

type eval_result =
| Eval_ok of svalue * event list
| Eval_err of char list * event list
| Eval_timeout of event list

(** val eval_binop : binop -> svalue -> svalue -> svalue option **)

let eval_binop op v1 v2 =
  match op with
  | Op_add ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_int (Z.add a b))
        | _ -> None)
     | _ -> None)
  | Op_sub ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_int (Z.sub a b))
        | _ -> None)
     | _ -> None)
  | Op_mul ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_int (Z.mul a b))
        | _ -> None)
     | _ -> None)
  | Op_div ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b ->
          if Z.eqb b 0 then None else Some (SVal_int (Z.quot a b))
        | _ -> None)
     | _ -> None)
  | Op_mod ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b ->
          if Z.eqb b 0 then None else Some (SVal_int (Z.rem a b))
        | _ -> None)
     | _ -> None)
  | Op_eq ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (Z.eqb a b))
        | _ -> None)
     | _ -> None)
  | Op_neq ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (negb (Z.eqb a b)))
        | _ -> None)
     | _ -> None)
  | Op_lt ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (Z.ltb a b))
        | _ -> None)
     | _ -> None)
  | Op_le ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (Z.leb a b))
        | _ -> None)
     | _ -> None)
  | Op_gt ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (Z.gtb a b))
        | _ -> None)
     | _ -> None)
  | Op_ge ->
    (match v1 with
     | SVal_int a ->
       (match v2 with
        | SVal_int b -> Some (SVal_bool (Z.geb a b))
        | _ -> None)
     | _ -> None)
  | Op_and ->
    (match v1 with
     | SVal_bool a ->
       (match v2 with
        | SVal_bool b -> Some (SVal_bool ((&&) a b))
        | _ -> None)
     | _ -> None)
  | Op_or ->
    (match v1 with
     | SVal_bool a ->
       (match v2 with
        | SVal_bool b -> Some (SVal_bool ((||) a b))
        | _ -> None)
     | _ -> None)

(** val eval_unop : unop -> svalue -> svalue option **)

let eval_unop op v =
  match op with
  | Op_neg ->
    (match v with
     | SVal_int n0 -> Some (SVal_int (Z.opp n0))
     | _ -> None)
  | Op_not ->
    (match v with
     | SVal_bool b -> Some (SVal_bool (negb b))
     | _ -> None)

(** val nat_to_events_aux : int -> int -> event list -> event list **)

let rec nat_to_events_aux fuel n0 acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun fuel' ->
    let digit =
      Z.of_nat
        (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
          (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))
          (Nat.modulo n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
            (Stdlib.Int.succ 0))))))))))))
    in
    let rest =
      Nat.div n0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))
    in
    if (=) rest 0
    then digit :: acc
    else nat_to_events_aux fuel' rest (digit :: acc))
    fuel

(** val z_to_events : int -> event list **)

let z_to_events z0 =
  (fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
    (fun _ -> ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
    ((fun p->1+2*p) 1))))) :: [])
    (fun p ->
    nat_to_events_aux (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))))))))) (Coq_Pos.to_nat p) [])
    (fun p -> ((fun p->1+2*p) ((fun p->2*p) ((fun p->1+2*p) ((fun p->1+2*p)
    ((fun p->2*p)
    1))))) :: (nat_to_events_aux (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                0)))))))))))))))))))) (Coq_Pos.to_nat p) []))
    z0

(** val apply_builtin :
    builtin -> svalue -> event list -> (svalue * event list) option **)

let apply_builtin b arg out =
  match b with
  | Bi_print_int ->
    (match arg with
     | SVal_int n0 -> Some (SVal_unit, (app (rev (z_to_events n0)) out))
     | _ -> None)
  | Bi_print_newline ->
    (match arg with
     | SVal_unit ->
       Some (SVal_unit, (((fun p->2*p) ((fun p->1+2*p) ((fun p->2*p)
         1))) :: out))
     | _ -> None)
  | Bi_print_char ->
    (match arg with
     | SVal_int c -> Some (SVal_unit, (c :: out))
     | _ -> None)
  | Bi_fst ->
    (match arg with
     | SVal_tuple l -> (match l with
                        | [] -> None
                        | a :: _ -> Some (a, out))
     | _ -> None)
  | Bi_snd ->
    (match arg with
     | SVal_tuple l ->
       (match l with
        | [] -> None
        | _ :: l0 -> (match l0 with
                      | [] -> None
                      | b0 :: _ -> Some (b0, out)))
     | _ -> None)
  | _ -> None

(** val stdlib_env : env0 **)

let stdlib_env =
  Env_cons
    (('p'::('r'::('i'::('n'::('t'::('_'::('i'::('n'::('t'::[]))))))))),
    (SVal_builtin Bi_print_int), (Env_cons
    (('p'::('r'::('i'::('n'::('t'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[])))))))))))),
    (SVal_builtin Bi_print_string), (Env_cons
    (('p'::('r'::('i'::('n'::('t'::('_'::('n'::('e'::('w'::('l'::('i'::('n'::('e'::[]))))))))))))),
    (SVal_builtin Bi_print_newline), (Env_cons
    (('p'::('r'::('i'::('n'::('t'::('_'::('c'::('h'::('a'::('r'::[])))))))))),
    (SVal_builtin Bi_print_char), (Env_cons
    (('c'::('o'::('m'::('p'::('a'::('r'::('e'::[]))))))), (SVal_builtin
    Bi_compare), (Env_cons (('f'::('s'::('t'::[]))), (SVal_builtin Bi_fst),
    (Env_cons (('s'::('n'::('d'::[]))), (SVal_builtin Bi_snd),
    Env_nil)))))))))))))

(** val eval : int -> expr -> env0 -> event list -> eval_result **)

let rec eval fuel e env1 out =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Eval_timeout out)
    (fun fuel' ->
    match e with
    | Exp_int n0 -> Eval_ok ((SVal_int n0), out)
    | Exp_bool b -> Eval_ok ((SVal_bool b), out)
    | Exp_unit -> Eval_ok (SVal_unit, out)
    | Exp_var x ->
      (match env_lookup env1 x with
       | Some v -> Eval_ok (v, out)
       | None ->
         Eval_err
           (('u'::('n'::('b'::('o'::('u'::('n'::('d'::(' '::('v'::('a'::('r'::('i'::('a'::('b'::('l'::('e'::[])))))))))))))))),
           out))
    | Exp_binop (op, e1, e2) ->
      (match eval fuel' e1 env1 out with
       | Eval_ok (v1, out1) ->
         (match eval fuel' e2 env1 out1 with
          | Eval_ok (v2, out2) ->
            (match eval_binop op v1 v2 with
             | Some v -> Eval_ok (v, out2)
             | None ->
               Eval_err
                 (('b'::('i'::('n'::('o'::('p'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::[])))))))))))))))),
                 out2))
          | x -> x)
       | x -> x)
    | Exp_unop (op, e1) ->
      (match eval fuel' e1 env1 out with
       | Eval_ok (v1, out1) ->
         (match eval_unop op v1 with
          | Some v -> Eval_ok (v, out1)
          | None ->
            Eval_err
              (('u'::('n'::('o'::('p'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::[]))))))))))))))),
              out1))
       | x -> x)
    | Exp_if (cond, then_e, else_e) ->
      (match eval fuel' cond env1 out with
       | Eval_ok (s, out1) ->
         (match s with
          | SVal_bool b ->
            if b
            then eval fuel' then_e env1 out1
            else eval fuel' else_e env1 out1
          | _ ->
            Eval_err
              (('i'::('f'::(':'::(' '::('n'::('o'::('n'::('-'::('b'::('o'::('o'::('l'::(' '::('c'::('o'::('n'::('d'::('i'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))),
              out1))
       | x -> x)
    | Exp_let (x, e1, e2) ->
      (match eval fuel' e1 env1 out with
       | Eval_ok (v1, out1) -> eval fuel' e2 (env_extend env1 x v1) out1
       | x0 -> x0)
    | Exp_letrec (f, e1, e2) ->
      (match e1 with
       | Exp_fun (param, body) ->
         let clos = SVal_recclosure (f, param, body, env1) in
         eval fuel' e2 (env_extend env1 f clos) out
       | _ ->
         (match eval fuel' e1 env1 out with
          | Eval_ok (v1, out1) -> eval fuel' e2 (env_extend env1 f v1) out1
          | x -> x))
    | Exp_fun (x, body) -> Eval_ok ((SVal_closure (x, body, env1)), out)
    | Exp_app (func, arg) ->
      (match eval fuel' func env1 out with
       | Eval_ok (fv, out1) ->
         (match eval fuel' arg env1 out1 with
          | Eval_ok (av, out2) ->
            (match fv with
             | SVal_closure (param, body, cenv) ->
               eval fuel' body (env_extend cenv param av) out2
             | SVal_recclosure (name, param, body, cenv) ->
               let cenv' = env_extend cenv name fv in
               eval fuel' body (env_extend cenv' param av) out2
             | SVal_builtin b ->
               (match apply_builtin b av out2 with
                | Some p -> let (rv, out3) = p in Eval_ok (rv, out3)
                | None ->
                  Eval_err
                    (('b'::('u'::('i'::('l'::('t'::('i'::('n'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::[])))))))))))))))))),
                    out2))
             | _ ->
               Eval_err
                 (('a'::('p'::('p'::('l'::('i'::('c'::('a'::('t'::('i'::('o'::('n'::(' '::('o'::('f'::(' '::('n'::('o'::('n'::('-'::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[]))))))))))))))))))))))))))),
                 out2))
          | x -> x)
       | x -> x)
    | Exp_tuple es ->
      let rec eval_list fuel0 es0 acc out0 =
        match es0 with
        | [] -> Eval_ok ((SVal_tuple (rev acc)), out0)
        | e1 :: rest ->
          (match eval fuel0 e1 env1 out0 with
           | Eval_ok (v, out1) -> eval_list fuel0 rest (v :: acc) out1
           | x -> x)
      in eval_list fuel' es [] out
    | Exp_constr (c, o) ->
      (match o with
       | Some e1 ->
         (match eval fuel' e1 env1 out with
          | Eval_ok (v, out1) -> Eval_ok ((SVal_constr (c, (Some v))), out1)
          | x -> x)
       | None -> Eval_ok ((SVal_constr (c, None)), out))
    | Exp_match (scrut, cases) ->
      (match eval fuel' scrut env1 out with
       | Eval_ok (sv, out1) ->
         (match try_cases cases sv with
          | Some p ->
            let (body, bindings) = p in
            eval fuel' body (env_append bindings env1) out1
          | None ->
            Eval_err
              (('m'::('a'::('t'::('c'::('h'::(' '::('f'::('a'::('i'::('l'::('u'::('r'::('e'::[]))))))))))))),
              out1))
       | x -> x)
    | Exp_seq (e1, e2) ->
      (match eval fuel' e1 env1 out with
       | Eval_ok (_, out1) -> eval fuel' e2 env1 out1
       | x -> x))
    fuel

(** val eval_program : int -> program -> env0 -> event list -> eval_result **)

let rec eval_program fuel prog env1 out =
  match prog with
  | [] -> Eval_ok (SVal_unit, out)
  | d :: rest ->
    (match d with
     | Decl_let (x, e) ->
       (match eval fuel e env1 out with
        | Eval_ok (v, out') ->
          eval_program fuel rest (env_extend env1 x v) out'
        | x0 -> x0)
     | Decl_letrec (f, e) ->
       (match e with
        | Exp_fun (param, body) ->
          let clos = SVal_recclosure (f, param, body, env1) in
          eval_program fuel rest (env_extend env1 f clos) out
        | _ ->
          (match eval fuel e env1 out with
           | Eval_ok (v, out') ->
             eval_program fuel rest (env_extend env1 f v) out'
           | x -> x))
     | Decl_type (_, _, _) -> eval_program fuel rest env1 out
     | Decl_expr e ->
       (match eval fuel e env1 out with
        | Eval_ok (_, out') -> eval_program fuel rest env1 out'
        | x -> x))

(** val interpret : int -> program -> behavior **)

let interpret fuel prog =
  match eval_program fuel prog stdlib_env [] with
  | Eval_ok (_, out) ->
    { trace = (rev out); result = (Term_normal (Val_int 0)) }
  | Eval_err (msg, out) -> { trace = (rev out); result = (Term_error msg) }
  | Eval_timeout out -> { trace = (rev out); result = Term_timeout }

type var_loc =
| Loc_stack of int
| Loc_env of int
| Loc_self

type comp_env = (ident * var_loc) list

(** val comp_lookup : comp_env -> ident -> var_loc option **)

let rec comp_lookup ce x =
  match ce with
  | [] -> None
  | p :: rest ->
    let (y, loc) = p in if eqb0 x y then Some loc else comp_lookup rest x

(** val shift0 : comp_env -> int -> comp_env **)

let rec shift0 ce n0 =
  match ce with
  | [] -> []
  | entry :: rest ->
    let (x, v) = entry in
    (match v with
     | Loc_stack pos -> (x, (Loc_stack (add pos n0))) :: (shift0 rest n0)
     | _ -> entry :: (shift0 rest n0))

(** val is_builtin : ident -> int option **)

let is_builtin x =
  if eqb0 x ('p'::('r'::('i'::('n'::('t'::('_'::('i'::('n'::('t'::[])))))))))
  then Some 0
  else if eqb0 x
            ('p'::('r'::('i'::('n'::('t'::('_'::('n'::('e'::('w'::('l'::('i'::('n'::('e'::[])))))))))))))
       then Some (Stdlib.Int.succ 0)
       else if eqb0 x
                 ('p'::('r'::('i'::('n'::('t'::('_'::('s'::('t'::('r'::('i'::('n'::('g'::[]))))))))))))
            then Some (Stdlib.Int.succ (Stdlib.Int.succ 0))
            else None

(** val is_inline_builtin : ident -> instruction list option **)

let is_inline_builtin x =
  if eqb0 x ('f'::('s'::('t'::[])))
  then Some ((GETFIELD 0) :: [])
  else if eqb0 x ('s'::('n'::('d'::[])))
       then Some ((GETFIELD (Stdlib.Int.succ 0)) :: [])
       else None

(** val mem_ident : ident -> ident list -> bool **)

let rec mem_ident x = function
| [] -> false
| y :: r -> if eqb0 x y then true else mem_ident x r

(** val remove_ident : ident -> ident list -> ident list **)

let rec remove_ident x = function
| [] -> []
| y :: r -> if eqb0 x y then remove_ident x r else y :: (remove_ident x r)

(** val dedup_acc : ident list -> ident list -> ident list **)

let rec dedup_acc seen = function
| [] -> []
| x :: r ->
  if mem_ident x seen
  then dedup_acc seen r
  else x :: (dedup_acc (x :: seen) r)

(** val dedup : ident list -> ident list **)

let dedup l =
  dedup_acc [] l

(** val pat_vars : pattern -> ident list **)

let rec pat_vars = function
| Pat_var x -> x :: []
| Pat_tuple ps ->
  let rec pv_list = function
  | [] -> []
  | p1 :: r -> app (pat_vars p1) (pv_list r)
  in pv_list ps
| Pat_constr (_, o) -> (match o with
                        | Some p' -> pat_vars p'
                        | None -> [])
| _ -> []

(** val remove_many : ident list -> ident list -> ident list **)

let remove_many xs l =
  fold_left (fun acc x -> remove_ident x acc) xs l

(** val free_vars : expr -> ident list **)

let rec free_vars = function
| Exp_var x -> x :: []
| Exp_binop (_, e1, e2) -> app (free_vars e1) (free_vars e2)
| Exp_unop (_, e1) -> free_vars e1
| Exp_if (c, t, e0) -> app (free_vars c) (app (free_vars t) (free_vars e0))
| Exp_let (x, e1, e2) -> app (free_vars e1) (remove_ident x (free_vars e2))
| Exp_letrec (f, e1, e2) ->
  app (remove_ident f (free_vars e1)) (remove_ident f (free_vars e2))
| Exp_fun (x, body) -> remove_ident x (free_vars body)
| Exp_app (e1, e2) -> app (free_vars e1) (free_vars e2)
| Exp_tuple es ->
  let rec fv_list = function
  | [] -> []
  | e1 :: r -> app (free_vars e1) (fv_list r)
  in fv_list es
| Exp_constr (_, o) -> (match o with
                        | Some e1 -> free_vars e1
                        | None -> [])
| Exp_match (scrut, cases) ->
  app (free_vars scrut)
    (let rec fv_cases = function
     | [] -> []
     | y :: r ->
       let (p, b) = y in
       app (remove_many (pat_vars p) (free_vars b)) (fv_cases r)
     in fv_cases cases)
| Exp_seq (e1, e2) -> app (free_vars e1) (free_vars e2)
| _ -> []

(** val closure_vars : ident list -> expr -> comp_env -> ident list **)

let closure_vars params body ce =
  let fvs = remove_many params (free_vars body) in
  let fvs' = dedup fvs in
  filter (fun x ->
    match comp_lookup ce x with
    | Some _ -> true
    | None -> false) fvs'

(** val make_fv_env : int -> ident list -> comp_env **)

let rec make_fv_env i = function
| [] -> []
| x :: rest ->
  (x, (Loc_env
    (add (Stdlib.Int.succ (Stdlib.Int.succ 0)) i))) :: (make_fv_env
                                                         (Stdlib.Int.succ i)
                                                         rest)

(** val make_body_env : ident -> ident list -> comp_env **)

let make_body_env param fvs =
  (param, (Loc_stack 0)) :: (make_fv_env 0 fvs)

(** val make_rec_body_env : ident -> ident -> ident list -> comp_env **)

let make_rec_body_env param fname fvs =
  (param, (Loc_stack 0)) :: ((fname, Loc_self) :: (make_fv_env 0 fvs))

(** val compile_push_fvs :
    ident list -> comp_env -> int -> instruction list **)

let rec compile_push_fvs fvs ce pushed =
  match fvs with
  | [] -> []
  | x :: rest ->
    (match rest with
     | [] ->
       let ce' = shift0 ce pushed in
       (match comp_lookup ce' x with
        | Some v ->
          (match v with
           | Loc_stack n0 -> (ACC n0) :: []
           | Loc_env n0 -> (ENVACC n0) :: []
           | Loc_self -> (OFFSETCLOSURE 0) :: [])
        | None -> (CONSTINT 0) :: [])
     | _ :: _ ->
       let ce' = shift0 ce pushed in
       let load =
         match comp_lookup ce' x with
         | Some v ->
           (match v with
            | Loc_stack n0 -> (ACC n0) :: []
            | Loc_env n0 -> (ENVACC n0) :: []
            | Loc_self -> (OFFSETCLOSURE 0) :: [])
         | None -> (CONSTINT 0) :: []
       in
       app load
         (app (PUSH :: [])
           (compile_push_fvs rest ce (Stdlib.Int.succ pushed))))

(** val compile_expr : int -> expr -> comp_env -> int -> instruction list **)

let rec compile_expr fuel e ce base =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> STOP :: [])
    (fun fuel' ->
    match e with
    | Exp_int n0 -> (CONSTINT n0) :: []
    | Exp_bool b -> if b then (CONSTINT 1) :: [] else (CONSTINT 0) :: []
    | Exp_unit -> (CONSTINT 0) :: []
    | Exp_var x ->
      (match comp_lookup ce x with
       | Some v ->
         (match v with
          | Loc_stack n0 -> (ACC n0) :: []
          | Loc_env n0 -> (ENVACC n0) :: []
          | Loc_self -> (OFFSETCLOSURE 0) :: [])
       | None -> (CONSTINT 0) :: [])
    | Exp_binop (op, e1, e2) ->
      let c2 = compile_expr fuel' e2 ce base in
      let c1 =
        compile_expr fuel' e1 (shift0 ce (Stdlib.Int.succ 0))
          (add (add base (length c2)) (Stdlib.Int.succ 0))
      in
      let op_instr =
        match op with
        | Op_add -> ADDINT
        | Op_sub -> SUBINT
        | Op_mul -> MULINT
        | Op_div -> DIVINT
        | Op_mod -> MODINT
        | Op_eq -> EQ
        | Op_neq -> NEQ
        | Op_lt -> LTINT
        | Op_le -> LEINT
        | Op_gt -> GTINT
        | Op_ge -> GEINT
        | Op_and -> ANDINT
        | Op_or -> ORINT
      in
      app c2 (app (PUSH :: []) (app c1 (op_instr :: [])))
    | Exp_unop (u, e1) ->
      (match u with
       | Op_neg -> app (compile_expr fuel' e1 ce base) (NEGINT :: [])
       | Op_not -> app (compile_expr fuel' e1 ce base) (BOOLNOT :: []))
    | Exp_if (cond, then_e, else_e) ->
      let cc = compile_expr fuel' cond ce base in
      let cc_len = length cc in
      let ct =
        compile_expr fuel' then_e ce
          (add (add base cc_len) (Stdlib.Int.succ 0))
      in
      let ct_len = length ct in
      let else_base =
        add (add (add (add base cc_len) (Stdlib.Int.succ 0)) ct_len)
          (Stdlib.Int.succ 0)
      in
      let ce_code = compile_expr fuel' else_e ce else_base in
      let ce_len = length ce_code in
      app cc
        (app ((BRANCHIFNOT (Z.of_nat else_base)) :: [])
          (app ct
            (app ((BRANCH (Z.of_nat (add else_base ce_len))) :: []) ce_code)))
    | Exp_let (x, e1, e2) ->
      let c1 = compile_expr fuel' e1 ce base in
      let c1_len = length c1 in
      let c2 =
        compile_expr fuel' e2 ((x, (Loc_stack
          0)) :: (shift0 ce (Stdlib.Int.succ 0)))
          (add (add base c1_len) (Stdlib.Int.succ 0))
      in
      app c1 (app (PUSH :: []) (app c2 ((POP (Stdlib.Int.succ 0)) :: [])))
    | Exp_letrec (f, e1, e2) ->
      (match e1 with
       | Exp_fun (param, body) ->
         let fvs = closure_vars (f :: (param :: [])) body ce in
         let nvars = length fvs in
         let body_env = make_rec_body_env param f fvs in
         let body_code =
           compile_expr fuel' body body_env (add base (Stdlib.Int.succ 0))
         in
         let body_instrs = app body_code ((RETURN (Stdlib.Int.succ 0)) :: [])
         in
         let body_len = length body_instrs in
         let push_code = compile_push_fvs (rev fvs) ce 0 in
         let body_start = Z.of_nat (add base (Stdlib.Int.succ 0)) in
         let branch_target =
           Z.of_nat (add (add base (Stdlib.Int.succ 0)) body_len)
         in
         let cr_pos =
           add (add (add base (Stdlib.Int.succ 0)) body_len)
             (length push_code)
         in
         let c2 =
           compile_expr fuel' e2 ((f, (Loc_stack
             0)) :: (shift0 ce (Stdlib.Int.succ 0)))
             (add cr_pos (Stdlib.Int.succ 0))
         in
         app ((BRANCH branch_target) :: [])
           (app body_instrs
             (app push_code
               (app ((CLOSUREREC ((Stdlib.Int.succ 0), nvars,
                 (body_start :: []))) :: [])
                 (app c2 ((POP (Stdlib.Int.succ 0)) :: [])))))
       | _ ->
         let c1 = compile_expr fuel' e1 ce base in
         let c1_len = length c1 in
         let c2 =
           compile_expr fuel' e2 ((f, (Loc_stack
             0)) :: (shift0 ce (Stdlib.Int.succ 0)))
             (add (add base c1_len) (Stdlib.Int.succ 0))
         in
         app c1 (app (PUSH :: []) (app c2 ((POP (Stdlib.Int.succ 0)) :: []))))
    | Exp_fun (param, body) ->
      let fvs = closure_vars (param :: []) body ce in
      let nvars = length fvs in
      let body_env = make_body_env param fvs in
      let body_code =
        compile_expr fuel' body body_env (add base (Stdlib.Int.succ 0))
      in
      let body_instrs = app body_code ((RETURN (Stdlib.Int.succ 0)) :: []) in
      let body_len = length body_instrs in
      let push_code = compile_push_fvs (rev fvs) ce 0 in
      let body_start = Z.of_nat (add base (Stdlib.Int.succ 0)) in
      let branch_target =
        Z.of_nat (add (add base (Stdlib.Int.succ 0)) body_len)
      in
      app ((BRANCH branch_target) :: [])
        (app body_instrs
          (app push_code ((CLOSURE (nvars, body_start)) :: [])))
    | Exp_app (func, arg) ->
      (match func with
       | Exp_var fname ->
         (match is_builtin fname with
          | Some prim_idx ->
            app (compile_expr fuel' arg ce base) ((C_CALL ((Stdlib.Int.succ
              0), prim_idx)) :: [])
          | None ->
            (match is_inline_builtin fname with
             | Some instrs -> app (compile_expr fuel' arg ce base) instrs
             | None ->
               let ca = compile_expr fuel' arg ce base in
               let ca_len = length ca in
               let cf =
                 compile_expr fuel' func (shift0 ce (Stdlib.Int.succ 0))
                   (add (add base ca_len) (Stdlib.Int.succ 0))
               in
               app ca (app (PUSH :: []) (app cf (APPLY1 :: [])))))
       | _ ->
         let ca = compile_expr fuel' arg ce base in
         let ca_len = length ca in
         let cf =
           compile_expr fuel' func (shift0 ce (Stdlib.Int.succ 0))
             (add (add base ca_len) (Stdlib.Int.succ 0))
         in
         app ca (app (PUSH :: []) (app cf (APPLY1 :: []))))
    | Exp_tuple es ->
      (match es with
       | [] -> (ATOM 0) :: []
       | e1 :: l ->
         (match l with
          | [] -> app (compile_expr fuel' e1 ce base) ((MAKEBLOCK1 0) :: [])
          | e2 :: l0 ->
            (match l0 with
             | [] ->
               let c2 = compile_expr fuel' e2 ce base in
               let c1 =
                 compile_expr fuel' e1 (shift0 ce (Stdlib.Int.succ 0))
                   (add (add base (length c2)) (Stdlib.Int.succ 0))
               in
               app c2 (app (PUSH :: []) (app c1 ((MAKEBLOCK2 0) :: [])))
             | e3 :: l1 ->
               (match l1 with
                | [] ->
                  let c3 = compile_expr fuel' e3 ce base in
                  let c3_len = length c3 in
                  let c2 =
                    compile_expr fuel' e2 (shift0 ce (Stdlib.Int.succ 0))
                      (add (add base c3_len) (Stdlib.Int.succ 0))
                  in
                  let c2_len = length c2 in
                  let c1 =
                    compile_expr fuel' e1
                      (shift0 ce (Stdlib.Int.succ (Stdlib.Int.succ 0)))
                      (add
                        (add (add (add base c3_len) (Stdlib.Int.succ 0))
                          c2_len)
                        (Stdlib.Int.succ 0))
                  in
                  app c3
                    (app (PUSH :: [])
                      (app c2
                        (app (PUSH :: []) (app c1 ((MAKEBLOCK3 0) :: [])))))
                | _ :: _ -> (CONSTINT 0) :: []))))
    | Exp_constr (_, o) ->
      (match o with
       | Some e1 -> app (compile_expr fuel' e1 ce base) ((MAKEBLOCK1 0) :: [])
       | None -> (CONSTINT 0) :: [])
    | Exp_match (scrut, cases) ->
      let cs = compile_expr fuel' scrut ce base in
      let cs_len = length cs in
      let scrut_ce = shift0 ce (Stdlib.Int.succ 0) in
      let cases_base = add (add base cs_len) (Stdlib.Int.succ 0) in
      let cases_code =
        let rec compile_cases cl b =
          match cl with
          | [] -> []
          | p :: rest ->
            let (pat, body) = p in
            let body_ce =
              match pat with
              | Pat_var x -> (x, (Loc_stack 0)) :: scrut_ce
              | _ -> scrut_ce
            in
            let irrefutable =
              match pat with
              | Pat_var _ -> true
              | Pat_unit -> true
              | Pat_wild -> true
              | _ -> false
            in
            if irrefutable
            then compile_expr fuel' body body_ce b
            else (match rest with
                  | [] -> compile_expr fuel' body body_ce b
                  | _ :: _ ->
                    let test =
                      match pat with
                      | Pat_var _ -> []
                      | Pat_int n0 ->
                        (ACC 0) :: (PUSH :: ((CONSTINT n0) :: (EQ :: [])))
                      | Pat_bool b0 ->
                        if b0
                        then (ACC 0) :: (PUSH :: ((CONSTINT 1) :: (EQ :: [])))
                        else (ACC 0) :: (PUSH :: ((CONSTINT 0) :: (EQ :: [])))
                      | _ -> []
                    in
                    let tl = length test in
                    let bs = add (add b tl) (Stdlib.Int.succ 0) in
                    let bc = compile_expr fuel' body body_ce bs in
                    let bl = length bc in
                    let ns = add (add bs bl) (Stdlib.Int.succ 0) in
                    let rc = compile_cases rest ns in
                    let rl = length rc in
                    let ep = add ns rl in
                    app test
                      (app ((BRANCHIFNOT (Z.of_nat ns)) :: [])
                        (app bc (app ((BRANCH (Z.of_nat ep)) :: []) rc))))
        in compile_cases cases cases_base
      in
      app cs
        (app (PUSH :: []) (app cases_code ((POP (Stdlib.Int.succ 0)) :: [])))
    | Exp_seq (e1, e2) ->
      let c1 = compile_expr fuel' e1 ce base in
      let c2 = compile_expr fuel' e2 ce (add base (length c1)) in app c1 c2)
    fuel

(** val compile_decls :
    int -> decl list -> comp_env -> int -> instruction list **)

let rec compile_decls fuel decls ce base =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> STOP :: [])
    (fun fuel' ->
    match decls with
    | [] -> STOP :: []
    | d :: rest ->
      (match d with
       | Decl_let (x, e) ->
         let c = compile_expr fuel' e ce base in
         let c_len = length c in
         app c
           (app (PUSH :: [])
             (compile_decls fuel' rest ((x, (Loc_stack
               0)) :: (shift0 ce (Stdlib.Int.succ 0)))
               (add (add base c_len) (Stdlib.Int.succ 0))))
       | Decl_letrec (f, e) ->
         (match e with
          | Exp_fun (param, body) ->
            let fvs = closure_vars (f :: (param :: [])) body ce in
            let nvars = length fvs in
            let body_env = make_rec_body_env param f fvs in
            let body_code =
              compile_expr fuel' body body_env (add base (Stdlib.Int.succ 0))
            in
            let body_instrs =
              app body_code ((RETURN (Stdlib.Int.succ 0)) :: [])
            in
            let body_len = length body_instrs in
            let push_code = compile_push_fvs (rev fvs) ce 0 in
            let body_start = Z.of_nat (add base (Stdlib.Int.succ 0)) in
            let branch_target =
              Z.of_nat (add (add base (Stdlib.Int.succ 0)) body_len)
            in
            let cr_pos =
              add (add (add base (Stdlib.Int.succ 0)) body_len)
                (length push_code)
            in
            let rest_code =
              compile_decls fuel' rest ((f, (Loc_stack
                0)) :: (shift0 ce (Stdlib.Int.succ 0)))
                (add cr_pos (Stdlib.Int.succ 0))
            in
            app ((BRANCH branch_target) :: [])
              (app body_instrs
                (app push_code
                  (app ((CLOSUREREC ((Stdlib.Int.succ 0), nvars,
                    (body_start :: []))) :: []) rest_code)))
          | _ -> compile_decls fuel' ((Decl_let (f, e)) :: rest) ce base)
       | Decl_type (_, _, _) -> compile_decls fuel' rest ce base
       | Decl_expr e ->
         let c = compile_expr fuel' e ce base in
         app c (compile_decls fuel' rest ce (add base (length c)))))
    fuel

(** val compile_program : program -> instruction list **)

let compile_program prog =
  compile_decls (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    prog [] 0
