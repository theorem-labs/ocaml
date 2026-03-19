
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
    iter_op add x (Stdlib.Int.succ 0)
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

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

type value =
| Val_int of int
| Val_block of int * value list

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
| Val_block (_, _) -> false

(** val field : value -> int -> value option **)

let field v n0 =
  match v with
  | Val_int _ -> None
  | Val_block (_, fields) -> nth_error fields n0

(** val block_size : value -> int option **)

let block_size = function
| Val_int _ -> None
| Val_block (_, fields) -> Some (length fields)

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

(** val set_field : value -> int -> value -> value option **)

let set_field v n0 x =
  match v with
  | Val_int _ -> None
  | Val_block (t, fields) ->
    (match set_nth fields n0 x with
     | Some fields' -> Some (Val_block (t, fields'))
     | None -> None)

(** val value_eqb : value -> value -> bool **)

let rec value_eqb v1 v2 =
  match v1 with
  | Val_int n1 ->
    (match v2 with
     | Val_int n2 -> Z.eqb n1 n2
     | Val_block (_, _) -> false)
  | Val_block (t1, fs1) ->
    (match v2 with
     | Val_int _ -> false
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
          in list_eqb fs1 fs2))

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

type state = { pc : int; accu : value; stack : value list; env : value;
               extra_args : int; global : value list;
               trap_stack : trap_frame list }

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
    s.extra_args; global = s.global; trap_stack = s.trap_stack }

(** val initial_state : value list -> state **)

let initial_state global_data =
  { pc = 0; accu = val_unit; stack = []; env = val_unit; extra_args = 0;
    global = global_data; trap_stack = [] }

(** val get_code_ptr : value -> int option **)

let get_code_ptr = function
| Val_int _ -> None
| Val_block (t, fields) ->
  if (=) t closure_tag
  then (match fields with
        | [] -> None
        | v0 :: _ ->
          (match v0 with
           | Val_int pc0 -> Some pc0
           | Val_block (_, _) -> None))
  else None

(** val step : instruction list -> state -> step_result **)

let step code s =
  match nth_error code (Z.to_nat s.pc) with
  | Some instr ->
    let pc' = Z.add s.pc 1 in
    (match instr with
     | ACC n0 ->
       (match nth_error s.stack n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('A'::('C'::('C'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))
     | PUSH ->
       Step { pc = pc'; accu = s.accu; stack = (s.accu :: s.stack); env =
         s.env; extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
     | PUSHACC n0 ->
       let new_stack = s.accu :: s.stack in
       (match nth_error new_stack n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = new_stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('A'::('C'::('C'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))
     | POP n0 ->
       Step { pc = pc'; accu = s.accu; stack = (skipn n0 s.stack); env =
         s.env; extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
     | ASSIGN n0 ->
       (match set_nth s.stack n0 s.accu with
        | Some new_stack ->
          Step { pc = pc'; accu = val_unit; stack = new_stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('A'::('S'::('S'::('I'::('G'::('N'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))
     | ENVACC n0 ->
       (match field s.env n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('E'::('N'::('V'::('A'::('C'::('C'::(':'::(' '::('e'::('n'::('v'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))
     | PUSHENVACC n0 ->
       let new_stack = s.accu :: s.stack in
       (match field s.env n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = new_stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('E'::('N'::('V'::('A'::('C'::('C'::(':'::(' '::('e'::('n'::('v'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))))
     | PUSH_RETADDR ret_addr ->
       let frame = (Val_int ret_addr) :: (s.env :: ((Val_int
         (Z.of_nat s.extra_args)) :: s.stack))
       in
       Step { pc = pc'; accu = s.accu; stack = frame; env = s.env;
       extra_args = s.extra_args; global = s.global; trap_stack =
       s.trap_stack }
     | APPLY n0 ->
       (match get_code_ptr s.accu with
        | Some target_pc ->
          Step { pc = target_pc; accu = s.accu; stack = s.stack; env =
            s.accu; extra_args = (Nat.sub n0 (Stdlib.Int.succ 0)); global =
            s.global; trap_stack = s.trap_stack }
        | None ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))
     | APPLY1 ->
       (match s.stack with
        | [] ->
          Error
            ('A'::('P'::('P'::('L'::('Y'::('1'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))
        | arg1 :: rest ->
          (match get_code_ptr s.accu with
           | Some target_pc ->
             let new_stack = arg1 :: ((Val_int pc') :: (s.env :: ((Val_int
               (Z.of_nat s.extra_args)) :: rest)))
             in
             Step { pc = target_pc; accu = s.accu; stack = new_stack; env =
             s.accu; extra_args = 0; global = s.global; trap_stack =
             s.trap_stack }
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
             (match get_code_ptr s.accu with
              | Some target_pc ->
                let new_stack = arg1 :: (arg2 :: ((Val_int
                  pc') :: (s.env :: ((Val_int
                  (Z.of_nat s.extra_args)) :: rest))))
                in
                Step { pc = target_pc; accu = s.accu; stack = new_stack;
                env = s.accu; extra_args = (Stdlib.Int.succ 0); global =
                s.global; trap_stack = s.trap_stack }
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
                (match get_code_ptr s.accu with
                 | Some target_pc ->
                   let new_stack = arg1 :: (arg2 :: (arg3 :: ((Val_int
                     pc') :: (s.env :: ((Val_int
                     (Z.of_nat s.extra_args)) :: rest)))))
                   in
                   Step { pc = target_pc; accu = s.accu; stack = new_stack;
                   env = s.accu; extra_args = (Stdlib.Int.succ
                   (Stdlib.Int.succ 0)); global = s.global; trap_stack =
                   s.trap_stack }
                 | None ->
                   Error
                     ('A'::('P'::('P'::('L'::('Y'::('3'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))))
     | APPTERM (nargs, slotsize) ->
       let args = firstn nargs s.stack in
       let base = skipn slotsize s.stack in
       (match get_code_ptr s.accu with
        | Some target_pc ->
          Step { pc = target_pc; accu = s.accu; stack = (app args base);
            env = s.accu; extra_args =
            (Nat.add s.extra_args (Nat.sub nargs (Stdlib.Int.succ 0)));
            global = s.global; trap_stack = s.trap_stack }
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
          (match get_code_ptr s.accu with
           | Some target_pc ->
             Step { pc = target_pc; accu = s.accu; stack = (arg1 :: base);
               env = s.accu; extra_args = s.extra_args; global = s.global;
               trap_stack = s.trap_stack }
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
             (match get_code_ptr s.accu with
              | Some target_pc ->
                Step { pc = target_pc; accu = s.accu; stack =
                  (arg1 :: (arg2 :: base)); env = s.accu; extra_args =
                  (Nat.add s.extra_args (Stdlib.Int.succ 0)); global =
                  s.global; trap_stack = s.trap_stack }
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
                (match get_code_ptr s.accu with
                 | Some target_pc ->
                   Step { pc = target_pc; accu = s.accu; stack =
                     (arg1 :: (arg2 :: (arg3 :: base))); env = s.accu;
                     extra_args =
                     (Nat.add s.extra_args (Stdlib.Int.succ (Stdlib.Int.succ
                       0)));
                     global = s.global; trap_stack = s.trap_stack }
                 | None ->
                   Error
                     ('A'::('P'::('P'::('T'::('E'::('R'::('M'::('3'::(':'::(' '::('a'::('c'::('c'::('u'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))))))))))
     | RETURN stacksize ->
       let stk = skipn stacksize s.stack in
       if Nat.ltb 0 s.extra_args
       then (match get_code_ptr s.accu with
             | Some target_pc ->
               Step { pc = target_pc; accu = s.accu; stack = stk; env =
                 s.accu; extra_args =
                 (Nat.sub s.extra_args (Stdlib.Int.succ 0)); global =
                 s.global; trap_stack = s.trap_stack }
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
                           Step { pc = ret_pc; accu = s.accu; stack = rest;
                             env = saved_env; extra_args =
                             (Z.to_nat saved_ea); global = s.global;
                             trap_stack = s.trap_stack }
                         | Val_block (_, _) ->
                           Error
                             ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))))
                | Val_block (_, _) ->
                  Error
                    ('R'::('E'::('T'::('U'::('R'::('N'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))))
     | RESTART ->
       (match s.env with
        | Val_int _ ->
          Error
            ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('e'::('n'::('v'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('b'::('l'::('o'::('c'::('k'::[])))))))))))))))))))))))))))
        | Val_block (t, fields) ->
          if (=) t closure_tag
          then let num_args =
                 Nat.sub (length fields) (Stdlib.Int.succ (Stdlib.Int.succ
                   (Stdlib.Int.succ 0)))
               in
               let args =
                 skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                   0))) fields
               in
               let new_stack = app args s.stack in
               (match nth_error fields (Stdlib.Int.succ (Stdlib.Int.succ 0)) with
                | Some saved_env ->
                  Step { pc = pc'; accu = s.accu; stack = new_stack; env =
                    saved_env; extra_args = (Nat.add s.extra_args num_args);
                    global = s.global; trap_stack = s.trap_stack }
                | None ->
                  Error
                    ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[])))))))))))))))))))))))))))
          else Error
                 ('R'::('E'::('S'::('T'::('A'::('R'::('T'::(':'::(' '::('e'::('n'::('v'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('c'::('l'::('o'::('s'::('u'::('r'::('e'::[]))))))))))))))))))))))))))))))
     | GRAB required ->
       if (<=) required s.extra_args
       then Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
              extra_args = (Nat.sub s.extra_args required); global =
              s.global; trap_stack = s.trap_stack }
       else let num_args = Stdlib.Int.succ s.extra_args in
            let saved_args = firstn num_args s.stack in
            let rest_stack = skipn num_args s.stack in
            let closinfo = Val_int 0 in
            let closure = Val_block (closure_tag, ((Val_int
              (Z.sub s.pc 1)) :: (closinfo :: (s.env :: saved_args))))
            in
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
                           Step { pc = ret_pc; accu = closure; stack = rest;
                             env = saved_env; extra_args =
                             (Z.to_nat saved_ea); global = s.global;
                             trap_stack = s.trap_stack }
                         | Val_block (_, _) ->
                           Error
                             ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[])))))))))))))))))))))))))))))))
                | Val_block (_, _) ->
                  Error
                    ('G'::('R'::('A'::('B'::(':'::(' '::('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))))))))))
     | CLOSURE (nvars, code_ofs) ->
       let stk = if Nat.ltb 0 nvars then s.accu :: s.stack else s.stack in
       let vars = firstn nvars stk in
       let rest = skipn nvars stk in
       let closinfo = Val_int 0 in
       let closure = Val_block (closure_tag, ((Val_int
         code_ofs) :: (closinfo :: vars)))
       in
       Step { pc = pc'; accu = closure; stack = rest; env = s.env;
       extra_args = s.extra_args; global = s.global; trap_stack =
       s.trap_stack }
     | CLOSUREREC (nfuncs, nvars, code_offsets) ->
       if (=) nfuncs (Stdlib.Int.succ 0)
       then let stk = if Nat.ltb 0 nvars then s.accu :: s.stack else s.stack
            in
            let vars = firstn nvars stk in
            let rest = skipn nvars stk in
            (match code_offsets with
             | [] ->
               Error
                 ('C'::('L'::('O'::('S'::('U'::('R'::('E'::('R'::('E'::('C'::(':'::(' '::('n'::('o'::(' '::('c'::('o'::('d'::('e'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::('s'::[])))))))))))))))))))))))))))
             | ofs :: _ ->
               let closinfo = Val_int 0 in
               let closure = Val_block (closure_tag, ((Val_int
                 ofs) :: (closinfo :: vars)))
               in
               Step { pc = pc'; accu = closure; stack = (closure :: rest);
               env = s.env; extra_args = s.extra_args; global = s.global;
               trap_stack = s.trap_stack })
       else Error
              ('C'::('L'::('O'::('S'::('U'::('R'::('E'::('R'::('E'::('C'::(':'::(' '::('m'::('u'::('t'::('u'::('a'::('l'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('o'::('n'::(' '::('('::('n'::('f'::('u'::('n'::('c'::('s'::('>'::('1'::(')'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))
     | OFFSETCLOSURE ofs ->
       if Z.eqb ofs 0
       then Step { pc = pc'; accu = s.env; stack = s.stack; env = s.env;
              extra_args = s.extra_args; global = s.global; trap_stack =
              s.trap_stack }
       else Error
              ('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('n'::('o'::('n'::('-'::('z'::('e'::('r'::('o'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))
     | PUSHOFFSETCLOSURE ofs ->
       let new_stack = s.accu :: s.stack in
       if Z.eqb ofs 0
       then Step { pc = pc'; accu = s.env; stack = new_stack; env = s.env;
              extra_args = s.extra_args; global = s.global; trap_stack =
              s.trap_stack }
       else Error
              ('P'::('U'::('S'::('H'::('O'::('F'::('F'::('S'::('E'::('T'::('C'::('L'::('O'::('S'::('U'::('R'::('E'::(':'::(' '::('n'::('o'::('n'::('-'::('z'::('e'::('r'::('o'::(' '::('o'::('f'::('f'::('s'::('e'::('t'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))
     | GETGLOBAL n0 ->
       (match nth_error s.global n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))
     | PUSHGETGLOBAL n0 ->
       let new_stack = s.accu :: s.stack in
       (match nth_error s.global n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = new_stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
        | None ->
          Error
            ('P'::('U'::('S'::('H'::('G'::('E'::('T'::('G'::('L'::('O'::('B'::('A'::('L'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))))
     | GETGLOBALFIELD (n0, p) ->
       (match nth_error s.global n0 with
        | Some glob ->
          (match field glob p with
           | Some v ->
             Step { pc = pc'; accu = v; stack = s.stack; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }
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
          (match field glob p with
           | Some v ->
             Step { pc = pc'; accu = v; stack = new_stack; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }
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
       Step { pc = pc'; accu = val_unit; stack = s.stack; env = s.env;
       extra_args = s.extra_args; global = new_global; trap_stack =
       s.trap_stack }
     | ATOM t ->
       Step { pc = pc'; accu = (Val_block (t, [])); stack = s.stack; env =
         s.env; extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
     | PUSHATOM t ->
       let new_stack = s.accu :: s.stack in
       Step { pc = pc'; accu = (Val_block (t, [])); stack = new_stack; env =
       s.env; extra_args = s.extra_args; global = s.global; trap_stack =
       s.trap_stack }
     | MAKEBLOCK (t, size) ->
       let fields =
         s.accu :: (firstn (Nat.sub size (Stdlib.Int.succ 0)) s.stack)
       in
       let new_stack = skipn (Nat.sub size (Stdlib.Int.succ 0)) s.stack in
       Step { pc = pc'; accu = (Val_block (t, fields)); stack = new_stack;
       env = s.env; extra_args = s.extra_args; global = s.global;
       trap_stack = s.trap_stack }
     | MAKEBLOCK1 t ->
       Step { pc = pc'; accu = (Val_block (t, (s.accu :: []))); stack =
         s.stack; env = s.env; extra_args = s.extra_args; global = s.global;
         trap_stack = s.trap_stack }
     | MAKEBLOCK2 t ->
       (match s.stack with
        | [] ->
          Error
            ('M'::('A'::('K'::('E'::('B'::('L'::('O'::('C'::('K'::('2'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))
        | v1 :: rest ->
          Step { pc = pc'; accu = (Val_block (t, (s.accu :: (v1 :: []))));
            stack = rest; env = s.env; extra_args = s.extra_args; global =
            s.global; trap_stack = s.trap_stack })
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
             Step { pc = pc'; accu = (Val_block (t,
               (s.accu :: (v1 :: (v2 :: []))))); stack = rest; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }))
     | MAKEFLOATBLOCK _ ->
       Error
         ('M'::('A'::('K'::('E'::('F'::('L'::('O'::('A'::('T'::('B'::('L'::('O'::('C'::('K'::(':'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))
     | GETFIELD n0 ->
       (match field s.accu n0 with
        | Some v ->
          Step { pc = pc'; accu = v; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack }
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
          (match set_field s.accu n0 newval with
           | Some _ ->
             Step { pc = pc'; accu = val_unit; stack = rest; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }
           | None ->
             Error
               ('S'::('E'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('a'::('c'::('c'::('e'::('s'::('s'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))))))))))))))
     | SETFLOATFIELD _ ->
       Error
         ('S'::('E'::('T'::('F'::('L'::('O'::('A'::('T'::('F'::('I'::('E'::('L'::('D'::(':'::(' '::('n'::('o'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))
     | VECTLENGTH ->
       (match block_size s.accu with
        | Some n0 ->
          Step { pc = pc'; accu = (Val_int (Z.of_nat n0)); stack = s.stack;
            env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = s.trap_stack }
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
             (match field s.accu (Z.to_nat idx) with
              | Some v0 ->
                Step { pc = pc'; accu = v0; stack = rest; env = s.env;
                  extra_args = s.extra_args; global = s.global; trap_stack =
                  s.trap_stack }
              | None ->
                Error
                  ('G'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('b'::('o'::('u'::('n'::('d'::('s'::[])))))))))))))))))))))))))))))))))
           | Val_block (_, _) ->
             Error
               ('G'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('b'::('a'::('d'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))))))
     | SETVECTITEM ->
       (match s.stack with
        | [] ->
          Error
            ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))
        | v :: l ->
          (match v with
           | Val_int _ ->
             (match l with
              | [] ->
                Error
                  ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))
              | _ :: rest ->
                Step { pc = pc'; accu = val_unit; stack = rest; env = s.env;
                  extra_args = s.extra_args; global = s.global; trap_stack =
                  s.trap_stack })
           | Val_block (_, _) ->
             Error
               ('S'::('E'::('T'::('V'::('E'::('C'::('T'::('I'::('T'::('E'::('M'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))
     | GETBYTESCHAR ->
       Error
         ('G'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))
     | SETBYTESCHAR ->
       Error
         ('S'::('E'::('T'::('B'::('Y'::('T'::('E'::('S'::('C'::('H'::('A'::('R'::(':'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[])))))))))))))))))))))))))))))))
     | GETSTRINGCHAR ->
       Error
         ('G'::('E'::('T'::('S'::('T'::('R'::('I'::('N'::('G'::('C'::('H'::('A'::('R'::(':'::(' '::('n'::('o'::('t'::(' '::('y'::('e'::('t'::(' '::('s'::('u'::('p'::('p'::('o'::('r'::('t'::('e'::('d'::[]))))))))))))))))))))))))))))))))
     | BRANCH target ->
       Step { pc = target; accu = s.accu; stack = s.stack; env = s.env;
         extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
     | BRANCHIF target ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step { pc = pc'; accu = s.accu; stack = s.stack; env =
             s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = target; accu = s.accu; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = target; accu = s.accu; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             z0)
        | Val_block (_, _) ->
          Step { pc = target; accu = s.accu; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack })
     | BRANCHIFNOT target ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step { pc = target; accu = s.accu; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = pc'; accu = s.accu; stack = s.stack; env =
             s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = pc'; accu = s.accu; stack = s.stack; env =
             s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             z0)
        | Val_block (_, _) ->
          Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack })
     | SWITCH (_, _, const_targets, block_targets) ->
       (match s.accu with
        | Val_int n0 ->
          (match nth_error const_targets (Z.to_nat n0) with
           | Some target ->
             Step { pc = target; accu = s.accu; stack = s.stack; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }
           | None ->
             Error
               ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('c'::('o'::('n'::('s'::('t'::('a'::('n'::('t'::(' '::('i'::('n'::('d'::('e'::('x'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('r'::('a'::('n'::('g'::('e'::[]))))))))))))))))))))))))))))))))))))
        | Val_block (t, _) ->
          (match nth_error block_targets t with
           | Some target ->
             Step { pc = target; accu = s.accu; stack = s.stack; env = s.env;
               extra_args = s.extra_args; global = s.global; trap_stack =
               s.trap_stack }
           | None ->
             Error
               ('S'::('W'::('I'::('T'::('C'::('H'::(':'::(' '::('b'::('l'::('o'::('c'::('k'::(' '::('t'::('a'::('g'::(' '::('o'::('u'::('t'::(' '::('o'::('f'::(' '::('r'::('a'::('n'::('g'::('e'::[]))))))))))))))))))))))))))))))))
     | BOOLNOT ->
       (match s.accu with
        | Val_int z0 ->
          ((fun f0 fp fn z -> if z=0 then f0 () else if z>0 then fp z else fn (-z))
             (fun _ -> Step { pc = pc'; accu = val_true; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = pc'; accu = val_false; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             (fun _ -> Step { pc = pc'; accu = val_false; stack = s.stack;
             env = s.env; extra_args = s.extra_args; global = s.global;
             trap_stack = s.trap_stack })
             z0)
        | Val_block (_, _) ->
          Step { pc = pc'; accu = val_false; stack = s.stack; env = s.env;
            extra_args = s.extra_args; global = s.global; trap_stack =
            s.trap_stack })
     | PUSHTRAP handler_pc ->
       let trap_frame0 = (Val_int handler_pc) :: ((Val_int
         0) :: (s.env :: ((Val_int (Z.of_nat s.extra_args)) :: s.stack)))
       in
       let tf = { trap_pc = handler_pc; trap_sp_offset =
         (length trap_frame0); trap_env = s.env; trap_extra_args =
         s.extra_args }
       in
       Step { pc = pc'; accu = s.accu; stack = trap_frame0; env = s.env;
       extra_args = s.extra_args; global = s.global; trap_stack =
       (tf :: s.trap_stack) }
     | POPTRAP ->
       (match s.trap_stack with
        | [] ->
          Error
            ('P'::('O'::('P'::('T'::('R'::('A'::('P'::(':'::(' '::('n'::('o'::(' '::('t'::('r'::('a'::('p'::(' '::('f'::('r'::('a'::('m'::('e'::[]))))))))))))))))))))))
        | _ :: rest ->
          Step { pc = pc'; accu = s.accu; stack =
            (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
              (Stdlib.Int.succ 0)))) s.stack);
            env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = rest })
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
             Step { pc = tf.trap_pc; accu = s.accu; stack =
               (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0)))) restored);
               env = tf.trap_env; extra_args = tf.trap_extra_args; global =
               s.global; trap_stack = rest }
           | _ :: l ->
             (match l with
              | [] ->
                Step { pc = tf.trap_pc; accu = s.accu; stack =
                  (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ 0)))) restored);
                  env = tf.trap_env; extra_args = tf.trap_extra_args;
                  global = s.global; trap_stack = rest }
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step { pc = tf.trap_pc; accu = s.accu; stack =
                     (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                     env = tf.trap_env; extra_args = tf.trap_extra_args;
                     global = s.global; trap_stack = rest }
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step { pc = tf.trap_pc; accu = s.accu; stack =
                        (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                        env = tf.trap_env; extra_args = tf.trap_extra_args;
                        global = s.global; trap_stack = rest }
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           real_stack; env = saved_env; extra_args =
                           (Z.to_nat saved_ea); global = s.global;
                           trap_stack = rest }
                       | Val_block (_, _) ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                           env = tf.trap_env; extra_args =
                           tf.trap_extra_args; global = s.global;
                           trap_stack = rest }))))))
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
             Step { pc = tf.trap_pc; accu = s.accu; stack =
               (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0)))) restored);
               env = tf.trap_env; extra_args = tf.trap_extra_args; global =
               s.global; trap_stack = rest }
           | _ :: l ->
             (match l with
              | [] ->
                Step { pc = tf.trap_pc; accu = s.accu; stack =
                  (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ 0)))) restored);
                  env = tf.trap_env; extra_args = tf.trap_extra_args;
                  global = s.global; trap_stack = rest }
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step { pc = tf.trap_pc; accu = s.accu; stack =
                     (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                     env = tf.trap_env; extra_args = tf.trap_extra_args;
                     global = s.global; trap_stack = rest }
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step { pc = tf.trap_pc; accu = s.accu; stack =
                        (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                        env = tf.trap_env; extra_args = tf.trap_extra_args;
                        global = s.global; trap_stack = rest }
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           real_stack; env = saved_env; extra_args =
                           (Z.to_nat saved_ea); global = s.global;
                           trap_stack = rest }
                       | Val_block (_, _) ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                           env = tf.trap_env; extra_args =
                           tf.trap_extra_args; global = s.global;
                           trap_stack = rest }))))))
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
             Step { pc = tf.trap_pc; accu = s.accu; stack =
               (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                 (Stdlib.Int.succ 0)))) restored);
               env = tf.trap_env; extra_args = tf.trap_extra_args; global =
               s.global; trap_stack = rest }
           | _ :: l ->
             (match l with
              | [] ->
                Step { pc = tf.trap_pc; accu = s.accu; stack =
                  (skipn (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
                    (Stdlib.Int.succ 0)))) restored);
                  env = tf.trap_env; extra_args = tf.trap_extra_args;
                  global = s.global; trap_stack = rest }
              | _ :: l0 ->
                (match l0 with
                 | [] ->
                   Step { pc = tf.trap_pc; accu = s.accu; stack =
                     (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                       (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                     env = tf.trap_env; extra_args = tf.trap_extra_args;
                     global = s.global; trap_stack = rest }
                 | saved_env :: l1 ->
                   (match l1 with
                    | [] ->
                      Step { pc = tf.trap_pc; accu = s.accu; stack =
                        (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                          (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                        env = tf.trap_env; extra_args = tf.trap_extra_args;
                        global = s.global; trap_stack = rest }
                    | v1 :: real_stack ->
                      (match v1 with
                       | Val_int saved_ea ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           real_stack; env = saved_env; extra_args =
                           (Z.to_nat saved_ea); global = s.global;
                           trap_stack = rest }
                       | Val_block (_, _) ->
                         Step { pc = tf.trap_pc; accu = s.accu; stack =
                           (skipn (Stdlib.Int.succ (Stdlib.Int.succ
                             (Stdlib.Int.succ (Stdlib.Int.succ 0)))) restored);
                           env = tf.trap_env; extra_args =
                           tf.trap_extra_args; global = s.global;
                           trap_stack = rest }))))))
     | C_CALL (nargs, prim_idx) ->
       let args =
         s.accu :: (firstn (Nat.sub nargs (Stdlib.Int.succ 0)) s.stack)
       in
       let new_stack = skipn (Nat.sub nargs (Stdlib.Int.succ 0)) s.stack in
       let cont = { pc = pc'; accu = val_unit; stack = new_stack; env =
         s.env; extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
       in
       CCall_request (prim_idx, args, cont)
     | CONSTINT n0 ->
       Step { pc = pc'; accu = (Val_int n0); stack = s.stack; env = s.env;
         extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack }
     | PUSHCONSTINT n0 ->
       let new_stack = s.accu :: s.stack in
       Step { pc = pc'; accu = (Val_int n0); stack = new_stack; env = s.env;
       extra_args = s.extra_args; global = s.global; trap_stack =
       s.trap_stack }
     | NEGINT ->
       (match s.accu with
        | Val_int n0 ->
          Step { pc = pc'; accu = (Val_int (Z.opp n0)); stack = s.stack;
            env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = s.trap_stack }
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.add a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('A'::('D'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.sub a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('S'::('U'::('B'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.mul a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('M'::('U'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                else Step { pc = pc'; accu = (Val_int (Z.quot a b)); stack =
                       rest; env = s.env; extra_args = s.extra_args; global =
                       s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('D'::('I'::('V'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                else Step { pc = pc'; accu = (Val_int (Z.rem a b)); stack =
                       rest; env = s.env; extra_args = s.extra_args; global =
                       s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('M'::('O'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.coq_land a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('A'::('N'::('D'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.coq_lor a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.coq_lxor a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('X'::('O'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.shiftl a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('L'::('S'::('L'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.shiftr a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('L'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (Val_int (Z.shiftr a b)); stack =
                  rest; env = s.env; extra_args = s.extra_args; global =
                  s.global; trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('A'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
          Error
            ('A'::('S'::('R'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | EQ ->
       (match s.stack with
        | [] ->
          Error
            ('E'::('Q'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))
        | b :: rest ->
          Step { pc = pc'; accu =
            (if value_eqb s.accu b then val_true else val_false); stack =
            rest; env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = s.trap_stack })
     | NEQ ->
       (match s.stack with
        | [] ->
          Error
            ('N'::('E'::('Q'::(':'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))
        | b :: rest ->
          Step { pc = pc'; accu =
            (if value_eqb s.accu b then val_false else val_true); stack =
            rest; env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = s.trap_stack })
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
                Step { pc = pc'; accu = (val_bool (Z.ltb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (val_bool (Z.leb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('L'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (val_bool (Z.gtb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('G'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (val_bool (Z.geb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
          Error
            ('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))
     | OFFSETINT n0 ->
       (match s.accu with
        | Val_int a ->
          Step { pc = pc'; accu = (Val_int (Z.add a n0)); stack = s.stack;
            env = s.env; extra_args = s.extra_args; global = s.global;
            trap_stack = s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('O'::('F'::('F'::('S'::('E'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))))
     | OFFSETREF _ ->
       (match s.accu with
        | Val_int _ ->
          Error
            ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[]))))))))))))))))))))
        | Val_block (_, l) ->
          (match l with
           | [] ->
             Error
               ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[]))))))))))))))))))))
           | v :: _ ->
             (match v with
              | Val_int _ ->
                Step { pc = pc'; accu = val_unit; stack = s.stack; env =
                  s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('O'::('F'::('F'::('S'::('E'::('T'::('R'::('E'::('F'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::(' '::('r'::('e'::('f'::[])))))))))))))))))))))))
     | ISINT ->
       Step { pc = pc'; accu =
         (if is_int s.accu then val_true else val_false); stack = s.stack;
         env = s.env; extra_args = s.extra_args; global = s.global;
         trap_stack = s.trap_stack }
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
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('E'::('Q'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))
     | BNEQ (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.eqb a n0
          then Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
          else Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('N'::('E'::('Q'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))
     | BLTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.ltb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BLEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.leb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('L'::('E'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BGTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.gtb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('G'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[])))))))))))))))))))))))
     | BGEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.geb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (val_bool (Z.ltb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
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
                Step { pc = pc'; accu = (val_bool (Z.geb a b)); stack = rest;
                  env = s.env; extra_args = s.extra_args; global = s.global;
                  trap_stack = s.trap_stack }
              | Val_block (_, _) ->
                Error
                  ('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[])))))))))))))))))))))))))))))))))))))))
        | Val_block (_, _) ->
          Error
            ('U'::('G'::('E'::('I'::('N'::('T'::(':'::(' '::('t'::('y'::('p'::('e'::(' '::('e'::('r'::('r'::('o'::('r'::(' '::('o'::('r'::(' '::('s'::('t'::('a'::('c'::('k'::(' '::('u'::('n'::('d'::('e'::('r'::('f'::('l'::('o'::('w'::[]))))))))))))))))))))))))))))))))))))))
     | BULTINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.ltb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
          Error
            ('B'::('U'::('L'::('T'::('I'::('N'::('T'::(':'::(' '::('n'::('o'::('t'::(' '::('a'::('n'::(' '::('i'::('n'::('t'::('e'::('g'::('e'::('r'::[]))))))))))))))))))))))))
     | BUGEINT (n0, target) ->
       (match s.accu with
        | Val_int a ->
          if Z.geb n0 a
          then Step { pc = target; accu = s.accu; stack = s.stack; env =
                 s.env; extra_args = s.extra_args; global = s.global;
                 trap_stack = s.trap_stack }
          else Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
                 extra_args = s.extra_args; global = s.global; trap_stack =
                 s.trap_stack }
        | Val_block (_, _) ->
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
       Step { pc = pc'; accu = s.accu; stack = s.stack; env = s.env;
         extra_args = s.extra_args; global = s.global; trap_stack =
         s.trap_stack })
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
       | Some result -> run fuel' code (set_accu cont result) handle_ccall
       | None ->
         Run_error
           ('C'::(' '::('c'::('a'::('l'::('l'::(' '::('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))))
    fuel

(** val run_pure : int -> instruction list -> value list -> run_result **)

let run_pure fuel code global_data =
  run fuel code (initial_state global_data) (fun _ _ -> None)

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
