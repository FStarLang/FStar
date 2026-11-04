module CherryMonoLocalRec
module U32 = FStar.UInt32
open FStar.All

(* A partial application of a local [let rec] (here through the alias [go])
   passed to a [@@@monomorphize] binder.  Instantiating the specialization
   used to normalize the argument with zeta, unfolding [go'] without bound
   (error 365).  The SMT encoding currently trips over the same shape (a
   local [let rec] bound variable escapes into a VC), hence the admit. *)
#set-options "--admit_smt_queries true"

let rec iter (#a: Type) ([@@@FStar.Attributes.monomorphize] f: a -> ML unit) (l: list a) : ML unit =
  match l with
  | [] -> ()
  | x :: t -> f x; iter f t

type tree = | Leaf of int | Node of list tree

let sum_trees (xs: list tree) : ML int =
  let n = alloc 0 in
  let visit (t: tree) : ML unit =
    let rec go' (k: int) (top: bool) (t: tree) : ML unit =
      let go = go' k in
      match t with
      | Leaf x -> n := !n + x + k
      | Node ts -> iter (go false) ts
    in
    go' 1 true t in
  iter visit xs;
  !n

let main () : ML U32.t =
  if sum_trees [Node [Leaf 1; Node [Leaf 2]]; Leaf 3] = 9 then 0ul else 1ul
