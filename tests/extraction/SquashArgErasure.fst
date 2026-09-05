(* An implicit `squash` argument must be dropped at extraction even when the
   binder it corresponds to is hidden inside the *result* of a type
   abbreviation, rather than appearing among the head's own binders. *)
module SquashArgErasure

type result (a:Type) =
  | RSuccess of a
  | RFail

let t_t =
    (x: int) ->
    (y: int) ->
    Pure (result unit)
      (requires x >= 0 /\ y >= 0)
      (ensures fun res -> match res with | RSuccess _ -> x >= 0 | _ -> True)

let callee (f: t_t) : Tot t_t = fun x y -> f x y

let rec caller (fuel: nat) : t_t =
  fun x y ->
    if fuel = 0
    then RFail
    else let fuel' : nat = fuel - 1 in
         callee (caller fuel') x y
