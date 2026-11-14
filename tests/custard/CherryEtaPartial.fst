module CherryEtaPartial
module U32 = FStar.UInt32
open FStar.All

(* Extraction eta-reduces [same_id r k = eq_id r.id k] to one parameter.  A
   partial use elsewhere ([any (same_id r) ks]) must not keep it at
   one: Cherry builds a partial application for that use anyway, and a full
   call [same_id r k] should then be a direct call, not a closure applied. *)
type rcd = { id: int; tag: string }
let eq_id (a: int) (b: int) : ML bool = a = b
let same_id (r: rcd) (k: int) : ML bool = eq_id r.id k

let rec any (f: int -> ML bool) (l: list int) : ML bool =
  match l with [] -> false | x :: xs -> f x || any f xs

let any_same (r: rcd) (ks: list int) : ML bool = any (same_id r) ks
let both (r: rcd) (k: int) : ML bool = same_id r k && same_id r (k + 1)

let main () : ML U32.t =
  let r = { id = 3; tag = "x" } in
  if any_same r [1; 3] && not (both r 3) then 0ul else 1ul
