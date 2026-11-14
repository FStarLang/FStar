module CherryStaticPap
module U32 = FStar.UInt32
open FStar.All

(* Partial applications to constants only -- a static closure, a string
   literal, a small integer -- are persistent closures in static
   storage, not allocated each time [pick] runs. *)
let tag (s: string) (n: int) (x: int) : ML string =
  if x = n then s ^ "!" else s
let twice (f: int -> ML int) (x: int) : ML int = f (f x)
let incr (x: int) : ML int = x + 1
let const_unit (u: unit) (x: int) : ML int = x

let apply (f: int -> ML 'a) (x: int) : ML 'a = f x
let sum10 (acc: int) (f: int -> ML int) : ML int = acc + f 10

let pick (k: int) : ML (int -> ML int) =
  match k with
  | 0 -> twice incr
  | 1 -> const_unit ()
  | _ -> incr

let main () : ML U32.t =
  let fs = [pick 0; pick 1; pick 0; pick 2] in
  let sum = List.fold_left sum10 0 fs in
  if sum = 12 + 10 + 12 + 11 && apply (tag "a" 3) 3 = "a!" && apply (tag "a" 3) 4 = "a"
  then 0ul else 1ul
