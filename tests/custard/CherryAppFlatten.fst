module CherryAppFlatten
module U32 = FStar.UInt32
open FStar.All

(* Inlining [lookup] hands it [wrap (scale 2)] for [c], and the body applies
   that to one more argument: [(wrap (scale 2)) v] is [wrap (scale 2) v], a
   direct call, and the outer partial application is never built. *)
let scale (k: int) (x: int) : ML int = k * x
let wrap (f: int -> ML int) (x: int) : ML (option int) =
  if x < 0 then None else Some (f x)

let get (s: int) : ML int = s + 1

[@@FStar.Attributes.custard_inline]
let lookup (s: int) (c: int -> ML 'a) : ML 'a = c (get s)

let doubled (s: int) : ML (option int) = lookup s (wrap (scale 2))

let main () : ML U32.t =
  match doubled 3, doubled (-5) with
  | Some 8, None -> 0ul
  | _ -> 1ul
