module CherryInlineHO
module U32 = FStar.UInt32
open FStar.All

(* Combinators marked [@@custard_inline] are inlined, so a lambda given to
   them meets its call and is no closure (cherry.md, "Functions"). *)
[@@FStar.Attributes.custard_inline]
let apply_plus_one (f: int -> ML int) (x: int) : ML int = f x + 1

let rec existsb (f: int -> ML bool) (l: list int) : ML bool =
  match l with
  | [] -> false
  | x :: xs -> if f x then true else existsb f xs

(* Eta-reduced to [some f = existsb f] before inlining: the call's second
   argument completes the application of [existsb]. *)
[@@FStar.Attributes.custard_inline]
let some (f: int -> ML bool) (l: list int) : ML bool = existsb f l

let add (k: int) (x: int) : ML int = apply_plus_one (fun y -> y + k) x

let has_above (k: int) (l: list int) : ML bool = some (fun y -> y > k) (0 :: l)

let main () : ML U32.t =
  if add 3 1 = 5 && has_above 2 [1; 2; 3] && not (has_above 5 [1]) then 0ul else 1ul
