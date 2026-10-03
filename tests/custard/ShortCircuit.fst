module ShortCircuit

(* Section 6, pass 1: [&&] and [||] are short-circuiting, and Custard has to
   keep them that way.

   Two things are being tested, because two different mechanisms are
   responsible.

   1. When an operand is *effectful*, F* itself has already rewritten the
      connective into an [if], so Custard never sees an [EOp] at all.  [order]
      pins that down: were it not so, "ab" would come out reversed or the
      right-hand tick would run when it must not.

   2. When both operands are pure, the connective survives as an [EOp] and the
      backend must emit it infix.  A prefix [((&&) a b)] happens to
      short-circuit in OCaml too -- [&&] is the [%sequand] primitive -- but not
      in a way any reader could be expected to know, and not at all in C.
      [safe] and [idx] are the cases where it *matters*: F* discharges the
      precondition of the division and of [index] precisely by reasoning that
      the right operand is not reached, so evaluating it would divide by zero
      and walk off the end of a list. *)

open FStar.All
open FStar.IO
module L = FStar.List.Tot

let tick (s:string) (b:bool) : ML bool = print_string s; b

let order () : ML string =
  let a = tick "a" false && tick "X" true in
  let b = tick "b" true || tick "X" false in
  string_of_bool a ^ string_of_bool b

let safe (x:int) : bool = x <> 0 && 100 / x > 5

let safe_or (x:int) : bool = x = 0 || 100 / x > 5

let idx (l: list int) (i: nat) : bool = i < L.length l && L.index l i > 0

(* [&&] at a width is *bitwise*, and strict: it must not be treated as delayed. *)
let mask (x:FStar.UInt32.t) : FStar.UInt32.t = FStar.UInt32.logand x 255ul

let main () : ML unit =
  let o = order () in
  print_string (o ^ "|" ^ string_of_bool (safe 0) ^ string_of_bool (safe 10)
                    ^ "|" ^ string_of_bool (safe_or 0) ^ string_of_bool (safe_or 1)
                    ^ "|" ^ string_of_bool (idx [1; 2] 5) ^ string_of_bool (idx [1; 2] 0)
                    ^ "|" ^ FStar.UInt32.to_string (mask 511ul) ^ "\n")
