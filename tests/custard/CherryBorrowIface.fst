module CherryBorrowIface
open FStar.All
module U32 = FStar.UInt32

(* [[@@@cherry_borrowed]] written on the implementation only: the interface
   supplies the type, and specialization must not lose the attribute. *)
let head_or #a ([@@@FStar.Attributes.cherry_borrowed] r) d =
  match !r with x :: _ -> x | [] -> d

(* An owned temporary passed in tail position: with [r] borrowed, the call
   is not a tail call and the caller drops the reference afterwards. *)
let first (rr: ref (ref (list string))) : ML string = head_or (!rr) "-"

let main () =
  let rr = alloc (alloc ["a"; "b"]) in
  if first rr = "a" && first rr = "a" then 0ul else 1ul
