module DebugProj

(* A projector applied to a value of the other constructor, of an unboxed
   tagged union.  A projector is a match with one branch. *)
open FStar.All

type t = | A of int | D of int

let main () : ML FStar.UInt32.t =
  let r = alloc (D 42) in
  if A?._0 !r = 42 then 0ul else 1ul
