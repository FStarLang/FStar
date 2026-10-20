module DebugMatch

(* An incomplete match, accepted only because the test admits its queries.
   The last branch is not tested, and every constructor carries an int, so
   without debug mode the call reads D's field as B's. *)
open FStar.All

type t = | A of int | B of int | D of int

let get (x:t) : int = match x with A n -> n | B n -> n + 1

let main () : ML FStar.UInt32.t =
  let r = alloc (D 42) in
  if get !r = 43 then 0ul else 1ul
