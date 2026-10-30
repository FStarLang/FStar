module CherryLocalFn
module U32 = FStar.UInt32
open FStar.All

(* Inlining a combinator that calls its argument twice binds the lambda to a
   name.  A local function that is only ever called, with all its arguments,
   is no closure: the calls go to the lifted definition directly, passing what
   it captured (cherry.md, "Functions"). *)
[@@FStar.Attributes.custard_inline]
let twice (f: int -> ML int) (x: int) : ML int = f (f x)

let use_twice (k: int) (x: int) : ML int = twice (fun y -> y + k) x

(* The combinator binds a name the lambda captures in the caller. *)
[@@FStar.Attributes.custard_inline]
let twice_let (f: int -> ML int) (x: int) : ML int = let k = f x in f k

let use_twice_let (k: int) : ML int = twice_let (fun y -> y + k) 1

(* Passed as well as called: still a closure. *)
[@@FStar.Attributes.custard_inline]
let call_and_pass (f: int -> ML int) (x: int) : ML int = f x + List.length (List.map f [x])

let use_call_and_pass (k: int) : ML int = call_and_pass (fun y -> y + k) 1

let main () : ML U32.t =
  if use_twice 3 1 = 7 && use_twice_let 3 = 7 && use_call_and_pass 3 = 5
  then 0ul else 1ul
