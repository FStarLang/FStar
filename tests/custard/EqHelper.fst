module EqHelper
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 116.  [T__eq] is a perfectly ordinary F* identifier, so the
   generated structural comparison has to be allocated against the names the
   program itself defines rather than assumed free. *)
type pair = { x:U32.t; y:U32.t }

let pair__eq (x:U32.t) : U32.t = x

let same (a:pair) (b:pair) : bool = a = b

let main () : ML I32.t =
  if same ({ x = 1ul; y = 2ul }) ({ x = 1ul; y = 2ul })
     && not (same ({ x = 1ul; y = 2ul }) ({ x = 1ul; y = 3ul }))
     && U32.eq (pair__eq 5ul) 5ul
  then 0l else 1l
