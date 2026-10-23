module DebugIArray

(* An index past the end of an immutable array. *)
open FStar.All
module IA = FStar.ImmutableArray

let main () : ML FStar.UInt32.t =
  let a = IA.of_list [1; 2; 3] in
  let i = alloc 5 in
  if IA.index a !i = 0 then 0ul else 1ul
