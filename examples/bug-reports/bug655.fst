module Bug655

open FStar.All
open FStar.Heap

let ghost_one () : GTot int = 1

assume val g: (u:unit) -> St unit

let test (u:unit) : St unit
  = ghost_one (); //rightfully complains about int </: unit
    g(); // (used to crash extraction)
    ()

let test2 (u:unit) : St unit
  = let _ = ghost_one () in //rightfully complains about Ghost nat not being composable with ST
    g(); // (used to crash extraction)
    ()
