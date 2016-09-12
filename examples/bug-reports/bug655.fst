module Bug655

open FStar.Heap

let ghost_one () : GTot int = 1

assume val g: (u:unit) -> St unit

let test (u:unit) : St unit
  = ghost_one ();
    g(); // Crashes extraction
    ()
