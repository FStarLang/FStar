module Bug2412

open FStar.Set
open FStar.All

// Set.as_set was not extracting correctly; it was undefined
// in FStar_Set
let list_to_set (l:list nat) : Tot (Set.set nat) = 
  Set.as_set l

// Test that the underlying library function works as expected.
let test _ : ML unit =
  let actual = list_to_set [1;2;3] in

  if Set.mem 1 actual && Set.mem 2 actual && Set.mem 3 actual then
     ()
  else
     failwith "positive membership check failed";

  if Set.mem 0 actual then
     failwith "negative membership check failed"
  else
     ()

let _ = test()
