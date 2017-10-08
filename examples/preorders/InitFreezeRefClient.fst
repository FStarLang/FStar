module InitFreezeRefClient

open FStar.Heap
open FStar.ST
open InitFreezeRef

assume val complex_routine: unit -> ST unit (fun _ -> True) (fun _ _ _ -> True)

let test () :ST unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True)) =
  let r = alloc int in
  //let x = read r in  -- can't read, rightfully so
  write r 0;
  let x = read r in
  assert (x = 0);

  write r 1;
  let x = read r in
  assert (x = 1);

  let x = freeze r in

  //write r 2  -- fails, rightfully so

  complex_routine ();

  recall_freeze r x;

  let y = read r in
  assert (x = y);
  ()
