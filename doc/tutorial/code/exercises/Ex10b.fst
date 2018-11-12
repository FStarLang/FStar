module Ex10b
//shift

open FStar.Ref

noeq type point =
  | Point : x:ref int -> y:ref int{addr_of y <> addr_of x} -> point

val new_point: x:int -> y:int -> ST point
  (requires (fun h -> True))
  (ensures (fun h0 p h1 ->
                modifies Set.empty h0 h1
                /\ fresh (Point?.x p) h0 h1
		/\ fresh (Point?.y p) h0 h1
                /\ Heap.sel h1 (Point?.x p) = x
                /\ Heap.sel h1 (Point?.y p) = y))
let new_point x y =
  let x = alloc x in
  let y = alloc y in
  Point x y

let shift_x p =
  Point?.x p := !(Point?.x p) + 1

// BEGIN: ShiftXP1Spec
val shift_x_p1: p1:point
           -> p2:point{   addr_of (Point?.x p2) <> addr_of (Point?.x p1)
                       /\ addr_of (Point?.y p2) <> addr_of (Point?.x p1) }
           -> ST unit
    (requires (fun h -> Heap.contains h (Point?.x p2)
                    /\  Heap.contains h (Point?.y p2)))
    (ensures (fun h0 _ h1 -> modifies (only (Point?.x p1)) h0 h1))
// END: ShiftXP1Spec

let shift_x_p1 p1 p2 =
    let p2_0 = !(Point?.x p2), !(Point?.y p2)  in //p2 is initially p2_0
    shift_x p1;
    let p2_1 = !(Point?.x p2), !(Point?.y p2) in
    admit(); //fix the precondition and remove the admit
    assert (p2_0 = p2_1)                         //p2 is unchanged


val test: unit -> St unit
let test () =
  let p1 = new_point 0 0 in
  recall (Point?.x p1);
  recall (Point?.y p1);
  let p2 = new_point 0 1 in
  recall (Point?.x p2);
  recall (Point?.y p2);
  shift_x_p1 p1 p2
