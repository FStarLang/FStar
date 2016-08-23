module Ex10b

open FStar.Heap
open FStar.ST

type point =
  | Point : x:ref int -> y:ref int{y<>x} -> point

val new_point: x:int -> y:int -> ST point
  (requires (fun h -> True))
  (ensures (fun h0 p h1 ->
                modifies TSet.empty h0 h1
                /\ fresh (Point.x p ^+^ Point.y p) h0 h1
                /\ Heap.sel h1 (Point.x p) = x
                /\ Heap.sel h1 (Point.y p) = y))
let new_point x y =
  let x = alloc x in
  let y = alloc y in
  Point x y

val shift: p:point -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> modifies (Point.x p ^+^ Point.y p) h0 h1))
let shift p =
  Point.x p := !(Point.x p) + 1;
  Point.y p := 17

// BEGIN: ShiftP1Spec
val shift_p1: p1:point
           -> p2:point{   Point.x p2 <> Point.x p1
                       /\ Point.y p2 <> Point.x p1
                       /\ Point.x p2 <> Point.y p1
                       /\ Point.y p2 <> Point.y p1 }
           -> ST unit
    (requires (fun h -> Heap.contains h (Point.x p2)
                    /\  Heap.contains h (Point.y p2)))
    (ensures (fun h0 _ h1 -> modifies (Point.x p1 ^+^ Point.y p1) h0 h1))
// END: ShiftP1Spec

let shift_p1 p1 p2 =
    let p2_0 = !(Point.x p2), !(Point.y p2)  in //p2 is initially p2_0
    shift p1;
    let p2_1 = !(Point.x p2), !(Point.y p2) in
    assert (p2_0 = p2_1)                        //p2 is unchanged

val test: unit -> St unit
let test () =
  let p1 = new_point 0 0 in
  recall (Point.x p1);
  recall (Point.y p1);
  let p2 = new_point 0 1 in
  recall (Point.x p2);
  recall (Point.y p2);
  shift_p1 p1 p2
