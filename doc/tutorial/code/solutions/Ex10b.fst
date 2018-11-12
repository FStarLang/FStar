module Ex10b
//shift

open FStar.Ref


noeq type point =
  | Point : x:ref int -> y:ref int{addr_of y <> addr_of x} -> point

// BEGIN: NewPointType
val new_point: x:int -> y:int -> ST point
  (requires (fun h -> True))
  (ensures (fun h0 p h1 ->
                modifies Set.empty h0 h1
                /\ Heap.fresh (Point?.x p) h0 h1
		/\ Heap.fresh (Point?.y p) h0 h1
                /\ Heap.sel h1 (Point?.x p) = x
                /\ Heap.sel h1 (Point?.y p) = y
                /\ Heap.contains h1 (Point?.x p) //these two lines should be captures by fresh
                /\ Heap.contains h1 (Point?.y p)))
// END: NewPointType
// BEGIN: NewPoint
let new_point x y =
  let x = ST.alloc x in
  let y = ST.alloc y in
  Point x y
// END: NewPoint

// BEGIN: ShiftXType
val shift_x: p:point -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> modifies (only (Point?.x p)) h0 h1))
// END: ShiftXType
let shift_x p =
  Point?.x p := !(Point?.x p) + 1

val shift_x_p1: p1:point
             -> p2:point{   addr_of (Point?.x p2) <> addr_of (Point?.x p1)
                          /\ addr_of (Point?.y p2) <> addr_of (Point?.x p1)
                          /\ addr_of (Point?.x p2) <> addr_of (Point?.y p1)
                          /\ addr_of (Point?.y p2) <> addr_of (Point?.y p1) }
           -> ST unit
    (requires (fun h -> Heap.contains h (Point?.x p2)
                    /\  Heap.contains h (Point?.y p2)))
    (ensures (fun h0 _ h1 -> modifies (only (Point?.x p1)) h0 h1))

// BEGIN: ShiftXP1
let shift_x_p1 p1 p2 =
    let p2_0 = !(Point?.x p2), !(Point?.y p2)  in //p2 is initially p2_0
    shift_x p1;
    let p2_1 = !(Point?.x p2), !(Point?.y p2) in
    assert (p2_0 = p2_1)                        //p2 is unchanged
// END: ShiftXP1


 (*
//The following won't typecheck
// BEGIN: Test0
val test0: unit -> St unit
let test0 () =
  let p1 = new_point 0 0 in
  shift_x_p1 p1 p1
// END: Test0
*)

// BEGIN: Test1
val test1: unit -> St unit
let test1 () =
  let p1 = new_point 0 0 in
  let p2 = new_point 0 0 in
  shift_x_p1 p1 p2
// END: Test1

// BEGIN: Test2
val test2: unit -> St unit
let test2 () =
  let p = new_point 0 0 in
  let z :ref nat = ST.alloc 0 in
  assert (addr_of (Point?.x p) <> addr_of z)
// END: Test2



// BEGIN: ShiftP1Solution
let shift p =
  Point?.x p := !(Point?.x p) + 1;
  Point?.y p := !(Point?.y p) + 1


val shift_p1: p1:point
           -> p2:point{   addr_of (Point?.x p2) <> addr_of (Point?.x p1)
                       /\ addr_of (Point?.y p2) <> addr_of (Point?.x p1)
                       /\ addr_of (Point?.x p2) <> addr_of (Point?.y p1)
                       /\ addr_of (Point?.y p2) <> addr_of (Point?.y p1) }
           -> ST unit
    (requires (fun h -> Heap.contains h (Point?.x p2)
                    /\  Heap.contains h (Point?.y p2)))
    (ensures (fun h0 _ h1 -> modifies (Point?.x p1 ^+^ Point?.y p1) h0 h1))

let shift_p1 p1 p2 =
    let p2_0 = !(Point?.x p2), !(Point?.y p2)  in //p2 is initially p2_0
    shift p1;
    let p2_1 = !(Point?.x p2), !(Point?.y p2) in
    assert (p2_0 = p2_1)                        //p2 is unchanged
// END: ShiftP1Solution



val test: unit -> St unit
let test () =
  let p1 = new_point 0 0 in
  let p2 = new_point 0 1 in
  shift_p1 p1 p2
