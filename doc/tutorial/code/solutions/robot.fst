(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Map --z3timeout 25;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
--*)
module Robot

open FStar.List
open FStar.Heap
open FStar.HyperHeap

type point (i:rid) = {
    x:rref i int;
    y:rref i int;
    z:rref i int;
}
let refs_in_point (#i:rid) (a:point i) =
   !{(as_ref a.x),
     (as_ref a.y),
     (as_ref a.z)}

type arm (i:rid) = {
  polar:rref i int;
  azim:rref i int;
}

let refs_in_arm (#i:rid) (a:arm i) =
  !{(as_ref a.polar),
    (as_ref a.azim)}

type robot (i:rid) = {
  position:  p:point i{p.x<>p.y /\ p.y<>p.z /\ p.x<>p.z};
  left_arm:  a:arm i{a.polar <> a.azim};
  right_arm: a:arm i{a.polar <> a.azim};
}
logic type Disjoint (#a:Type) (s1:Set.set a) (s2:Set.set a) =
  Set.Equal (Set.intersect s1 s2) Set.empty
type t =
  | Robot : i:rid
         -> r:robot i{Disjoint (refs_in_point r.position) (refs_in_arm r.left_arm)
                      /\ Disjoint (refs_in_point r.position) (refs_in_arm r.right_arm)
                      /\ Disjoint (refs_in_arm r.left_arm) (refs_in_arm r.right_arm)}
         -> t

let refs_in (x:t) =
  let r = Robot.r x in
  Set.union (refs_in_point r.position)
            (Set.union (refs_in_arm r.left_arm)
                       (refs_in_arm r.right_arm))

type robot_inv (x:t) (h:HyperHeap.t) =
  Map.contains h (Robot.i x)
  /\ (forall (a:Type) (r:ref a). Set.mem (Heap.Ref r) (refs_in x)
                ==> Heap.contains (Map.sel h (Robot.i x)) r)
  /\ (sel h (Robot.r x).position.z > 0 //if flying
      ==> (sel h (Robot.r x).right_arm.polar = 0)) //then right arm is up!

val new_robot: r0:rid -> ST t (requires (fun h0 -> True))
                              (ensures (fun h0 x h1 ->
                                      HyperHeap.modifies Set.empty h0 h1
                                      /\ fresh_region (Robot.i x) h0 h1
                                      /\ robot_inv x h1))
let new_robot r0 =
  let r = new_region r0 in
  let x = {position={x=ralloc r 0; y=ralloc r 0; z=ralloc r 0};
           left_arm={polar=ralloc r 180; azim=ralloc r 0};
           right_arm={polar=ralloc r 180; azim=ralloc r 0}} in
  Robot r x

val walk_robot_to: x:int -> y:int -> r:t -> ST unit
    (requires (robot_inv r))
    (ensures (fun h0 u h1 ->
                HyperHeap.modifies (Set.singleton (Robot.i r)) h0 h1
                /\ Heap.modifies !{as_ref ((Robot.r r).position.x),
                                   as_ref ((Robot.r r).position.y)}
                                  (Map.sel h0 (Robot.i r)) (Map.sel h1 (Robot.i r))
                /\ robot_inv r h1
                /\ sel h1 (Robot.r r).position.x = x
                /\ sel h1 (Robot.r r).position.y = y))
let walk_robot_to x y r =
 let robot = Robot.r r in
 assert (Set.mem (Ref (as_ref (robot.right_arm.polar))) (refs_in_arm robot.right_arm));
 op_Colon_Equals robot.position.x x;
 op_Colon_Equals robot.position.y y
