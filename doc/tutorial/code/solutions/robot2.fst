(*--build-config
    options:--admit_fsi Set --admit_fsi Map --z3timeout 20;
    variables:LIB=../../../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/map.fsi $LIB/list.fst $LIB/hyperheap2.fst
--*)
module Robot
open List
open Heap
open HyperHeap

type point =
  | Point : #r:rid
          -> x:rref r int
          -> y:rref r int
          -> z:rref r int{x<>y /\ y<>z /\ x<>z}
          -> point

type arm =
  | Arm : #r:rid
       -> polar:rref r int
       -> azim:rref r int{polar <> azim}
       -> arm

let disjoint (i:rid) (j:rid) =
  not (includes i j) && not (includes j i)

type bot =
  | Bot : #r:rid
       -> pos  :point{includes r (Point.r pos)}
       -> left :arm  {includes r (Arm.r left)}
       -> right:arm  {includes r (Arm.r right)
                        /\ disjoint (Point.r pos) (Arm.r left)
                        /\ disjoint (Point.r pos) (Arm.r right)
                        /\ disjoint (Arm.r left)  (Arm.r right)}
       -> bot

let refs_in_point (p:point) =
  !{as_ref (Point.x p),
    as_ref (Point.y p),
    as_ref (Point.z p)}

let refs_in_arm (a:arm) =
  !{as_ref (Arm.polar a),
    as_ref (Arm.azim a)}

let op_Plus_Plus x y = Set.union x y
let op_Plus_Plus_Hat x y = x ++ (Set.singleton y)
let op_Hat_Plus_Hat  x y = (Set.singleton x) ++ (Set.singleton y)

let refs (b:bot) =
  refs_in_point (Bot.pos b)
  ++ refs_in_arm (Bot.left b)
  ++ refs_in_arm (Bot.right b)

let regions (b:bot) =
  Bot.r b
  ^+^ Point.r (Bot.pos b)
  ++^ Arm.r (Bot.left  b)
  ++^ Arm.r (Bot.right b)

  (*/\ (forall (a:Type) (r:ref a). Set.mem (Heap.Ref r) (refs b)
                ==> Heap.contains (Map.sel h (Robot.i x)) r)*)

opaque type modifies1 (s:Set.set rid) (m0:t) (m1:t) =
  (forall (id:rid). Map.contains m0 id ==> Map.contains m1 id)
  /\ (forall (id:rid).//{:pattern (Map.sel m1 id)}
            Map.contains m0 id
            /\ (forall (mod:rid). Set.mem mod s ==> not (includes mod id))
            ==> Map.sel m1 id = Map.sel m0 id)

assume val mod_set : Set.set rid -> Tot (Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)


opaque logic type modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0))

let flying (b:bot) (h:HyperHeap.t) =
    sel h (Point.z (Bot.pos b)) > 0

let arms_up (b:bot) (h:HyperHeap.t) =
    sel h (Arm.polar (Bot.right b)) = 0
    && sel h (Arm.polar (Bot.left b)) = 0

type robot_inv (b:bot) (h:HyperHeap.t) =
  Map.contains h (Bot.r b)
  /\ Map.contains h (Point.r (Bot.pos b))
  /\ Map.contains h (Arm.r (Bot.left b))
  /\ Map.contains h (Arm.r (Bot.right b))
  /\ (flying b h ==> arms_up b h)

assume val lemma_disjoint_includes: i:rid -> j:rid -> k:rid ->
  Lemma (requires (disjoint i j /\ includes j k))
        (ensures (disjoint i k))
        [SMTPat (disjoint i j);
         SMTPat (includes j k)]
(*let lemma_disjoint_includes i j k = ()*)

assume val lemma_modifies_trans: m1:HyperHeap.t -> m2:HyperHeap.t -> m3:HyperHeap.t
                        -> s1:Set.set rid -> s2:Set.set rid
                        -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                                 (ensures (modifies (Set.union s1 s2) m1 m3))
                                 (*[SMTPatT (modifies s1 m1 m2);
                                  SMTPatT (modifies s2 m2 m3)]*)

val lemma_frame_robot_inv1 : b:bot -> h0:HyperHeap.t -> h1:HyperHeap.t -> i:rid{disjoint i (Bot.r b)}
  -> Lemma (requires (robot_inv b h0 /\ modifies (Set.singleton i) h0 h1))
           (ensures (robot_inv b h1))
let lemma_frame_robot_inv1 b h0 h1 i = ()

val lemma_frame_robot_inv2 : b:bot -> h0:HyperHeap.t -> h1:HyperHeap.t -> s:Set.set rid
  -> Lemma (requires (robot_inv b h0
                     /\ modifies s h0 h1
                     /\ (forall r. Set.mem r s ==> disjoint r (Bot.r b))))
           (ensures (robot_inv b h1))
let lemma_frame_robot_inv2 b h0 h1 s = ()

val new_point: r0:rid -> x:int -> y:int -> z:int -> ST point
    (requires (fun h0 -> True))
    (ensures (fun h0 p h1 ->
          modifies Set.empty h0 h1
          /\ extends (Point.r p) r0
          /\ fresh_region (Point.r p) h0 h1
          /\ sel h1 (Point.x p) = x
          /\ sel h1 (Point.y p) = y
          /\ sel h1 (Point.z p) = z))
let new_point r0 x y z=
  let r = new_region r0 in
  let x = ralloc r x in
  let y = ralloc r y in
  let z = ralloc r z in
  Point x y z

val new_arm: r0:rid -> ST arm
    (requires (fun h0 -> True))
    (ensures (fun h0 x h1 ->
          modifies Set.empty h0 h1
          /\ extends (Arm.r x) r0
          /\ fresh_region (Arm.r x) h0 h1))
let new_arm r0 =
  let r = new_region r0 in
  let p = ralloc r 0 in
  let a = ralloc r 0 in
  Arm p a

val test: r0:rid -> ST unit (requires (fun _ -> True)) (ensures (fun _ _ _ -> True))
let test r0 =
  let r = new_region r0 in
  let m0 = get() in
  cut (b2t(Map.contains m0 r));
  let m1 = magic() in
  admitP (modifies Set.empty m0 m1);
  assert (Map.contains m1 r)

val test1: r0:rid -> ST unit (requires (fun m0 -> Map.contains m0 r0)) (ensures (fun _ _ _ -> True))
let test1 r0 =
  let x = ralloc r0 0 in
  let m0 = get() in
  assert (sel m0 x = 0);
  let m1 = magic() in
  admitP (modifies Set.empty m0 m1);
  assert (sel m1 x = 0)


val new_robot: r0:rid -> ST bot (requires (fun h0 -> True))
                                (ensures (fun h0 x h1 ->
                                      modifies Set.empty h0 h1
                                      /\ extends (Bot.r x) r0
                                      /\ fresh_region (Bot.r x) h0 h1
                                      /\ robot_inv x h1))
let new_robot r0 =
  let r = new_region r0 in
  let p = new_point r 0 0 0 in
  let left = new_arm r in
  let right = new_arm r in
  Bot #r p left right

val walk_robot_to: x:int -> y:int -> b:bot -> ST unit
    (requires (robot_inv b))
    (ensures (fun h0 u h1 ->
                modifies (Set.singleton (Point.r (Bot.pos b))) h0 h1
                /\ robot_inv b h1
                /\ sel h1 (Point.z (Bot.pos b))  = sel h1 (Point.z (Bot.pos b))
                /\ sel h1 (Point.x (Bot.pos b))  = x
                /\ sel h1 (Point.y (Bot.pos b))  = y))
let walk_robot_to x y b =
 op_ColonEquals (Point.x (Bot.pos b)) x;
 op_ColonEquals (Point.y (Bot.pos b)) y

val fly: b:bot -> ST unit
  (requires (robot_inv b))
  (ensures (fun h0 _u h1 ->
              modifies (Set.singleton (Bot.r b)) h0 h1
              /\ robot_inv b h1
              /\ flying b h1))
let fly b =
  op_ColonEquals (Arm.polar (Bot.left b)) 0;
  op_ColonEquals (Arm.polar (Bot.right b)) 0;
  op_ColonEquals (Point.z (Bot.pos b)) 100

val fly_robots: b0:bot
             -> b1:bot{disjoint (Bot.r b0) (Bot.r b1)}
             -> ST unit
    (requires (fun h -> robot_inv b0 h /\ robot_inv b1 h))
    (ensures (fun h0 x h1 ->
              modifies (Bot.r b0 ^+^ Bot.r b1) h0 h1
              /\ robot_inv b0 h1
              /\ robot_inv b1 h1
              /\ flying b0 h1
              /\ flying b1 h1))
let fly_robots b0 b1 =
    let m0 = get () in
  fly b0;
    let m1 = get () in
  fly b1;
    let m2 = get () in
    lemma_frame_robot_inv1 b0 m1 m2 (Bot.r b1);
    lemma_modifies_trans m0 m1 m2 (Set.singleton (Bot.r b0)) (Set.singleton (Bot.r b1))

val main: unit -> ST unit
    (requires (fun _ -> True))
    (ensures (fun m0 _ m1 -> modifies Set.empty m0 m1))
let main () =
  let b1 = new_robot [] in
  let b2 = new_robot [] in
  fly_robots b1 b2
