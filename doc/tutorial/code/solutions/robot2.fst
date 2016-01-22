(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.HyperHeap --max_fuel 0 --initial_ifuel 0 --logQueries --z3timeout 20;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst hyperHeap.fsi stHyperHeap.fst allHyperHeap.fst FStar.Util.fst FStar.List.fst
--*)
module Robot
#set-options "--initial_ifuel 1 --max_ifuel 1"
open FStar.Heap
open FStar.Util
open FStar.HyperHeap

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

type bot =
  | Bot : #r:rid
       -> pos  :point{includes r (Point.r pos)}
       -> left :arm  {includes r (Arm.r left)}
       -> right:arm  {includes r (Arm.r right)
                        /\ disjoint (Point.r pos) (Arm.r left)
                        /\ disjoint (Point.r pos) (Arm.r right)
                        /\ disjoint (Arm.r left)  (Arm.r right)}
       -> bot

#set-options "--initial_fuel 0 --max_ifuel 0"
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

let only i = Set.singleton i

val lemma_frame_robot_inv1 : b:bot -> h0:HyperHeap.t -> h1:HyperHeap.t -> i:rid{disjoint i (Bot.r b)}
  -> Lemma (requires (robot_inv b h0 /\ modifies (only i) h0 h1))
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
                modifies (only (Point.r (Bot.pos b))) h0 h1
                /\ robot_inv b h1
                /\ sel h1 (Point.z (Bot.pos b))  = sel h1 (Point.z (Bot.pos b))
                /\ sel h1 (Point.x (Bot.pos b))  = x
                /\ sel h1 (Point.y (Bot.pos b))  = y))
let walk_robot_to x y b =
  Point.x (Bot.pos b) := x;
  Point.y (Bot.pos b) := y

val fly: b:bot -> ST unit
  (requires (robot_inv b))
  (ensures (fun h0 _u h1 ->
              modifies (only (Bot.r b)) h0 h1
              /\ robot_inv b h1
              /\ flying b h1))
let fly b =
  Arm.azim (Bot.right b)  := 17;
  Arm.polar (Bot.left b)  := 0;
  Arm.polar (Bot.right b) := 0;
  Point.z (Bot.pos b)     := 100

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
  fly b0;
  fly b1

open FStar.Set
type distinct (r:rid) (s:set rid) =
  forall x. Set.mem x s ==> disjoint x r

#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 1 --max_ifuel 1"
type bots : set rid -> Type =
  | Nil    : bots Set.empty
  | Cons   :  #rs:set rid
           -> hd:bot{distinct (Bot.r hd) rs}
           -> tl:bots rs
           -> bots (rs ++^ Bot.r hd)
val mem : #rs:set rid -> bot -> bs:bots rs -> Tot bool (decreases bs)
let rec mem  (#rs:set rid) b bs = match bs with
  | Nil -> false
  | Cons hd tl -> b=hd || mem b tl

val lemma_aux: #rs:set rid -> bs:bots rs -> b:bot
             -> Lemma (requires (mem #rs b bs))
                      (ensures (Set.mem (Bot.r b) rs))
                      (decreases bs)
                      [SMTPat (mem #rs b bs)]
let rec lemma_aux #rs bs b =
  match bs with
    | Nil -> ()
    | Cons hd tl ->
      if b=hd
      then ()
      else lemma_aux tl b

val lemma_bots_tl_disjoint : #rs:set rid -> bs:bots rs{is_Cons bs}
                           -> Lemma (requires (True))
                                    (ensures (forall b. mem b (Cons.tl bs) ==> disjoint (Bot.r b) (Bot.r (Cons.hd bs))))
let lemma_bots_tl_disjoint #rs bs = ()

opaque logic type trigger (#a:Type) (x:a) = True
val fly_robot_army:  #rs:Set.set rid
                  -> bs:bots rs
                  -> ST unit
                     (requires (fun h -> (forall b.{:pattern (trigger b)} (trigger b /\ mem b bs ==> robot_inv b h))))
                     (ensures  (fun h0 _u h1 ->
                                    modifies rs h0 h1
                                     /\ (forall b.{:pattern (trigger b)} (trigger b /\ mem b bs ==> robot_inv b h1 /\ flying b h1))))
let rec fly_robot_army #rs bs =
  match bs with
   | Nil -> ()
   | Cons #rs' hd tl  ->
         cut (trigger hd);
         cut (rs == (rs' ++^ Bot.r hd)); //not necesary, but goes faster with the hint
         lemma_bots_tl_disjoint bs; //again, not necessary; but goes faster
     fly hd;
     fly_robot_army tl

val main: unit -> ST unit
    (requires (fun _ -> True))
    (ensures (fun m0 _ m1 -> modifies Set.empty m0 m1))
let main () =
  let b1 = new_robot root in
  let b2 = new_robot root in
  fly_robots b1 b2
