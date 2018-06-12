module Ex11a
//robot

open FStar.Set
open FStar.HyperStack
open FStar.HyperStack.ST

module HST = FStar.HyperStack.ST

let only (#t:eqtype) (i:t) =
  singleton i

let op_Hat_Plus_Hat (r1:rid) (r2:rid) =
  union (singleton r1) (singleton r2)

let op_Plus_Plus_Hat (s:set rid) (r2:rid) =
  union s (singleton r2)

type distinct (r:rid) (s:set rid) =
  forall x. Set.mem x s ==> disjoint x r

// BEGIN: Types
noeq type point =
  | Point : r:rid
          -> x:ref int{frameOf x = r}
          -> y:ref int{frameOf y = r}
          -> z:ref int{frameOf z = r /\ as_addr x <> as_addr y /\ as_addr y <> as_addr z /\ as_addr x <> as_addr z}
          -> point

noeq type arm =
  | Arm : r:rid
       -> polar:ref int{frameOf polar = r}
       -> azim:ref int{frameOf azim = r /\ as_addr polar <> as_addr azim}
       -> arm

noeq type bot =
  | Bot : r:rid
        -> pos  :point{includes r (Point?.r pos)}
        -> left :arm  {includes r (Arm?.r left)}
        -> right:arm  {includes r (Arm?.r right)
                      /\ disjoint (Point?.r pos) (Arm?.r left)
                      /\ disjoint (Point?.r pos) (Arm?.r right)
                      /\ disjoint (Arm?.r left)  (Arm?.r right)}
        -> bot
// END: Types

// BEGIN: Invariant
let flying (b:bot) (h:mem) =
  sel h (Point?.z (Bot?.pos b)) > 0

let arms_up (b:bot) (h:mem) =
    sel h (Arm?.polar (Bot?.right b)) = 0
  /\ sel h (Arm?.polar (Bot?.left b))  = 0

type robot_inv (b:bot) (h:mem) =
    Map.contains (get_hmap h) (Bot?.r b)
  /\ Map.contains (get_hmap h) (Point?.r (Bot?.pos b))
  /\ Map.contains (get_hmap h) (Arm?.r (Bot?.left b))
  /\ Map.contains (get_hmap h) (Arm?.r (Bot?.right b))
  /\ (flying b h ==> arms_up b h)
// END: Invariant

// BEGIN: Build
val new_point: r0:rid{is_eternal_region r0} -> x:int -> y:int -> z:int -> ST point
  (requires (fun h0 -> True))
  (ensures (fun h0 p h1 ->
              modifies empty h0 h1
            /\ extends (Point?.r p) r0
            /\ fresh_region (Point?.r p) h0 h1
            /\ sel h1 (Point?.x p) = x
            /\ sel h1 (Point?.y p) = y
            /\ sel h1 (Point?.z p) = z))
let new_point r0 x y z =
  let r = new_region r0 in
  let x = ralloc r x in
  let y = ralloc r y in
  let z = ralloc r z in
  Point r x y z

val new_arm: r0:rid{is_eternal_region r0} -> ST arm
  (requires (fun h0 -> True))
  (ensures (fun h0 x h1 ->
              modifies empty h0 h1
            /\ extends (Arm?.r x) r0
            /\ fresh_region (Arm?.r x) h0 h1))
let new_arm r0 =
  let r = new_region r0 in
  let p = ralloc r 0 in
  let a = ralloc r 0 in
  Arm r p a

val new_robot: r0:rid{is_eternal_region r0} -> ST bot
  (requires (fun h0 -> True))
  (ensures (fun h0 x h1 ->
	      modifies empty h0 h1
            /\ extends (Bot?.r x) r0
            /\ fresh_region (Bot?.r x) h0 h1
            /\ robot_inv x h1))
let new_robot r0 =
  let r = new_region r0 in
  let p = new_point r 0 0 0 in
  let left = new_arm r in
  let right = new_arm r in
  Bot r p left right
// END: Build

val walk_robot_to: x:int -> y:int -> b:bot -> ST unit
  (requires (robot_inv b))
  (ensures (fun h0 u h1 ->
              modifies (only (Point?.r (Bot?.pos b))) h0 h1
            /\ robot_inv b h1
            /\ sel h1 (Point?.z (Bot?.pos b)) = sel h1 (Point?.z (Bot?.pos b))
            /\ sel h1 (Point?.x (Bot?.pos b)) = x
            /\ sel h1 (Point?.y (Bot?.pos b)) = y))
let walk_robot_to x y b =
  recall (Point?.x (Bot?.pos b));
  recall (Point?.y (Bot?.pos b));
  Point?.x (Bot?.pos b) := x;
  Point?.y (Bot?.pos b) := y

// BEGIN: Fly
val fly: b:bot -> ST unit
  (requires (fun h -> robot_inv b h))
  (ensures (fun h0 _u h1 ->
              modifies_transitively (only (Bot?.r b)) h0 h1
            /\ robot_inv b h1
            /\ flying b h1))
#set-options "--z3rlimit 20"
let fly b =
  recall (Arm?.azim (Bot?.right b));
  recall (Arm?.polar (Bot?.left b));
  recall (Arm?.polar (Bot?.right b));
  recall (Point?.z (Bot?.pos b));
  Arm?.azim (Bot?.right b)  := 17;
  Arm?.polar (Bot?.left b)  := 0;
  Arm?.polar (Bot?.right b) := 0;
  Point?.z (Bot?.pos b)     := 100
// END: Fly

// BEGIN: FlyBoth
val fly_both: b0:bot -> b1:bot{disjoint (Bot?.r b0) (Bot?.r b1)}
  -> ST unit
  (requires (fun h -> robot_inv b0 h /\ robot_inv b1 h))
  (ensures (fun h0 x h1 ->
              modifies_transitively (Bot?.r b0 ^+^ Bot?.r b1) h0 h1
            /\ robot_inv b0 h1
            /\ robot_inv b1 h1
            /\ flying b0 h1
            /\ flying b1 h1))
#set-options "--z3rlimit 50"
let fly_both b0 b1 =
  fly b0;
  fly b1
// END: FlyBoth

#reset-options "--z3rlimit 10"
val fly_one: b0:bot -> b1:bot{disjoint (Bot?.r b0) (Bot?.r b1)} -> ST unit
  (requires (fun h -> robot_inv b0 h /\ robot_inv b1 h /\ ~(flying b1 h)))
  (ensures (fun h0 x h1 ->
              modifies_transitively (only (Bot?.r b0)) h0 h1
            /\ robot_inv b0 h1
            /\ robot_inv b1 h1
            /\ flying b0 h1
            /\ ~(flying b1 h1)))
let fly_one b0 b1 =
  fly b0

noeq type bots : set rid -> Type =
  | Nil : bots empty
  | Cons : #rs:set rid
         -> hd:bot{distinct (Bot?.r hd) rs}
         -> tl:bots rs
         -> bots (rs ++^ Bot?.r hd)

val mem : #rs:set rid -> bot -> bs:bots rs -> Tot Type0 (decreases bs)
let rec mem  (#rs:set rid) b = function
  | Nil -> false
  | Cons hd tl -> b == hd \/ mem b tl

val lemma_mem_rid: #rs:set rid -> bs:bots rs -> b:bot
  -> Lemma (requires True)
          (ensures  (mem #rs b bs ==> Set.mem (Bot?.r b) rs))
	  (decreases bs)
          [SMTPat (mem #rs b bs)]
let rec lemma_mem_rid #rs bs b =
  match bs with
  | Nil -> ()
  | Cons hd tl -> lemma_mem_rid tl b

val lemma_bots_tl_disjoint: #rs:set rid -> bs:bots rs{Cons? bs}
  -> Lemma (requires True)
          (ensures (forall b. let Cons hd tl = bs in
			 mem b tl ==> disjoint (Bot?.r b) (Bot?.r hd)))
let lemma_bots_tl_disjoint #rs bs = ()

#reset-options "--z3rlimit 20"

module HS = FStar.HyperStack

let lemma_frame_robot_inv_and_flying
  (b:bot) (rs:set rid) (h0:HS.mem) (h1:HS.mem)
  :Lemma (requires (modifies_transitively rs h0 h1 /\ (forall r. Set.mem r rs ==> disjoint r (Bot?.r b)) /\ robot_inv b h0 /\ flying b h0))
         (ensures  (robot_inv b h1 /\ flying b h1))
  = ()

val fly_robot_army: #rs:set rid -> bs:bots rs -> ST unit
  (requires (fun h -> (forall b. mem b bs ==> robot_inv b h)))
  (ensures  (fun h0 _u h1 ->   modifies_transitively rs h0 h1
                          /\ (forall b. mem b bs ==> robot_inv b h1 /\ flying b h1)))
#set-options "--z3rlimit 50"
let rec fly_robot_army #rs bs =
  match bs with
  | Nil -> ()
  | Cons #rs' b bs' ->
    //cut (rs == (rs' ++^ Bot?.r b));  //not necesary, doesn't improve speed
    //lemma_bots_tl_disjoint bs;      //not necessary; doesnt' improve speed
    fly b;
    let h1 = HST.get () in
    fly_robot_army bs';
    let h2 = HST.get () in
    lemma_frame_robot_inv_and_flying b rs' h1 h2

val main: unit -> ST unit
    (requires (fun _ -> True))
    (ensures (fun m0 _ m1 -> modifies_transitively Set.empty m0 m1))
#set-options "--z3rlimit 20"
let main () =
  witness_region root;
  let b1 = new_robot root in
  let b2 = new_robot root in
  fly_both b1 b2
