module PulseCore.BaseHeapSig
open FStar.Ghost
open FStar.PCM
module Set = FStar.GhostSet
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad

type mem : Type u#(a + 1) = H2.heap u#a

let empty_mem : mem u#a = H2.empty_heap

let disjoint_mem (m0 m1: mem) : prop = H2.disjoint m0 m1

let join_mem (m0:mem) (m1:mem { disjoint_mem m0 m1 }) : mem = H2.join m0 m1

let non_info (t:Type u#a) : Type u#a = x:erased t -> (y:t { y == reveal x })

let core_ref: Type u#0 = H2.core_ref
let core_ref_null = H2.core_ref_null
let is_null : core_ref -> GTot bool = H2.core_ref_is_null
let ref (a:Type u#a) (p:pcm a) = core_ref

let core_ghost_ref : Type u#0 = H2.core_ghost_ref
let core_ghost_ref_null = H2.core_ghost_ref_null
let ghost_ref (a:Type u#a) (p:pcm a) = core_ghost_ref
let add (#a:Type) (f:Set.decide_eq a) (x:a) (y:Set.set a) = Set.union (Set.singleton f x) y

let full_mem_pred m = H2.full_heap_pred m

let is_ghost_action m0 m1 : prop =
  H2.concrete m0 == H2.concrete m1

let slprop = H2.slprop

let is_affine_mem_prop (p:mem -> prop)
: prop
= forall (m0 m1:mem). p m0 /\ disjoint_mem m0 m1 ==> p (join_mem m0 m1)

let affine_mem_prop
= p:(mem u#a -> prop){ is_affine_mem_prop p }

val interp (p:slprop u#a) : affine_mem_prop u#a

val as_slprop (p:affine_mem_prop) : q:slprop{forall h. interp q h <==> p h}

let emp : slprop = H2.emp
val pure (p:prop) : slprop

let star (p1:slprop) (p2:slprop) : slprop =
  H2.star p1 p2
val star_equiv (p q:slprop u#a) (m:mem u#a)
: Lemma (
    interp (p `star` q) m <==> 
        (exists m0 m1. 
          disjoint_mem m0 m1 /\
          m == join_mem m0 m1 /\
          interp p m0 /\
          interp q m1)
  )

val slprop_extensionality (p q:slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)

val star_commutative (p q: slprop) : Lemma (star p q == star q p)
val star_associative p q r : Lemma (star (star p q) r == star p (star q r))

val interp_as (p:affine_mem_prop)
: Lemma (forall c. interp (as_slprop p) c == p c)

val emp_unit (p:slprop) : Lemma (p == (p `star` emp))

let update_ghost (m0:mem u#a) (m1:erased (mem u#a) { is_ghost_action m0 m1 })
: m:mem u#a { m == reveal m1 }
= H2.upd_ghost_heap m0 m1

val pure_true_emp () : Lemma (pure True == emp)
val intro_emp (h:mem) : Lemma (interp emp h)
val pure_interp (p:prop) (c:mem) : Lemma (interp (pure p) c == p)
let is_ghost_action_preorder () : Lemma (FStar.Preorder.preorder_rel is_ghost_action) = ()

let full_mem  = m:mem{ full_mem_pred m }
let maybe_ghost_action (maybe_ghost:bool) (m0 m1:mem)
    = maybe_ghost ==> is_ghost_action m0 m1

let step_t 
  (a:Type u#a)
  (maybe_ghost:bool)
  (expects:slprop)
  (provides: a -> GTot slprop)
  (frame:slprop)
= ST.st #(full_mem u#m) a
    (requires fun m0 ->
        interp (expects `star` frame) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action maybe_ghost m0 m1 /\
        interp (expects `star` frame) m0 /\  //TODO: fix the effect so as not to repeat this
        interp (provides x `star` frame) m1)

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let _action_except 
    (a:Type u#a)
    (maybe_ghost:bool)
    (expects:slprop u#m)
    (provides: a -> GTot slprop)
 : Type u#(max a (m + 1)) 
 = frame:slprop -> step_t a maybe_ghost expects provides frame

let action_except
    (a:Type u#a)
    (expects:slprop u#m)
    (provides:a -> GTot slprop)
= _action_except a false expects provides

let ghost_action_except
      (a:Type u#a)
      (expects:slprop u#m)
      (provides: a -> GTot slprop)
= _action_except a true expects provides

val core_ghost_ref_is_null (c:core_ghost_ref) : GTot bool
let non_null_core_ghost_ref = r:core_ghost_ref { not (core_ghost_ref_is_null r) }
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat
val addr_as_core_ghost_ref (addr:nat) : non_null_core_ghost_ref
val core_ghost_ref_as_addr_injective (c1:core_ghost_ref)
: Lemma 
  (requires not (core_ghost_ref_is_null c1))
  (ensures addr_as_core_ghost_ref (core_ghost_ref_as_addr c1) == c1)
val addr_as_core_ghost_ref_injective (a:nat)
: Lemma 
  (ensures core_ghost_ref_as_addr (addr_as_core_ghost_ref a) == a)
val select_ghost (i:nat) (m:mem u#a) : GTot (option (H.cell u#a))

val pts_to (#a:Type u#a) (#p:pcm a) (r:ref a p) (x:a) : slprop u#a
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref a p) (x:a) : slprop u#a

val ghost_extend
    (#a:Type)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except (ghost_ref a pcm) emp (fun r -> ghost_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except (erased (v:a{compatible p x v /\ p.refine v}))
        (ghost_pts_to r x)
        (fun v -> ghost_pts_to r (f v)) 

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except unit
        (ghost_pts_to r x)
        (fun _ -> ghost_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except unit
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except (squash (composable pcm v0 v1))
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val ghost_pts_to_not_null_action
      (#a:Type)
      (#pcm:pcm a)
      (r:ghost_ref a pcm)
      (v:Ghost.erased a)
: ghost_action_except (squash (r =!= core_ghost_ref_null))
    (ghost_pts_to r v)
    (fun _ -> ghost_pts_to r v)

val extend
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: action_except (ref a pcm) emp (fun r -> pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except (v:a{compatible p x v /\ p.refine v})
    (pts_to r x)
    (fun v -> pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except unit
    (pts_to r x)
    (fun _ -> pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except unit
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 `star` pts_to r v1)

val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except (squash (composable pcm v0 v1))
    (pts_to r v0 `star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val pts_to_not_null_action 
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: ghost_action_except (squash (not (is_null r)))
    (pts_to r v)
    (fun _ -> pts_to r v)

val lift_ghost
      (#a:Type u#a)
      (#p:slprop u#b)
      (#q:a -> GTot slprop)
      (ni_a:non_info a)
      (f:erased (ghost_action_except a p q))
: ghost_action_except a p q