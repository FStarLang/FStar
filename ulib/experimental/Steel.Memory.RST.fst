module Steel.Memory.RST

open Steel.Memory
open LowStar.Permissions

new_effect GST = STATE_h mem

let gst_pre = st_pre_h mem
let gst_post' (a:Type) (pre:Type) = st_post_h' mem a pre
let gst_post (a:Type) = st_post_h mem a
let gst_wp (a:Type) = st_wp_h mem a

unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:mem) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

effect ST (a:Type) (pre:gst_pre) (post: (m0:mem -> Tot (gst_post' a (pre m0)))) =
  GST a
    (fun (p:gst_post a) (h:mem) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1))

/// Attribute for normalization
let __reduce__ = ()

(** TODO: Add a value_depends_only_on fp predicate. With this predicate,
    we should be able to conclude that any predicate defined using only the views
    is on fp_prop fp **)
type view (a:Type) (fp:hprop) = (m:hheap fp) -> a

(** An extension of hprops to include a view.
    Note that the type of the view is not related to the fprop, and is completely up to the user.
    For hprops for which we cannot defined a view, we thus could use unit.
    TODO: This should have a better name. hprop_with_view?
    **)
noeq
type viewable' = {
    t:Type0;
    fp:hprop;
    sel:view t fp }

(** Redefine an inductive for Star on top of hprops/viewables. This will allow us
    to normalize by induction on the datatype **)
noeq type viewable =
   | VUnit: viewable' -> viewable
   | VStar: viewable -> viewable -> viewable

(** TODO: Could we go to a "flat" representation of tuples from t_of? **)
[@__reduce__]
let rec t_of (v:viewable) = match v with
  | VUnit v -> v.t
  | VStar v1 v2 -> (t_of v1 * t_of v2)

[@__reduce__]
let rec fp_of (v:viewable) = match v with
  | VUnit v -> v.fp
  | VStar v1 v2 -> (fp_of v1 `star` fp_of v2)

[@__reduce__]
let rec sel_of (v:viewable) (h:hheap (fp_of v)) : t_of v = match v with
  | VUnit v -> v.sel h
  | VStar v1 v2 ->
    affine_star (fp_of v1) (fp_of v2) h;
    (sel_of v1 h, sel_of v2 h)

(** Completely incorrect, but used for test purposes. In the tests below, the left resource
    will always be the leftmost starred hprop **)
[@__reduce__]
let rec incorrect_left_sel
  (outer inner:viewable)
  (delta:viewable)
  (v:t_of outer)
  : GTot (t_of inner)
  = match outer with
    | VUnit r -> assume (VUnit r == inner); v
    | VStar r1 r2 ->
      let (v1, v2) : t_of r1 * t_of r2 = v in incorrect_left_sel r1 inner delta v1

(** Similar for right_sel **)
[@__reduce__]
let rec incorrect_right_sel
  (outer:viewable{VStar? outer})
  (inner delta:viewable)
  (v:t_of outer)
  : GTot (t_of delta)
  = match outer with
    | VStar (VUnit r1) r2 ->
        let (v1, v2) : t_of (VUnit r1) * t_of r2 = v in
        assume (r2 == delta);
        v2
    | VStar r1 r2 ->
        let (v1, v2) : t_of r1 * t_of r2 = v in
        admit();
        incorrect_right_sel r1 inner delta v1, v2


/// Reimplementing tactics for framing.
/// AF: This should be moved to a separate module once hprops with views are stable and
/// moved to Steel.Memory

// Irreducible for now because of goals disappearing in tactics again...
// This should just be hidden behind a val in another module,
// while exposing all the necessary lemmas
irreducible
let equiv (r1 r2:viewable) : prop = equiv (fp_of r1) (fp_of r2) /\ True

let can_be_split_into (outer inner delta:viewable) : prop =
  (VStar inner delta) `equiv` outer

(** A more convenient notation for VStar **)
[@__reduce__]
unfold
let (<*>) = VStar

module CME = FStar.Algebra.CommMonoid.Equiv
module T = FStar.Tactics
module TCE = FStar.Tactics.CanonCommMonoidSimple.Equiv

let equiv_refl (x:viewable) : Lemma (equiv x x) = admit()

let equiv_sym (x y:viewable) : Lemma
  (requires equiv x y)
  (ensures equiv y x)
  = admit()

let equiv_trans (x y z:viewable) : Lemma
  (requires equiv x y /\ equiv y z)
  (ensures equiv x z)
  = admit()

inline_for_extraction noextract
let req : CME.equiv viewable =
  CME.EQ equiv
         equiv_refl
         equiv_sym
         equiv_trans

let vemp' : viewable' = {
  t = unit;
  fp = emp;
  sel = fun _ -> () }

[@__reduce__]
let vemp : viewable = VUnit vemp'

let cm_identity (x:viewable) : Lemma ((vemp <*> x) `equiv` x)
  = admit()

let star_commutative (p1 p2:viewable)
  : Lemma ((p1 <*> p2) `equiv` (p2 <*> p1))
  = admit()

let star_associative (p1 p2 p3:viewable)
  : Lemma ((p1 <*> p2 <*> p3)
           `equiv`
           (p1 <*> (p2 <*> p3)))
  = admit()

let star_congruence (p1 p2 p3 p4:viewable)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv`p4)
          (ensures (p1 <*> p2) `equiv` (p3 <*> p4))
  = admit()

[@__reduce__]
inline_for_extraction noextract
let rm : CME.cm viewable req =
  CME.CM vemp
         (<*>)
         cm_identity
         star_associative
         star_commutative
         star_congruence

let canon () : T.Tac unit = TCE.canon_monoid (`req) (`rm)

let squash_and p q (x:squash (p /\ q)) : (p /\ q) =
  let x : squash (p `c_and` q) = FStar.Squash.join_squash x in
  x

let can_be_split_into_star (res1 res2 res3:viewable)
  : Lemma
    (requires ((res2 <*> res3) `equiv` res1))
    (ensures  (can_be_split_into res1 res2 res3))
  = ()

// AF: The tactic is not yet working because of <*>.
// Inside canon_monoid, specifically in reification_aux, a normalized mult is compared
// to the current function applied. Since <*> is not the same term as VStar,
// the resource is not split into atoms.
// Why does this happen although <*> is defined as unfold?
inline_for_extraction noextract let resolve_frame () : T.Tac unit =
  T.refine_intro();
  T.flip();
  T.apply_lemma (`T.unfold_with_tactic);
  T.split();
  T.apply_lemma (`can_be_split_into_star);
  T.flip();
  canon();
  T.trivial()

inline_for_extraction noextract let reprove_frame () : T.Tac unit =
  T.apply (`squash_and);
  T.split();
  T.apply_lemma (`can_be_split_into_star);
  canon();
  T.trivial()



(** A shortcut for the normalization. We need to reduce all our recursive functions **)
unfold
let normal (#a:Type) (x:a) =
  let open FStar.Algebra.CommMonoid.Equiv in
  norm [delta_attr [`%__reduce__];
       delta;
        delta_only [
          `%__proj__CM__item__mult;
          `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
          `%fst; `%snd];
        primops; iota; zeta] x



(** AF: These functions should be the ones actually doing the rewriting in the end.
    I think we can implement them using a variant of the canon_monoid tactic.
    The postconditions are here for documentation purposes, we would probably need them
    as lemmas to prove the correctness of frame
    **)
assume val left_sel
  (outer inner:viewable)
  (delta:viewable{can_be_split_into outer inner delta})
  (v:t_of outer)
  : Ghost (t_of inner)
          (requires True)
         (ensures fun v' -> (forall (h:hheap (fp_of outer)).
           (assume (interp (fp_of inner) h);
           (sel_of outer h) == v ==> (sel_of inner h) == v')))

assume val right_sel
  (outer inner:viewable)
  (delta:viewable{can_be_split_into outer inner delta})
  (v:t_of outer)
  : Ghost (t_of delta)
          (requires True)
         (ensures fun v' -> (forall (h:hheap (fp_of outer)).
           (assume (interp (fp_of delta) h);
           (sel_of outer h) == v ==> (sel_of delta h) == v')))

effect Steel
  (a: Type)
  (res0: viewable)
  (res1: a -> viewable)
  (pre: (t_of res0) -> prop)
  (post: (t_of res0) -> (x:a) -> (t_of (res1 x)) -> prop)
= ST
  a
  (fun h0 ->
    interp (fp_of res0) (heap_of_mem h0) /\
    pre (normal (sel_of res0 (heap_of_mem h0))))
  (fun h0 x h1 ->
    interp (fp_of res0) (heap_of_mem h0) /\
    pre (normal (sel_of res0 (heap_of_mem h0))) /\
    interp (fp_of (res1 x)) (heap_of_mem h1) /\
    post (normal (sel_of res0 (heap_of_mem h0)))
         x
         (normal (sel_of (res1 x) (heap_of_mem h1)))
  )

(** We underspecify get: It returns a heap about which we only know that
    the resource invariant is satisfied, and that the views of the resouce
    correspond to the ones we would compute from this heap **)
assume val get (r:viewable)
  :Steel (hheap (fp_of r)) (r) (fun _ -> r)
             (requires (fun m -> True))
             (ensures (fun m0 x m1 -> m0 == m1 /\
               m0 == normal (sel_of r x)))

(*

assume val put (r_init r_out:viewable) (m:hmem r_out.fp)
  :Steel unit (r_init) (fun _ -> r_out)
             (requires fun m -> True)
             (ensures (fun _ _ m1 ->
               affine_star r_out.fp (locks_invariant m) (heap_of_mem m);
               m1 == r_out.sel (heap_of_mem m)))
*)

(** A few lemmas to cast between the different pointer hprops **)
let interp_perm_to_ptr (#a:Type) (p:permission) (r:ref a) (h:heap)
  : Lemma (requires interp (ptr_perm r p) h)
          (ensures interp (ptr r) h)
  = let lem (v:a) (h:heap) : Lemma
   (requires interp (pts_to r p v) h)
   (ensures interp (ptr r) h)
   = intro_exists v (pts_to r p) h;
     intro_exists p (ptr_perm r) h
   in Classical.forall_intro (Classical.move_requires (fun v -> lem v h));
   elim_exists (pts_to r p) (ptr r) h

let interp_pts_to_perm (#a:Type) (p:permission) (r:ref a) (v:a) (h:heap)
  : Lemma (requires interp (pts_to r p v) h)
          (ensures interp (ptr_perm r p) h)
  = let lem (v:a) (h:heap) : Lemma
     (requires interp (pts_to r p v) h)
     (ensures interp (ptr_perm r p) h)
     = intro_exists v (pts_to r p) h
     in Classical.forall_intro (Classical.move_requires (fun v -> lem v h))

let pts_to_sel (#a:Type) (p:permission) (r:ref a) (v:a) (h:heap)
  : Lemma (requires interp (pts_to r p v) h)
          (ensures interp (ptr r) h /\ sel r h == v)
  = interp_pts_to_perm p r v h; interp_perm_to_ptr p r h;
    sel_lemma r p h;
    pts_to_injective r p v (sel r h) h
(*
let vptr_perm #a (r:ref a) (p:permission) = {
  t = unit;
  fp = ptr_perm r p;
  sel = fun _ -> ()}

let vptr #a (r:ref a) = {
  t = a;
  fp = ptr r;
  sel = fun h -> sel r h}

let vpts_to #a (r:ref a) (p:permission) (v:a) = {
  t = a;
  fp = pts_to r p v;
  sel = fun _ -> v}

val perm_to_ptr (#a:Type) (p:permission) (r:ref a) : Steel unit
  (vptr_perm r p)
  (fun _ -> vptr r)
  (fun _ -> True)
  (fun h0 _ h1 -> h0 == h1)

let perm_to_ptr #a p r =
 admit();
 let h = get (vptr_perm r p) in
 interp_perm_to_ptr p r (heap_of_mem h)

val pts_to_perm (#a:Type) (p:permission) (r:ref a) (v:a) : Steel unit
  (vpts_to r p v)
  (fun _ -> vptr_perm r p)
  (fun _ -> True)
  (fun h0 _ h1 -> True) // interp (ptr r) (heap_of_mem h1) /\ h0 == h1 /\ sel r (heap_of_mem h1) == v)

let pts_to_perm  #a p r v =
 admit();
 let h = get (vpts_to r p v) in
 interp_pts_to_perm p r v (heap_of_mem h);
 interp_perm_to_ptr p r (heap_of_mem h);
 pts_to_sel p r v (heap_of_mem h)

val ptr_read (#a:Type) (r:ref a) : Steel a
  (vptr_perm r full_permission)
  (fun v -> vpts_to r full_permission v)
  (fun _ -> True)
  (fun _ _ _ -> True)

let ptr_read #a r =
 admit();
 perm_to_ptr full_permission r;
 let h = get (vptr r) in
 let v = sel r (heap_of_mem h) in
 sel_lemma r full_permission (heap_of_mem h);
 v

val ptr_update (#a:Type) (r:ref a) (v:a) : Steel unit
  (ptr_perm r full_permission)
  (fun _ -> pts_to r full_permission v)
  (fun _ -> True)
  (fun _ _ _ -> True)

let ptr_update #a r v =
  perm_to_ptr #a full_permission r;
  let h = get (ptr_perm r full_permission) in
  let (| _, h' |) = upd r v h in
  put (ptr_perm r full_permission) (pts_to r full_permission v) h'
*)

(** Shortcut for a pointer with full permission **)
let fptr (#a:Type) (r:ref a) : hprop = ptr_perm r full_permission

let fsel (#a:Type) (r:ref a) (h:hheap (fptr r)) : a =
  interp_perm_to_ptr full_permission r h;
  sel r h

(** The actual hprop with view for a pointer. Its view has the same type as the pointer **)
let vptr' (#a:Type) (r:ref a) : viewable' =
  ({ t = a;
    fp = fptr r;
    sel = fun h -> fsel r h })

[@__reduce__]
let vptr (#a:Type) (r:ref a) : viewable = VUnit (vptr' r)

val fread (#a:Type) (r:ref a) : Steel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun m0 v m1 -> m0 == m1 /\ m1 == v)

(** TODO: Reimplement this **)
let fread #a r = admit()
  // let v = ptr_read #a r in
  // pts_to_perm full_permission r v;
  // v

val fupd (#a:Type) (r:ref a) (v:a) : Steel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ m1 -> m1 == v)

(** TODO: Reimplement this **)
let fupd #a r v = admit()
  // ptr_update r v;
  // pts_to_perm full_permission r v


(** For test purposes, assume that outer is a star.
    Remove once left/right_sel are done correctly through tactics **)
assume
val frame
  (outer:viewable{VStar? outer})
  (#inner0:viewable)
  (#a:Type)
  (#inner1:a -> viewable)
  (#[resolve_frame()]
    delta:viewable{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer inner0 delta /\ True)})
  (#pre:t_of inner0 -> prop)
  (#post:t_of inner0 -> (x:a) -> t_of (inner1 x) -> prop)
  ($f:unit -> Steel a inner0 inner1 pre post)
  : Steel a
          outer
          (* Observe that we do not need to use tactics for the postresource here. *)
          (fun v -> (inner1 v) <*> delta)
          (* We should satisfy the precondition of the framed function, using only the views
              of inner0 *)
          (fun v -> pre (normal (incorrect_left_sel outer inner0 delta v)))
          (* fst v1 is here the view of inner1, snd v1 the view of delta after execution
              by definition of sel_of *)
          (fun v0 x v1 ->
            post (normal (incorrect_left_sel outer inner0 delta v0)) x (normal (fst v1)) /\
           (normal (incorrect_right_sel outer inner0 delta v0)) == normal (snd v1))

#reset-options "--max_fuel 1 --max_ifuel 0"

(** A few tests of framing and normalization. An interesting observation is that we
    do not need fuel to obtain egalities on "atomic" resources inside delta. **)

val test1 (#a:Type) (r1 r2:ref a) : Steel a
  (vptr r1 <*> vptr r2)
  (fun _ -> vptr r1 <*> vptr r2)
  (fun _ -> True)
  (fun (ov1, ov2) v (v1, v2) -> ov1 == v1 /\ v == v1 /\ ov2 == v2)

let test1 #a r1 r2 =
  frame (vptr r1 <*> vptr r2)
        (fun () -> fread r1)

val test2 (#a:Type) (r1 r2 r3:ref a) : Steel a
  (vptr r1 <*> vptr r2 <*> vptr r3)
  (fun _ -> vptr r1 <*> (vptr r2 <*> vptr r3))
  (fun _ -> True)
  (fun ov x v ->
    let ((ov1, ov2), ov3) = ov in
    let (v1, (v2, v3)) = v in
    v1 == x /\ v2 == ov2 /\ v3 == ov3)

let test2 #a r1 r2 r3 =
  frame (vptr r1 <*> vptr r2 <*> vptr r3)
        (fun () -> fread r1)

val test3 (#a:Type) (r1 r2 r3 r4:ref a) : Steel a
  (vptr r1 <*> vptr r2 <*> vptr r3 <*> vptr r4)
  (fun _ -> vptr r1 <*> (vptr r2 <*> vptr r3 <*> vptr r4))
  (fun _ -> True)
  (fun ov x v ->
    let (((ov1, ov2), ov3), ov4) = ov in
    let (v1, ((v2, v3), v4)) = v in
    v1 == x /\ v2 == ov2 /\ v3 == ov3 /\ v4 == ov4)

// Not yet working because of a mismatch on select_left: We have an equality between
// ((old ptr2, old_ptr3), old_ptr4) and (ptr_2, (ptr_3, ptr4))
let test3 #a r1 r2 r3 r4 =
  let v =
  frame (vptr r1 <*> vptr r2 <*> vptr r3 <*> vptr r4)
        // #_ #_ #_
        // #(vptr r2 <*> vptr r3 <*> vptr r4)
        (fun () -> fread r1)
  in
  assert (True) by (T.dump "test3");
  v
