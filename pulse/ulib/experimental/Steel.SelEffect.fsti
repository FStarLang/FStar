module Steel.SelEffect

open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost

(* Normalization helpers *)

irreducible let __steel_reduce__ : unit = ()

unfold
let normal (#a:Type) (x:a) =
  norm [
    delta_attr [`%__steel_reduce__];
    iota;zeta;primops]
  x

(* Definition of a selector for a given slprop *)

let selector' (a:Type0) (hp:slprop) = hmem hp -> GTot a

let sel_depends_only_on (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp) (m1:mem{disjoint m0 m1}).
    (interp_depends_only_on hp; (
    sel m0 == sel (join m0 m1)))

let sel_depends_only_on_core (#a:Type) (#hp:slprop) (sel:selector' a hp) =
  forall (m0:hmem hp). sel m0 == sel (core_mem m0)

let selector (a:Type) (hp:slprop) : Type =
  sel:selector' a hp{sel_depends_only_on sel /\ sel_depends_only_on_core sel}

/// The basis of our selector framework: Separation logic assertions enhanced with selectors
/// Note that selectors are "optional", it is always possible to use a non-informative selector,
/// such as fun _ -> () and to rely on the standard separation logic reasoning
noeq
type vprop' =
  { hp: slprop u#1;
    t:Type0;
    sel: selector t hp}

(* Lifting the star operator to an inductive type makes normalization
   and implementing some later functions easier *)
noeq
type vprop =
  | VUnit : vprop' -> vprop
  | VStar: vprop -> vprop -> vprop

[@__steel_reduce__]
let star = VStar

[@__steel_reduce__]
let rec hp_of (p:vprop) = match p with
  | VUnit p -> p.hp
  | VStar p1 p2 -> hp_of p1 `Mem.star` hp_of p2

[@__steel_reduce__]
let rec t_of (p:vprop) = match p with
  | VUnit p -> p.t
  | VStar p1 p2 -> t_of p1 * t_of p2

[@__steel_reduce__]
let rec sel_of (p:vprop) : selector (t_of p) (hp_of p) = match p with
  | VUnit p -> fun h -> p.sel h
  | VStar p1 p2 ->
     let sel1 = sel_of p1 in
     let sel2 = sel_of p2 in
     fun h -> (sel1 h, sel2 h)

type pre_t = vprop
type post_t (a:Type) = a -> vprop

val can_be_split (p q:vprop) : prop
val can_be_split_forall (#a:Type) (p q:post_t a) : prop

val can_be_split_trans (p q r:vprop)
: Lemma
  (requires p `can_be_split` q /\ q `can_be_split` r)
  (ensures p `can_be_split` r)

val can_be_split_star_l (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` p)
  [SMTPat ((p `star` q) `can_be_split` p)]

val can_be_split_star_r (p q:vprop)
: Lemma
  (ensures (p `star` q) `can_be_split` q)
  [SMTPat ((p `star` q) `can_be_split` q)]

val can_be_split_refl (p:vprop)
: Lemma (p `can_be_split` p)
[SMTPat (p `can_be_split` p)]
//
(* A restricted view of the heap,
   that only allows to access selectors of the current slprop *)

let rmem (pre:vprop) =
  FExt.restricted_g_t
  (r0:vprop{can_be_split pre r0})
  (fun r0 -> normal (t_of r0))

(* Logical pre and postconditions can only access the restricted view of the heap *)

type req_t (pre:pre_t) = rmem pre -> prop
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  rmem pre -> (x:a) -> rmem (post x) -> prop

(* focus_rmem is an additional restriction of our view of memory.
   We expose it here to be able to reduce through normalization;
   Any valid application of focus_rmem h will be reduced to the application of h *)

[@__steel_reduce__]
let unrestricted_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  = fun (r':vprop{can_be_split r0 r'}) -> can_be_split_trans r r0 r'; h r'

[@__steel_reduce__]
let focus_rmem (#r: vprop) (h: rmem r) (r0: vprop{r `can_be_split` r0}) : Tot (rmem r0)
 = FExt.on_dom_g
   (r':vprop{can_be_split r0 r'})
   (unrestricted_focus_rmem h r0)

(* Defining the Steel effect with selectors *)

val repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p = fun _ r _ -> r == x

val return (a:Type u#a) (x:a) (p:a -> vprop)
  : repr a (p x) p (return_req (p x)) (return_ens x p)

unfold
let bind_req (#a:Type) (#pre_f:vprop) (#post_f:a -> vprop)
             (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
             (req_g:(x:a -> req_t (post_f x)))
  : req_t pre_f
  = fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1)

unfold
let bind_ens (#a:Type) (#b:Type) (#pre_f:vprop) (#post_f:a -> vprop)
             (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
             (#post_g:b -> vprop) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  : ens_t pre_f b post_g
  = fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2)

val bind (a:Type)
         (b:Type)
         (pre_f:vprop)
         (post_f:a -> vprop)
         (req_f:req_t pre_f)
         (ens_f:ens_t pre_f a post_f)
         (post_g:b -> vprop)
         (req_g:(x:a -> req_t (post_f x)))
         (ens_g:(x:a -> ens_t (post_f x) b post_g))
         (f:repr a pre_f post_f req_f ens_f)
         (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
   : repr b pre_f post_g
          (bind_req req_f ens_f req_g)
          (bind_ens req_f ens_f ens_g)

unfold
let subcomp_pre (#a:Type)
                (#pre:vprop)
                (#post:a -> vprop)
                (req_f:req_t pre)
                (ens_f:ens_t pre a post)
                (req_g:req_t pre)
                (ens_g:ens_t pre a post)
   : pure_pre
   = (forall h. req_g h ==> req_f h) /\
     (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1)

val subcomp (a:Type)
            (pre:vprop)
            (post:a -> vprop)
            (req_f:req_t pre)
            (ens_f:ens_t pre a post)
            (req_g:req_t pre)
            (ens_g:ens_t pre a post)
            (f:repr a pre post req_f ens_f)
  : Pure (repr a pre post req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
         (ensures fun _ -> True)

[@@ allow_informative_binders]
reifiable reflectable
layered_effect {
  SteelSel : a:Type
        -> pre:pre_t
        -> post:post_t a
        -> req:req_t pre
        -> ens:ens_t pre a post
        -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp
}

(* Defining a bind with pure functions *)

unfold
let bind_pure_steel_req (#a:Type)
                        (wp:pure_wp a)
                        (#pre_g:vprop)
                        (req_g:a -> req_t pre_g)
  : req_t pre_g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True)

unfold
let bind_pure_steel_ens (#a:Type)
                        (#b:Type)
                        (wp:pure_wp a)
                        (#pre_g:vprop)
                        (#post_g:b -> vprop)
                        (ens_g:a -> ens_t pre_g b post_g)
   : ens_t pre_g b post_g
   = fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1)

val bind_pure_steel (a:Type)
                    (b:Type)
                    (wp:pure_wp a)
                    (pre_g:vprop)
                    (post_g:b -> vprop)
                    (req_g:a -> req_t pre_g)
                    (ens_g:a -> ens_t pre_g b post_g)
                    (f:eqtype_as_type unit -> PURE a wp)
                    (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
  : repr b pre_g post_g
         (bind_pure_steel_req wp req_g)
         (bind_pure_steel_ens wp ens_g)

polymonadic_bind (PURE, SteelSel) |> SteelSel = bind_pure_steel

(* State that all "atomic" subresources have the same selectors on both views *)

[@__steel_reduce__]
let rec frame_equalities
  (frame:vprop)
  (h0:rmem frame) (h1:rmem frame) : prop
  = match frame with
    | VUnit p ->
        h0 frame == h1 frame
    | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h01 = focus_rmem h0 p1 in
        let h11 = focus_rmem h1 p1 in

        let h02 = focus_rmem h0 p2 in
        let h12 = focus_rmem h1 p2 in


        frame_equalities p1 h01 h11 /\
        frame_equalities p2 h02 h12

(* Some helper functions *)

val returnc (#a:Type) (#p:a -> vprop) (x:a)
  : SteelSel a (p x) p (fun _ -> True) (fun h0 r h1 -> r == x /\ normal (frame_equalities (p x) h0 h1))

val get (#p:vprop) (_:unit) : SteelSel (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

val change_slprop (p q:vprop) (vp:erased (t_of p)) (vq:erased (t_of q))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSel unit p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)

val frame (#a:Type)
          (#pre:pre_t)
          (#post:post_t a)
          (#req:req_t pre)
          (#ens:ens_t pre a post)
          ($f:unit -> SteelSel a pre post req ens)
          (frame:vprop)
  : SteelSel a
    (pre `star` frame)
    (fun x -> post x `star` frame)
    (fun h -> normal (req (focus_rmem h pre)))
    (fun h0 r h1 -> normal (
      req (focus_rmem h0 pre) /\
      ens (focus_rmem h0 pre) r (focus_rmem h1 (post r))
      /\ frame_equalities frame (focus_rmem h0 frame) (focus_rmem h1 frame)))

(* Empty assertion *)
val vemp :vprop

(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

val ref (a:Type0) : Type0
val ptr (#a:Type0) (r:ref a) : slprop u#1
val ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r)

[@__steel_reduce__]
let vptr' #a r : vprop' =
  {hp = ptr r;
   t = a;
   sel = ptr_sel r}
[@__steel_reduce__]
let vptr r = VUnit (vptr' r)

val alloc (#a:Type0) (x:a) : SteelSel (ref a)
  vemp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x)

val read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))

val write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))

(* Should do this in a more princpled way once we have automated framing *)

val rewrite_2 (p q:vprop) : SteelSel unit
  (p `star` q) (fun _ -> q `star` p)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    h0 p == h1 p /\
    h0 q == h1 q)

(* AF: Ultimately, the precondition should probably be a squashed implicit that can be resolved by tactic *)
unfold
let sel (#a:Type) (#p:vprop) (h:rmem p) (r:ref a)
  : Ghost a (requires can_be_split p (vptr r)) (ensures fun _ -> True)
  = h (vptr r)

(* Some tests *)



let test (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel h1 r == 0)
  = write r 1;
    write r 0

let test2 (r1 r2:ref int) : SteelSel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> sel h1 r1 == 0 /\ sel h0 r2 == sel h1 r2)
  = frame (fun _ -> write r1 1) (vptr r2);
    frame (fun _ -> write r1 0) (vptr r2)

// AF: Should work with r3 if we specify the additional can_be_split
let test3 (r1 r2 r3:ref int) : SteelSel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ ->
    can_be_split (vptr r1 `star` vptr r2 `star` vptr r3) (vptr r1) /\
    can_be_split (vptr r1 `star` (vptr r2 `star` vptr r3)) (vptr r2))
  (ensures fun h0 _ h1 ->
    can_be_split (vptr r1 `star` vptr r2 `star` vptr r3) (vptr r1) /\
    can_be_split (vptr r1 `star` (vptr r2 `star` vptr r3)) (vptr r2) /\
    sel h1 r1 == 0 /\
    sel h0 r2 == sel h1 r2
  )
  = let h0 = get () in
    frame (fun _ -> write r1 1) (vptr r2 `star` vptr r3);
    let h1 = get() in
    assert (sel h1 r1 == 1);
    assert (sel h0 r2 == sel h1 r2);
    frame (fun _ -> write r1 0) (vptr r2 `star` vptr r3)


let swap (#a:Type0) (r1 r2:ref a) : SteelSel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel h0 r1 == sel h1 r2 /\
    sel h0 r2 == sel h1 r1)
  = let x1 = frame (fun _ -> read r1) (vptr r2) in
    rewrite_2 (vptr r1) (vptr r2);
    let x2 = frame (fun _ -> read r2) (vptr r1) in
    frame (fun _ -> write r2 x1) (vptr r1);
    rewrite_2 (vptr r2) (vptr r1);
    frame (fun _ -> write r1 x2) (vptr r2)
