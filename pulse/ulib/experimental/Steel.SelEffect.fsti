module Steel.SelEffect

open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost
include Steel.SelEffect.Common

#set-options "--warn_error -330"  //turn off the experimental feature warning

(* focus_rmem is an additional restriction of our view of memory.
   We expose it here to be able to reduce through normalization;
   Any valid application of focus_rmem h will be reduced to the application of h *)

[@@ __steel_reduce__]
unfold
let unrestricted_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  = fun (r':vprop{can_be_split r0 r'}) -> can_be_split_trans r r0 r'; h r'

[@@ __steel_reduce__]
let focus_rmem (#r: vprop) (h: rmem r) (r0: vprop{r `can_be_split` r0}) : Tot (rmem r0)
 = FExt.on_dom_g
   (r':vprop{can_be_split r0 r'})
   (unrestricted_focus_rmem h r0)

(* State that all "atomic" subresources have the same selectors on both views *)

(* AF 04/27/2021: The linear equality generation, where equalities are only
   generated for leaf, VUnit nodes, works well for concrete code, but does
   not allow to propagate information when handling abstract vprops.
   While defining generic combinators on vprops such as vrefine and vdep,
   Tahina encountered issues with this. For instance, elim_vdep returns
   a v `star` q, where v and q are abstract vprops. As such, equalities
   on the selectors of v and q are not propagated: Normalization gets stuck
   on both v and q, since they are neither a VUnit nor a VStar.
   An earlier fix was creating a "top-level" equality on the full vprop
   to handle most generic vprops cases. Unfortunately, this does not
   help when we have atomic, abstract vprops as in v `star` q.
   For now, I'm reenabling quadratic equality generation. But we need
   to find a better way to handle generic vprops selectors while avoiding
   a context blowup; furthermore, equalities on composite resources are mostly
   irrelevant because of AC-rewriting, and because we do not provide patterns
   on lemmas relating sel (p * q) with (sel p, sel q), or sel (p * q) with
   sel (q * p) for instance.
   We should instead have a better way to define atomic vprops, which encapsulates
   atomic, abstract vprops
*)
[@@ __steel_reduce__]
let rec frame_equalities
  (frame:vprop)
  (h0:rmem frame) (h1:rmem frame) : prop
  = h0 frame == h1 frame /\
    begin match frame with
    | VUnit p -> True
    | VStar p1 p2 ->
        can_be_split_star_l p1 p2;
        can_be_split_star_r p1 p2;

        let h01 = focus_rmem h0 p1 in
        let h11 = focus_rmem h1 p1 in

        let h02 = focus_rmem h0 p2 in
        let h12 = focus_rmem h1 p2 in


        frame_equalities p1 h01 h11 /\
        frame_equalities p2 h02 h12
    end

(* Defining the Steel effect with selectors *)

val repr (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p =
  fun h0 r h1 -> normal (r == x /\ frame_equalities (p x) h0 h1)

(*
 * Return is parametric in post (cf. return-scoping.txt)
 *)
val return (a:Type) (x:a) (#[@@@ framing_implicit] p:a -> vprop)
: repr a true (return_pre (p x)) p (return_req (p x)) (return_ens a x p)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (#pr:a -> prop)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (forall (x:a) (m1:rmem (post_f x `star` frame_f)).
    (ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
      frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f))
    ==> pr x /\
      (can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
      (req_g x) (focus_rmem m1 (pre_g x)))))

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (#pr:a -> prop)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall_dep pr (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (exists (x:a) (m1:rmem (post_f x `star` frame_f)).
    pr x /\
    (
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);
    frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f) /\
    frame_equalities (frame_g x) (focus_rmem m1 (frame_g x)) (focus_rmem m2 (frame_g x)) /\
    ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
    (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y)))))

val bind (a:Type) (b:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:a -> post_t b)
  (#[@@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@@ framing_implicit] frame_f:vprop) (#[@@@ framing_implicit] frame_g:a -> vprop)
  (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] _ : squash (maybe_emp framed_f frame_f))
  (#[@@@ framing_implicit] _ : squash (maybe_emp_dep framed_g frame_g))
  (#[@@@ framing_implicit] pr:a -> prop)
  (#[@@@ framing_implicit] p1:squash (can_be_split_forall_dep pr
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a framed_f pre_f post_f req_f ens_f)
  (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    true
    (pre_f `star` frame_f)
    post
    (bind_req req_f ens_f req_g frame_f frame_g p1)
    (bind_ens req_f ens_f ens_g frame_f frame_g post p1 p2)



unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (equiv_forall post_f post_g))
: pure_pre
= (forall (m0:rmem pre_g). normal (req_g m0 ==> req_f (focus_rmem m0 pre_f))) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_g x)). normal (
      ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> ens_g m0 x m1
    )
  )


val subcomp (a:Type)
  (#framed_f:eqtype_as_type bool)
  (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] req_f:req_t pre_f) (#[@@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_g:req_t pre_g) (#[@@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (equiv_forall post_f post_g))
  (f:repr a framed_f pre_f post_f req_f ens_f)
: Pure (repr a framed_g pre_g post_g req_g ens_g)
  (requires (subcomp_pre req_f ens_f req_g ens_g p1 p2))
  (ensures fun _ -> True)

unfold
let if_then_else_req
  (#pre_f:pre_t) (#pre_g:pre_t)
  (s: squash (can_be_split pre_f pre_g))
  (req_then:req_t pre_f) (req_else:req_t pre_g)
  (p:Type0)
: req_t pre_f
= fun h -> normal (
    (p ==> req_then h) /\
    ((~ p) ==> req_else (focus_rmem h pre_g))
  )

unfold
let if_then_else_ens (#a:Type)
  (#pre_f:pre_t) (#pre_g:pre_t) (#post_f:post_t a) (#post_g:post_t a)
  (s1 : squash (can_be_split pre_f pre_g))
  (s2 : squash (equiv_forall post_f post_g))
  (ens_then:ens_t pre_f a post_f) (ens_else:ens_t pre_g a post_g)
  (p:Type0)
: ens_t pre_f a post_f
= fun h0 x h1 -> normal (
    (p ==> ens_then (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x))) /\
    ((~ p) ==> ens_else (focus_rmem h0 pre_g) x (focus_rmem h1 (post_g x)))
  )

let if_then_else (a:Type)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] pre_g:pre_t)
  (#[@@@ framing_implicit] post_f:post_t a) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] req_then:req_t pre_f) (#[@@@ framing_implicit] ens_then:ens_t pre_f a post_f)
  (#[@@@ framing_implicit] req_else:req_t pre_g) (#[@@@ framing_implicit] ens_else:ens_t pre_g a post_g)
  (#[@@@ framing_implicit] s_pre: squash (can_be_split pre_f pre_g))
  (#[@@@ framing_implicit] s_post: squash (equiv_forall post_f post_g))
  (f:repr a framed pre_f post_f req_then ens_then)
  (g:repr a framed pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a framed pre_f post_f
    (if_then_else_req s_pre req_then req_else p)
    (if_then_else_ens s_pre s_post ens_then ens_else p)

reflectable
effect {
  SteelSelBase
    (a:Type) (framed:bool) (pre:pre_t) (post:post_t a) (_:req_t pre) (_:ens_t pre a post)
  with { repr; return; bind; subcomp; if_then_else }
}


effect SteelSel (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelSelBase a false pre post req ens
effect SteelSelF (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  SteelSelBase a true pre post req ens

(*
//  * PURE, Steel(F) bind
//  *)

unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> normal ((wp (fun x -> (req x) m) /\ as_requires wp))

unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> normal ((as_requires wp /\ (exists (x:a). as_ensures wp x /\ ((ens x) m0 r m1))))

val bind_pure_steel_ (a:Type) (b:Type)
  (#[@@@ framing_implicit] wp:pure_wp a)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t b)
  (#[@@@ framing_implicit] req:a -> req_t pre) (#[@@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b framed pre post (req x) (ens x)))
: repr b
    framed
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

polymonadic_bind (PURE, SteelSelBase) |> SteelSelBase = bind_pure_steel_

(*
//  * Annotations without the req and ens
//  *)

effect SteelSelT (a:Type) (pre:pre_t) (post:post_t a) =
  SteelSel a pre post (fun _ -> True) (fun _ _ _ -> True)

(* Some helper functions *)

val noop (_:unit)
  : SteelSel unit vemp (fun _ -> vemp) (requires fun _ -> True) (ensures fun _ _ _ -> True)

val get (#p:vprop) (_:unit) : SteelSelF (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

let gget (p: vprop) : SteelSel (Ghost.erased (t_of p))
  p (fun _ -> p)
  (requires (fun _ -> True))
  (ensures (fun h0 res h1 ->
    h1 p == h0 p /\
    Ghost.reveal res == h0 p /\
    Ghost.reveal res == h1 p
  ))
=
  let m = get #p () in
  Ghost.hide (m p)

val change_slprop (p q:vprop) (vp:erased (normal (t_of p))) (vq:erased (normal (t_of q)))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSel unit p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)

val change_equal_slprop (p q: vprop)
  : SteelSel unit p (fun _ -> q) (fun _ -> p == q) (fun h0 _ h1 -> p == q /\ h1 q == h0 p)

val change_slprop_2 (p q:vprop) (vq:erased (t_of q))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSel unit p (fun _ -> q) (fun _ -> True) (fun _ _ h1 -> h1 q == reveal vq)

val change_slprop_rel (p q:vprop)
  (rel : normal (t_of p) -> normal (t_of q) -> prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m)
    (ensures interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : SteelSel unit p (fun _ -> q) (fun _ -> True) (fun h0 _ h1 -> rel (h0 p) (h1 q))

val change_slprop_rel_with_cond (p q:vprop)
  (cond:  (t_of p) -> prop)
  (rel :  (t_of p) ->  (t_of q) -> prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ cond (sel_of p m))
    (ensures interp (hp_of q) m /\
      rel (sel_of p m) (sel_of q m))
  ) : SteelSel unit p (fun _ -> q) (fun h0 -> cond (h0 p)) (fun h0 _ h1 -> rel (h0 p) (h1 q))

val extract_info (p:vprop) (vp:erased (normal (t_of p))) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures fact)
  ) : SteelSel unit p (fun _ -> p)
      (fun h -> h p == reveal vp)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)

val sladmit (#a:Type)
            (#p:pre_t)
            (#q:post_t a)
            (_:unit)
  : SteelSelF a p q (requires fun _ -> True) (ensures fun _ _ _ -> False)

val reveal_star (p1 p2:vprop)
 : SteelSel unit (p1 `star` p2) (fun _ -> p1 `star` p2)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     h0 p1 == h1 p1 /\
     h0 p2 == h1 p2 /\
     h0 (p1 `star` p2) == (h0 p1, h0 p2) /\
     h1 (p1 `star` p2) == (h1 p1, h1 p2)
   )

val reveal_star_3 (p1 p2 p3:vprop)
 : SteelSel unit (p1 `star` p2 `star` p3) (fun _ -> p1 `star` p2 `star` p3)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     can_be_split (p1 `star` p2 `star` p3) p1 /\
     can_be_split (p1 `star` p2 `star` p3) p2 /\
     h0 p1 == h1 p1 /\ h0 p2 == h1 p2 /\ h0 p3 == h1 p3 /\
     h0 (p1 `star` p2 `star` p3) == ((h0 p1, h0 p2), h0 p3) /\
     h1 (p1 `star` p2 `star` p3) == ((h1 p1, h1 p2), h1 p3)
   )


(* Simple Reference library, only full permissions.
   AF: Permissions would likely need to be an index of the vprop ptr.
   It cannot be part of a selector, as it is not invariant when joining with a disjoint memory
   Using the value of the ref as a selector is ok because refs with fractional permissions
   all share the same value.
   Refs on PCM are more complicated, and likely not usable with selectors
*)

module R = Steel.Reference
open Steel.FractionalPermission

let ref (a:Type0) : Type0 = R.ref a
let ptr (#a:Type0) (r:ref a) : slprop u#1 = h_exists (R.pts_to r full_perm)

val ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r)

val ptr_sel_interp (#a:Type0) (r:ref a) (m:mem) : Lemma
  (requires interp (ptr r) m)
  (ensures interp (R.pts_to r full_perm (ptr_sel r m)) m)

[@@ __steel_reduce__]
let vptr' #a r : vprop' =
  {hp = ptr r;
   t = a;
   sel = ptr_sel r}

[@@ __steel_reduce__]
unfold
let vptr r = VUnit (vptr' r)

val alloc (#a:Type0) (x:a) : SteelSel (ref a)
  vemp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> h1 (vptr r) == x /\ not (R.is_null r))

val free (#a:Type0) (r:ref a) : SteelSel unit
  (vptr r) (fun _ -> vemp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

val read (#a:Type0) (r:ref a) : SteelSel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptr r) == h1 (vptr r) /\ x == h1 (vptr r))

val write (#a:Type0) (r:ref a) (x:a) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == h1 (vptr r))

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
  = h (vptr r)

val vptr_not_null
  (#a: Type)
  (r: ref a)
: SteelSel unit
    (vptr r)
    (fun _ -> vptr r)
    (fun _ -> True)
    (fun h0 _ h1 ->
      h1 (vptr r) == h0 (vptr r) /\
      R.is_null r == false
    )

(* Introduction and elimination principles for vprop combinators *)

val intro_vrefine
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelSel unit v (fun _ -> vrefine v p)
  (requires (fun h -> p (h v)))
  (ensures (fun h _ h' -> normal (h' (vrefine v p) == h v)))

val elim_vrefine
  (v: vprop) (p: (normal (t_of v) -> Tot prop))
: SteelSel unit (vrefine v p) (fun _ -> v)
  (requires (fun _ -> True))
  (ensures (fun h _ h' -> normal (h' v == h (vrefine v p))))

val intro_vdep
  (v: vprop)
  (q: vprop)
  (p: (t_of v -> Tot vprop))
: SteelSel unit
    (v `star` q)
    (fun _ -> vdep v p)
    (requires (fun h -> q == p (h v)))
    (ensures (fun h _ h' ->
      let x2 = h' (vdep v p) in
      q == p (h v) /\
      dfst x2 == (h v) /\
      dsnd x2 == (h q)
    ))

val elim_vdep
  (v: vprop)
  (p: (t_of v -> Tot vprop))
: SteelSel (Ghost.erased (t_of v))
  (vdep v p)
  (fun res -> v `star` p (Ghost.reveal res))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
      let fs = h' v in
      let sn : t_of (p (Ghost.reveal res)) = h' (p (Ghost.reveal res)) in
      let x2 = h (vdep v p) in
      Ghost.reveal res == fs /\
      dfst x2 == fs /\
      dsnd x2 == sn
  ))

val intro_vrewrite
  (v: vprop) (#t: Type) (f: (normal (t_of v) -> GTot t))
: SteelSel unit v (fun _ -> vrewrite v f) (fun _ -> True) (fun h _ h' -> h' (vrewrite v f) == f (h v))

val elim_vrewrite
  (v: vprop)
  (#t: Type)
  (f: (normal (t_of v) -> GTot t))
: SteelSel unit (vrewrite v f) (fun _ -> v)
    (fun _ -> True)
    (fun h _ h' -> h (vrewrite v f) == f (h' v))
