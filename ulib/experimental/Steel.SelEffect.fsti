module Steel.SelEffect

open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost
include Steel.SelEffect.Common


(* focus_rmem is an additional restriction of our view of memory.
   We expose it here to be able to reduce through normalization;
   Any valid application of focus_rmem h will be reduced to the application of h *)

[@__steel_reduce__]
unfold
let unrestricted_focus_rmem (#r:vprop) (h:rmem r) (r0:vprop{r `can_be_split` r0})
  = fun (r':vprop{can_be_split r0 r'}) -> can_be_split_trans r r0 r'; h r'

[@__steel_reduce__]
let focus_rmem (#r: vprop) (h: rmem r) (r0: vprop{r `can_be_split` r0}) : Tot (rmem r0)
 = FExt.on_dom_g
   (r':vprop{can_be_split r0 r'})
   (unrestricted_focus_rmem h r0)

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


(* Defining the Steel effect with selectors *)

val repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) : Type u#2

unfold
let return_req (p:vprop) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> vprop) : ens_t (p x) a p =
  fun h0 r h1 -> normal (r == x /\ frame_equalities (p x) h0 h1)

(*
 * Return is parametric in post (cf. return-scoping.txt)
 *)
val return (a:Type) (x:a) (#[@@ framing_implicit] p:a -> vprop)
: repr a (return_pre (p x)) (return_post p) (return_req (p x)) (return_ens a x p)

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (_:squash (can_be_split_forall post_f pre_g))
: req_t pre_f
= fun m0 -> normal (
  req_f m0 /\
  (forall (x:a) (m1:rmem (post_f x)). ens_f m0 x m1 ==> (req_g x) (focus_rmem m1 (pre_g x))))

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (post:post_t b)
  (_:squash (can_be_split_forall post_f pre_g))
  (_:squash (can_be_split_post post_g post))
: ens_t pre_f b post
= fun m0 y m2 -> normal (
  req_f m0 /\
  (exists (x:a) (m1:rmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y))))

val bind (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p1:squash (can_be_split_forall post_f pre_g))
  (#[@@ framing_implicit] p2:squash (can_be_split_post post_g post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    pre_f
    post
    (bind_req req_f ens_f req_g p1)
    (bind_ens req_f ens_f ens_g post p1 p2)

unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (can_be_split pre_g pre_f))
  (_:squash (equiv_forall post_f post_g))
: pure_pre
= normal ((forall (m0:rmem pre_g). req_g m0 ==> req_f (focus_rmem m0 pre_f)) /\
  (forall (m0:rmem pre_g) (x:a) (m1:rmem (post_g x)). ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) ==> ens_g m0 x m1))

val subcomp (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] req_g:req_t pre_g) (#[@@ framing_implicit] ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@ framing_implicit] p2:squash (equiv_forall post_f post_g))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires (subcomp_pre req_f ens_f req_g ens_g p1 p2))
  (ensures fun _ -> True)

unfold
let if_then_else_req
  (#pre_f:pre_t) (#pre_g:pre_t)
  (s: squash (can_be_split pre_f pre_g))
  (req_then:req_t pre_f) (req_else:req_t pre_g)
  (p:Type0)
: req_t pre_f
= fun h -> normal ((p ==> req_then h) /\ ((~ p) ==> req_else (focus_rmem h pre_g)))

unfold
let if_then_else_ens (#a:Type)
  (#pre_f:pre_t) (#pre_g:pre_t) (#post_f:post_t a) (#post_g:post_t a)
  (s1 : squash (can_be_split pre_f pre_g))
  (s2 : squash (equiv_forall post_f post_g))
  (ens_then:ens_t pre_f a post_f) (ens_else:ens_t pre_g a post_g)
  (p:Type0)
: ens_t pre_f a post_f
= fun h0 x h1 -> normal ((p ==> ens_then (focus_rmem h0 pre_f) x (focus_rmem h1 (post_f x))) /\
  ((~ p) ==> ens_else (focus_rmem h0 pre_g) x (focus_rmem h1 (post_g x))))

let if_then_else (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] pre_g:pre_t)
  (#[@@ framing_implicit] post_f:post_t a) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] req_then:req_t pre_f) (#[@@ framing_implicit] ens_then:ens_t pre_f a post_f)
  (#[@@ framing_implicit] req_else:req_t pre_g) (#[@@ framing_implicit] ens_else:ens_t pre_g a post_g)
  (#[@@ framing_implicit] s_pre: squash (can_be_split pre_f pre_g))
  (#[@@ framing_implicit] s_post: squash (equiv_forall post_f post_g))
  (f:repr a pre_f post_f req_then ens_then)
  (g:repr a pre_g post_g req_else ens_else)
  (p:bool)
: Type
= repr a pre_f post_f
    (if_then_else_req s_pre req_then req_else p)
    (if_then_else_ens s_pre s_post ens_then ens_else p)

[@@allow_informative_binders]
reifiable reflectable
layered_effect {
  SteelSelF: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
}

[@@allow_informative_binders]
reifiable reflectable
new_effect SteelSel = SteelSelF


(*
 * Onto polymonadic binds
 *)

(*
 * First the bind between two unframed computations
 *
 * Add a frame to each
 *)

unfold
let bind_steel_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
: req_t (pre_f `star` frame_f)
= fun m0 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (forall (x:a) (m1:rmem (post_f x `star` frame_f)). (
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    (ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
      frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f))
    ==>
      (req_g x) (focus_rmem m1 (pre_g x)))))

unfold
let bind_steel_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop) (frame_g:a -> vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (exists (x:a) (m1:rmem (post_f x `star` frame_f)). (
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x `star` frame_f) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);
    frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f) /\
    frame_equalities (frame_g x) (focus_rmem m1 (frame_g x)) (focus_rmem m2 (frame_g x)) /\
    ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\
    (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y)))))

val bind_steel_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:vprop) (#[@@ framing_implicit] frame_g:a -> vprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post
    (bind_steel_steel_req req_f ens_f req_g frame_f frame_g p)
    (bind_steel_steel_ens req_f ens_f ens_g frame_f frame_g post p p2)

(*
 * Note that the output is a framed computation, hence SteelF
 *)

polymonadic_bind (SteelSel, SteelSel) |> SteelSelF = bind_steel_steel


(*
 * Steel, SteelF: frame the first computation
 *)

unfold
let bind_steel_steelf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:vprop)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
: req_t (pre_f `star` frame_f)
= fun m0 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (forall (x:a) (m1:rmem (post_f x `star` frame_f)).
    (ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\ frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f)) ==>
      (req_g x) (focus_rmem m1 (pre_g x))))

unfold
let bind_steel_steelf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_f:vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (_: squash (can_be_split_post post_g post))
: ens_t (pre_f `star` frame_f) b post
= fun m0 y m2 -> normal (
  req_f (focus_rmem m0 pre_f) /\
  (exists (x:a) (m1:rmem (post_f x `star` frame_f)). (
    frame_equalities frame_f (focus_rmem m0 frame_f) (focus_rmem m1 frame_f)) /\
    ens_f (focus_rmem m0 pre_f) x (focus_rmem m1 (post_f x)) /\ (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y))))

val bind_steel_steelf (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_f:vprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (#[@@ framing_implicit] p2: squash (can_be_split_post post_g post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post
    (bind_steel_steelf_req req_f ens_f req_g frame_f p)
    (bind_steel_steelf_ens req_f ens_f ens_g frame_f post p p2)

polymonadic_bind (SteelSel, SteelSelF) |> SteelSelF = bind_steel_steelf


(*
 * SteelF, Steel: frame the second computation
 *)

unfold
let bind_steelf_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_g:a -> vprop)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
: req_t pre_f
= fun m0 -> normal (
  req_f m0 /\
  (forall (x:a) (m1:rmem (post_f x)). (
    can_be_split_trans (post_f x) (pre_g x `star` frame_g x) (pre_g x);
    ens_f m0 x m1 ==> (req_g x) (focus_rmem m1 (pre_g x)))))

unfold
let bind_steelf_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:a -> pre_t) (#post_g:a -> post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (frame_g:a -> vprop)
  (post:post_t b)
  (_:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (_:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
: ens_t pre_f b post
= fun m0 y m2 -> normal (
  req_f m0 /\
  (exists (x:a) (m1:rmem (post_f x)). (
    can_be_split_trans (post_f x) (pre_g x `star` frame_g x) (pre_g x);
    can_be_split_trans (post_f x) (pre_g x `star` frame_g x) (frame_g x);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (post_g x y);
    can_be_split_trans (post y) (post_g x y `star` frame_g x) (frame_g x);
    frame_equalities (frame_g x) (focus_rmem m1 (frame_g x)) (focus_rmem m2 (frame_g x)) /\
    ens_f m0 x m1 /\ (ens_g x) (focus_rmem m1 (pre_g x)) y (focus_rmem m2 (post_g x y)))))

val bind_steelf_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] req_f:req_t pre_f) (#[@@ framing_implicit] ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:a -> post_t b)
  (#[@@ framing_implicit] req_g:(x:a -> req_t (pre_g x))) (#[@@ framing_implicit] ens_g:(x:a -> ens_t (pre_g x) b (post_g x)))
  (#[@@ framing_implicit] frame_g:a -> vprop)
  (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g x)))
  (#[@@ framing_implicit] p2:squash (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) (post_g x) (req_g x) (ens_g x)))
: repr b
    pre_f
    post
    (bind_steelf_steel_req req_f ens_f req_g frame_g p)
    (bind_steelf_steel_ens req_f ens_f ens_g frame_g post p p2)


polymonadic_bind (SteelSelF, SteelSel) |> SteelSelF = bind_steelf_steel

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
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (#[@@ framing_implicit] req:a -> req_t pre) (#[@@ framing_implicit] ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)

polymonadic_bind (PURE, SteelSel) |> SteelSel = bind_pure_steel_
polymonadic_bind (PURE, SteelSelF) |> SteelSelF = bind_pure_steel_

(*
//  * subcomp relation from SteelF to Steel
//  *)

polymonadic_subcomp SteelSelF <: SteelSel = subcomp


(* Some helper functions *)

val get (#[@@framing_implicit] p:vprop) (_:unit) : SteelSelF (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

val change_slprop (p q:vprop) (vp:erased (normal (t_of p))) (vq:erased (normal (t_of q)))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSel unit p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)

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

val extract_info (p:vprop) (vp:erased (normal (t_of p))) (fact:prop)
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures fact)
  ) : SteelSel unit p (fun _ -> p)
      (fun h -> h p == reveal vp)
      (fun h0 _ h1 -> normal (frame_equalities p h0 h1) /\ fact)


val reveal_star (p1 p2:vprop)
 : SteelSel unit (p1 `star` p2) (fun _ -> p1 `star` p2)
   (requires fun _ -> True)
   (ensures fun h0 _ h1 ->
     h0 (p1 `star` p2) == (h1 p1, h1 p2) /\
     h1 (p1 `star` p2) == (h0 p1, h0 p2)
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
  (ensures fun _ r h1 -> h1 (vptr r) == x)

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

(* Some tests *)

#push-options "--fuel 0 --ifuel 0"

// #set-options "--admit_smt_queries true"

let test0 (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun h -> sel r h == 0)
  (ensures fun _ _ h1 -> sel r h1 == 1)
  = let h = get () in
    assert (sel r h == 0);
    write r 1;
    let h1 = get() in
    assert (sel r h1 == 1);
    write r 1

let test1 (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel r h1 == 0)
  = write r 1;
    write r 0;
    ()

let test2 (r1 r2:ref int) : SteelSel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun h -> sel r1 h == 1)
  (ensures fun h0 _ h1 -> sel r1 h1 == 0 /\ sel r2 h0 == sel r2 h1)
  = write r1 0;
    write r1 0

let test3 (r1 r2 r3:ref int) : SteelSel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h1 == 0 /\
    sel r2 h0 == sel r2 h1 /\
    sel r3 h0 == sel r3 h1
  )
  = let h0 = get () in
    write r1 1;
    let h1 = get() in
    assert (sel r1 h1 == 1);
    assert (sel r2 h0 == sel r2 h1);
    write r1 0


let swap (#a:Type0) (r1 r2:ref a) : SteelSel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h0 == sel r2 h1 /\
    sel r2 h0 == sel r1 h1)
  = let x1 = read r1 in
    let x2 = read r2 in
    write r2 x1;
    write r1 x2
