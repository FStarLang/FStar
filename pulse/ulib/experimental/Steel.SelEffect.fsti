module Steel.SelEffect

open Steel.Memory
module Mem = Steel.Memory
module FExt = FStar.FunctionalExtensionality
open FStar.Ghost

(* Normalization helpers *)

irreducible let framing_implicit : unit = ()
irreducible let __steel_reduce__ : unit = ()
irreducible let __reduce__ : unit = ()

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
[@@__steel_reduce__]
noeq
type vprop =
  | VUnit : vprop' -> vprop
  | VStar: vprop -> vprop -> vprop

unfold
let normal (#a:Type) (x:a) =
  norm [
    delta_attr [`%__steel_reduce__];
    delta_only [`%Mkvprop'?.t; `%Mkvprop'?.hp; `%Mkvprop'?.sel];
    delta_qualifier ["unfold"];
    iota;zeta;primops]
  x


[@@ __steel_reduce__; __reduce__]
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

let return_pre (p:vprop) : vprop = p
let return_post (#a:Type) (p:post_t a) : post_t a = p


val can_be_split (p q:vprop) : Type0
let can_be_split_forall (#a:Type) (p q:post_t a) = forall x. can_be_split (p x) (q x)

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

let equiv_forall (#a:Type) (t1 t2:post_t a) : Type0
  = t1 `can_be_split_forall` t2 /\ t2 `can_be_split_forall` t1

// val equiv_forall_split (#a:Type) (t1 t2:post_t a)
//   : Lemma (requires t1 `equiv_forall` t2)
//           (ensures can_be_split_forall t1 t2 /\ can_be_split_forall t2 t1)
//           [SMTPat (t1 `equiv_forall` t2)]

let can_be_split_post (#a #b:Type) (t1:a -> post_t b) (t2:post_t b) =
  forall (x:a). equiv_forall (t1 x) t2

val equiv (p q:vprop) : prop

let rmem (pre:vprop) =
  FExt.restricted_g_t
  (r0:vprop{can_be_split pre r0})
  (fun r0 -> normal (t_of r0))

(* Logical pre and postconditions can only access the restricted view of the heap *)

type req_t (pre:pre_t) = rmem pre -> Type0
type ens_t (pre:pre_t) (a:Type) (post:post_t a) =
  rmem pre -> (x:a) -> rmem (post x) -> Type0

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

[@@__steel_reduce__]
unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> (wp (fun x -> (req x) m) /\ as_requires wp)

[@@__steel_reduce__]
unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> (as_requires wp /\ (exists (x:a). as_ensures wp x /\ ((ens x) m0 r m1)))

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

(* Framing Tactic *)

val equiv_can_be_split (p1 p2:vprop) : Lemma
  (requires p1 `equiv` p2)
  (ensures p1 `can_be_split` p2)

val intro_can_be_split_frame (p q:vprop) (frame:vprop)
  : Lemma (requires q `equiv` (p `star` frame))
          (ensures can_be_split q p /\ True)

val can_be_split_post_elim (#a #b:Type) (t1:a -> post_t b) (t2:post_t b)
  : Lemma (requires (forall (x:a) (y:b). t1 x y `equiv` t2 y))
          (ensures t1 `can_be_split_post` t2)

val equiv_forall_elim (#a:Type) (t1 t2:post_t a)
  : Lemma (requires (forall (x:a). t1 x `equiv` t2 x))
          (ensures t1 `equiv_forall` t2)


(* Empty assertion *)
val vemp :vprop

open FStar.Tactics

open FStar.Tactics.CanonCommMonoidSimple.Equiv

val equiv_refl (x:vprop) : Lemma (equiv x x)

val equiv_sym (x y:vprop) : Lemma
  (requires equiv x y)
  (ensures equiv y x)

val equiv_trans (x y z:vprop) : Lemma
  (requires equiv x y /\ equiv y z)
  (ensures equiv x z)

module CE = FStar.Algebra.CommMonoid.Equiv

inline_for_extraction noextract let req : CE.equiv vprop =
  CE.EQ equiv
     equiv_refl
     equiv_sym
     equiv_trans

val cm_identity (x:vprop) : Lemma ((vemp `star` x) `equiv` x)

val star_commutative (p1 p2:vprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:vprop)
  : Lemma (((p1 `star` p2) `star` p3)
           `equiv`
           (p1 `star` (p2 `star` p3)))

val star_congruence (p1 p2 p3 p4:vprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))


inline_for_extraction noextract let rm : CE.cm vprop req =
  CE.CM vemp
     star
     cm_identity
     star_associative
     star_commutative
     star_congruence

(* Specialize visit_tm to reimplement name_appears_in.
   AF: As of Jan 14, 2021, calling name_appears_in from FStar.Tactics.Derived leads to a segfault *)

exception Appears

let on_sort_bv (f : term -> Tac unit) (xbv:bv) : Tac unit =
  f (inspect_bv xbv).bv_sort

let on_sort_binder (f : term -> Tac unit) (b:binder) : Tac unit =
  let (bv, q) = inspect_binder b in
  on_sort_bv f bv

let rec visit_tm (ff : term -> Tac unit) (t : term) : Tac unit =
  let tv = inspect_ln t in
  (match tv with
  | Tv_FVar _ -> ()
  | Tv_Var bv ->
      on_sort_bv ff bv

  | Tv_BVar bv -> on_sort_bv ff bv

  | Tv_Type () -> ()
  | Tv_Const c -> ()
  | Tv_Uvar i u -> ()
  | Tv_Unknown -> ()
  | Tv_Arrow b c ->
      on_sort_binder ff b;
      visit_comp ff c
  | Tv_Abs b t ->
      let b = on_sort_binder (visit_tm ff) b in
      visit_tm ff t

  | Tv_App l (r, q) ->
       visit_tm ff l;
       visit_tm ff r

  | Tv_Refine b r ->
      visit_tm ff r

  | Tv_Let r attrs b def t ->
      visit_tm ff def;
      visit_tm ff t

  | Tv_Match sc brs ->
      visit_tm ff sc;
      iter (visit_br ff) brs

  | Tv_AscribedT e t topt ->
      visit_tm ff e;
      visit_tm ff t

  | Tv_AscribedC e c topt ->
      visit_tm ff e

  ); ff t

and visit_br (ff : term -> Tac unit) (b:branch) : Tac unit =
  let (p, t) = b in
  visit_tm ff t

and visit_comp (ff : term -> Tac unit) (c : comp) : Tac unit =
  let cv = inspect_comp c in
  match cv with
  | C_Total ret decr ->
      visit_tm ff ret;
      (match decr with
        | None -> ()
        | Some d -> visit_tm ff d
      )
  | C_GTotal ret decr ->
      visit_tm ff ret;
      (match decr with
        | None -> ()
        | Some d -> visit_tm ff d
      )

  | C_Lemma pre post pats ->
      visit_tm ff pre;
      visit_tm ff post;
      visit_tm ff pats

  | C_Eff us eff res args ->
      visit_tm ff res;
      iter (fun (a, q) -> visit_tm ff a) args


(** Decides whether a top-level name [nm] syntactically
// appears in the term [t]. *)
let name_appears_in (nm:name) (t:term) : Tac bool =
  let ff (t : term) : Tac unit =
    match t with
    | Tv_FVar fv -> if inspect_fv fv = nm then raise Appears
    | t -> ()
  in
  try ignore (visit_tm ff t); false with
  | Appears -> true
  | e -> raise e


let term_appears_in (t:term) (i:term) : Tac bool =
  name_appears_in (explode_qn (term_to_string t)) i



let atom : eqtype = int

let rec atoms_to_string (l:list atom) = match l with
  | [] -> ""
  | hd::tl -> string_of_int hd ^ " " ^ atoms_to_string tl

type exp : Type =
  | Unit : exp
  | Mult : exp -> exp -> exp
  | Atom : atom -> exp

let amap (a:Type) = list (atom * a) * a
let const (#a:Type) (xa:a) : amap a = ([], xa)
let select (#a:Type) (x:atom) (am:amap a) : Tot a =
  match List.Tot.Base.assoc #atom #a x (fst am) with
  | Some a -> a
  | _ -> snd am
let update (#a:Type) (x:atom) (xa:a) (am:amap a) : amap a =
  (x, xa)::fst am, snd am

let is_uvar (t:term) : Tac bool = match t with
  | Tv_Uvar _ _ -> true
  | Tv_App _ _ ->
      let hd, args = collect_app t in
      Tv_Uvar? hd
  | _ -> false

(* For a given term t, collect all terms in the list l with the same head symbol *)
let rec get_candidates (t:term) (l:list term) : Tac (list term) =
  let name, _ = collect_app t in
  match l with
  | [] -> []
  | hd::tl ->
      let n, _ = collect_app hd in
      if term_eq n name then (
        hd::(get_candidates t tl)
      ) else get_candidates t tl

(* Try to remove a term that is exactly matching, not just that can be unified *)
let rec trivial_cancel (t:atom) (l:list atom) =
  match l with
  | [] -> false, l
  | hd::tl ->
      if hd = t then
        // These elements match, we remove them
        true, tl
      else (let b, res = trivial_cancel t tl in b, hd::res)

(* Call trivial_cancel on all elements of l1.
   The first two lists returned are the remainders of l1 and l2.
   The last two lists are the removed parts of l1 and l2, with
   the additional invariant that they are equal *)
let rec trivial_cancels (l1 l2:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, [], []
  | hd::tl ->
      let b, l2'   = trivial_cancel hd l2 in
      let l1', l2', l1_del, l2_del = trivial_cancels tl l2' am in
      (if b then l1' else hd::l1'), l2',
      (if b then hd::l1_del else l1_del), (if b then hd::l2_del else l2_del)

exception Failed
exception Success

(* For a list of candidates l, count the number that can unify with t.
   Does not try to unify with a uvar, this will be done at the very end.
   Tries to unify with slprops with a different head symbol, it might
   be an abbreviation
 *)
let rec try_candidates (t:atom) (l:list atom) (am:amap term) : Tac (atom * int) =
  match l with
  | [] -> t, 0
  | hd::tl ->
      if is_uvar (select hd am) then (try_candidates t tl am)
      else
        // Encapsulate unify in a try/with to ensure unification is not actually performed
        let res = try if unify (select t am) (select hd am) then raise Success else raise Failed
                  with | Success -> true | _ -> false in
        let t', n' = try_candidates t tl am in
        if res then hd, 1 + n'  else t', n'

(* Remove the given term from the list. Only to be called when
   try_candidates succeeded *)
let rec remove_from_list (t:atom) (l:list atom) : Tac (list atom) =
  match l with
  | [] -> fail "atom in remove_from_list not found: should not happen"; []
  | hd::tl -> if t = hd then tl else hd::remove_from_list t tl

(* Check if two lists of slprops are equivalent by recursively calling
   try_candidates.
   Assumes that only l2 contains terms with the head symbol unresolved.
   It returns all elements that were not resolved during this iteration *)
let rec equivalent_lists_once (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * list atom * list atom) =
  match l1 with
  | [] -> [], l2, l1_del, l2_del
  | hd::tl ->
    let t, n = try_candidates hd l2 am in
    // if n = 0 then
    //   fail ("not equiv: no candidate found for scrutinee " ^ term_to_string (select hd am))
    if n = 1 then (
      let l2 = remove_from_list t l2 in
      equivalent_lists_once tl l2 (hd::l1_del) (t::l2_del) am
    ) else
      // Either too many candidates for this scrutinee, or no candidate but the uvar
      let rem1, rem2, l1'_del, l2'_del = equivalent_lists_once tl l2 l1_del l2_del am in
      hd::rem1, rem2, l1'_del, l2'_del

let get_head (l:list atom) (am:amap term) : term = match l with
  | [] -> `()
  | hd::_ -> select hd am

let is_only_uvar (l:list atom) (am:amap term) : Tac bool =
  if List.Tot.Base.length l = 1 then is_uvar (select (List.Tot.Base.hd l) am)
  else false

(* Assumes that u is a uvar, checks that all variables in l can be unified with it.
   Later in the tactic, the uvar will be unified to a star of l *)
let rec try_unifying_remaining (l:list atom) (u:term) (am:amap term) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
      try if unify u (select hd am) then raise Success else raise Failed with
      | Success -> try_unifying_remaining tl u am
      | _ -> fail ("could not find candidate for scrutinee " ^ term_to_string (select hd am))

(* Recursively calls equivalent_lists_once.
   Stops when we're done with unification, or when we didn't make any progress
   If we didn't make any progress, we have too many candidates for some terms.
   Accumulates rewritings of l1 and l2 in l1_del and l2_del, with the invariant
   that the two lists are unifiable at any point
   The boolean indicates if there is a leftover empty frame
   *)
let rec equivalent_lists' (n:nat) (l1 l2 l1_del l2_del:list atom) (am:amap term)
  : Tac (list atom * list atom * bool) =
  match l1 with
  | [] -> begin match l2 with
    | [] -> (l1_del, l2_del, false)
    | [hd] ->
      // Succeed if there is only one uvar left in l2, which can be therefore
      // be unified with emp
      if is_uvar (select hd am) then (
        // xsdenote is left associative: We put hd at the top to get
        // ?u `star` p <==> emp `star` p
        (l1_del, hd :: l2_del, true))
      else fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    | _ -> fail ("could not find candidates for " ^ term_to_string (get_head l2 am))
    end
  | _ ->
    if is_only_uvar l2 am then (
      // Terms left in l1, but only a uvar left in l2.
      // Put all terms left at the end of l1_rem, so that they can be unified
      // with exactly the uvar because of the structure of xsdenote
      try_unifying_remaining l1 (get_head l2 am) am;
      l1_del @ l1, l2_del @ l2, false
    ) else
      let rem1, rem2, l1_del', l2_del' = equivalent_lists_once l1 l2 l1_del l2_del am in
      let n' = List.Tot.length rem1 in
      if n' >= n then
        // Should always be smaller or equal to n
        // If it is equal, no progress was made.
        fail ("could not find candidate for scrutinee " ^ term_to_string (get_head rem2 am))
      else equivalent_lists' n' rem1 rem2 l1_del' l2_del' am

(* Checks if term for atom t unifies with fall uvars in l *)
let rec unifies_with_all_uvars (t:term) (l:list atom) (am:amap term) : Tac bool =
  match l with
  | [] -> true
  | hd::tl ->
      if unifies_with_all_uvars t tl am then (
        // Unified with tail, try this term
        let hd_t = select hd am in
        if is_uvar hd_t then (
          // The head term is a uvar, try unifying
          try if unify t hd_t then raise Success else raise Failed
          with | Success -> true | _ -> false
        ) else true // The uvar is not a head term, we do not need to try it
      ) else false

(* Puts all terms in l1 that cannot unify with the uvars in l2 at the top:
   They need to be solved first *)
let rec most_restricted_at_top (l1 l2:list atom) (am:amap term) : Tac (list atom) =
  match l1 with
  | [] -> []
  | hd::tl ->
    if unifies_with_all_uvars (select hd am) l2 am then (most_restricted_at_top tl l2 am)@[hd]
    else hd::(most_restricted_at_top tl l2 am)

(* First remove all trivially equal terms, then try to decide equivalence.
   Assumes that l1 does not contain any slprop uvar.
   If it succeeds, returns permutations of l1, l2, and a boolean indicating
   if l2 has a trailing empty frame to be unified
*)
let equivalent_lists (l1 l2:list atom) (am:amap term) : Tac (list atom * list atom * bool) =
  let l1, l2, l1_del, l2_del = trivial_cancels l1 l2 am in
  let l1 = most_restricted_at_top l1 l2 am in
  let n = List.Tot.length l1 in
  let l1_del, l2_del, emp_frame = equivalent_lists' n l1 l2 l1_del l2_del am in
  l1_del, l2_del, emp_frame

open FStar.Reflection.Derived.Lemmas

let rec list_to_string (l:list term) : Tac string =
  match l with
  | [] -> "end"
  | hd::tl -> term_to_string hd ^ " " ^ list_to_string tl

open FStar.Algebra.CommMonoid.Equiv

let rec mdenote (#a:Type u#aa) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp) : a =
  match e with
  | Unit -> CM?.unit m
  | Atom x -> select x am
  | Mult e1 e2 -> CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2)

let rec xsdenote (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom) : a =
  match xs with
  | [] -> CM?.unit m
  | [x] -> select x am
  | x::xs' -> CM?.mult m (select x am) (xsdenote eq m am xs')

let rec flatten (e:exp) : list atom =
  match e with
  | Unit -> []
  | Atom x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

let rec flatten_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs1 xs2:list atom)
  : Lemma (xsdenote eq m am (xs1 @ xs2) `EQ?.eq eq` CM?.mult m (xsdenote eq m am xs1)
                                                               (xsdenote eq m am xs2)) =
  match xs1 with
  | [] ->
      CM?.identity m (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.unit m) (xsdenote eq m am xs2)) (xsdenote eq m am xs2)
  | [x] -> (
      if (Nil? xs2)
      then (right_identity eq m (select x am);
            EQ?.symmetry eq (CM?.mult m (select x am) (CM?.unit m)) (select x am))
      else EQ?.reflexivity eq (CM?.mult m (xsdenote eq m am [x]) (xsdenote eq m am xs2)))
  | x::xs1' ->
      flatten_correct_aux eq m am xs1' xs2;
      EQ?.reflexivity eq (select x am);
      CM?.congruence m (select x am) (xsdenote eq m am (xs1' @ xs2))
                       (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2));
      CM?.associativity m (select x am) (xsdenote eq m am xs1') (xsdenote eq m am xs2);
      EQ?.symmetry eq (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))
                      (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)));
      EQ?.transitivity eq (CM?.mult m (select x am) (xsdenote eq m am (xs1' @ xs2)))
                          (CM?.mult m (select x am) (CM?.mult m (xsdenote eq m am xs1') (xsdenote eq m am xs2)))
                          (CM?.mult m (CM?.mult m (select x am) (xsdenote eq m am xs1')) (xsdenote eq m am xs2))

let rec flatten_correct (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e:exp)
  : Lemma (mdenote eq m am e `EQ?.eq eq` xsdenote eq m am (flatten e)) =
  match e with
  | Unit -> EQ?.reflexivity eq (CM?.unit m)
  | Atom x -> EQ?.reflexivity eq (select x am)
  | Mult e1 e2 ->
      flatten_correct_aux eq m am (flatten e1) (flatten e2);
      EQ?.symmetry eq (xsdenote eq m am (flatten e1 @ flatten e2))
                      (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)));
      flatten_correct eq m am e1;
      flatten_correct eq m am e2;
      CM?.congruence m (mdenote eq m am e1) (mdenote eq m am e2)
                       (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2));
      EQ?.transitivity eq (CM?.mult m (mdenote eq m am e1) (mdenote eq m am e2))
                          (CM?.mult m (xsdenote eq m am (flatten e1)) (xsdenote eq m am (flatten e2)))
                          (xsdenote eq m am (flatten e1 @ flatten e2))

let monoid_reflect (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (e1 e2:exp)
    (_ : squash (xsdenote eq m am (flatten e1) `EQ?.eq eq` xsdenote eq m am (flatten e2)))
       : squash (mdenote eq m am e1 `EQ?.eq eq` mdenote eq m am e2) =
    flatten_correct eq m am e1;
    flatten_correct eq m am e2;
    EQ?.symmetry eq (mdenote eq m am e2) (xsdenote eq m am (flatten e2));
    EQ?.transitivity eq
      (xsdenote eq m am (flatten e1))
      (xsdenote eq m am (flatten e2))
      (mdenote eq m am e2);
    EQ?.transitivity eq
      (mdenote eq m am e1)
      (xsdenote eq m am (flatten e1))
      (mdenote eq m am e2)

// Here we sort the variable numbers

let permute = list atom -> list atom
let sort : permute = List.Tot.Base.sortWith #int (List.Tot.Base.compare_of_bool (<))

#push-options "--fuel 1 --ifuel 1"

let lemma_xsdenote_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (hd:atom) (tl:list atom)
  : Lemma (xsdenote eq m am (hd::tl) `EQ?.eq eq`
         (CM?.mult m (select hd am) (xsdenote eq m am tl)))
  = match tl with
    | [] ->
      assert (xsdenote eq m am (hd::tl) == select hd am);
      CM?.identity m (select hd am);
      EQ?.symmetry eq (CM?.unit m `CM?.mult m` select hd am) (select hd am);
      CM?.commutativity m (CM?.unit m) (select hd am);
      EQ?.transitivity eq
        (xsdenote eq m am (hd::tl))
        (CM?.unit m `CM?.mult m` select hd am)
        (CM?.mult m (select hd am) (xsdenote eq m am tl))
    | _ -> EQ?.reflexivity eq (xsdenote eq m am (hd::tl))

let rec partition_equiv (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (pivot:atom) (q:list atom)
  : Lemma
    (let open FStar.List.Tot.Base in
     let hi, lo = partition (bool_of_compare (compare_of_bool (<)) pivot) q in
     EQ?.eq eq
      (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
      (xsdenote eq m am q))
   = let open FStar.List.Tot.Base in
     let f = bool_of_compare (compare_of_bool (<)) pivot in
     let hi, lo = partition f q in
     match q with
     | [] -> CM?.identity m (xsdenote eq m am hi)
     | hd::tl ->
         let l1, l2 = partition f tl in
         partition_equiv eq m am pivot tl;
         assert (EQ?.eq eq
           (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
           (xsdenote eq m am tl));

         EQ?.reflexivity eq (xsdenote eq m am l1);
         EQ?.reflexivity eq (xsdenote eq m am l2);
         EQ?.reflexivity eq (xsdenote eq m am hi);
         EQ?.reflexivity eq (xsdenote eq m am lo);


         if f hd then begin
           assert (hi == hd::l1 /\ lo == l2);
           lemma_xsdenote_aux eq m am hd l1;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am l1)
             (xsdenote eq m am l2);
           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l1)
             (xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l1) `CM?.mult m` xsdenote eq m am l2)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))

         end else begin
           assert (hi == l1 /\ lo == hd::l2);
           lemma_xsdenote_aux eq m am hd l2;
           CM?.congruence m
             (xsdenote eq m am hi)
             (xsdenote eq m am lo)
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           CM?.commutativity m
             (xsdenote eq m am l1)
             (select hd am `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (xsdenote eq m am l1 `CM?.mult m` (select hd am `CM?.mult m` xsdenote eq m am l2))
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1);

           CM?.associativity m
             (select hd am)
             (xsdenote eq m am l2)
             (xsdenote eq m am l1);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             ((select hd am `CM?.mult m` xsdenote eq m am l2) `CM?.mult m` xsdenote eq m am l1)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1));

           CM?.commutativity m (xsdenote eq m am l2) (xsdenote eq m am l1);
           EQ?.reflexivity eq (select hd am);
           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1)
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l2 `CM?.mult m` xsdenote eq m am l1))
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2));

           CM?.congruence m
             (select hd am)
             (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2)
             (select hd am)
             (xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` (xsdenote eq m am l1 `CM?.mult m` xsdenote eq m am l2))
             (select hd am `CM?.mult m` xsdenote eq m am tl);

           lemma_xsdenote_aux eq m am hd tl;
           EQ?.symmetry eq
             (xsdenote eq m am (hd::tl))
             (select hd am `CM?.mult m` xsdenote eq m am tl);
           EQ?.transitivity eq
             (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
             (select hd am `CM?.mult m` xsdenote eq m am tl)
             (xsdenote eq m am (hd::tl))
         end

let rec sort_correct_aux (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (xs:list atom)
  : Lemma (requires True)
          (ensures xsdenote eq m am xs `EQ?.eq eq` xsdenote eq m am (sort xs))
          (decreases (FStar.List.Tot.Base.length xs))
  = match xs with
  | [] -> EQ?.reflexivity eq (xsdenote eq m am [])
  | pivot::q ->
      let open FStar.List.Tot.Base in
      let f:int -> int -> int = compare_of_bool (<) in
      let hi, lo = partition (bool_of_compare f pivot) q in
      flatten_correct_aux eq m am (sort lo) (pivot::sort hi);
      assert (xsdenote eq m am (sort xs) `EQ?.eq eq`
        CM?.mult m (xsdenote eq m am (sort lo))
                   (xsdenote eq m am (pivot::sort hi)));

      lemma_xsdenote_aux eq m am pivot (sort hi);

      EQ?.reflexivity eq (xsdenote eq m am (sort lo));
      CM?.congruence m
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` xsdenote eq m am (pivot::sort hi))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi))));

      CM?.commutativity m
        (xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` xsdenote eq m am (sort hi));
      CM?.associativity m
        (select pivot am)
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo));
      EQ?.transitivity eq
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        ((select pivot am `CM?.mult m` xsdenote eq m am (sort hi)) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      EQ?.transitivity eq
         (xsdenote eq m am (sort xs))
         (xsdenote eq m am (sort lo) `CM?.mult m` (select pivot am `CM?.mult m` xsdenote eq m am (sort hi)))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))));


      partition_length (bool_of_compare f pivot) q;
      sort_correct_aux eq m am hi;
      sort_correct_aux eq m am lo;
      EQ?.symmetry eq (xsdenote eq m am lo) (xsdenote eq m am (sort lo));
      EQ?.symmetry eq (xsdenote eq m am hi) (xsdenote eq m am (sort hi));
      CM?.congruence m
        (xsdenote eq m am (sort hi))
        (xsdenote eq m am (sort lo))
        (xsdenote eq m am hi)
        (xsdenote eq m am lo);
      assert (EQ?.eq eq
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));

      EQ?.reflexivity eq (select pivot am);
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo))
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am (sort hi) `CM?.mult m` xsdenote eq m am (sort lo)))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)));

      partition_equiv eq m am pivot q;
      CM?.congruence m
        (select pivot am)
        (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo)
        (select pivot am)
        (xsdenote eq m am q);
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am hi `CM?.mult m` xsdenote eq m am lo))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      assert (EQ?.eq eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q)));

      lemma_xsdenote_aux eq m am pivot q;
      EQ?.symmetry eq
        (xsdenote eq m am (pivot::q))
        (select pivot am `CM?.mult m` (xsdenote eq m am q));
      EQ?.transitivity eq
        (xsdenote eq m am (sort xs))
        (select pivot am `CM?.mult m` (xsdenote eq m am q))
        (xsdenote eq m am xs);
      EQ?.symmetry eq (xsdenote eq m am (sort xs)) (xsdenote eq m am xs)

#pop-options

#push-options "--fuel 0 --ifuel 0"

let identity_left (#a:Type) (eq:equiv a) (m:cm a eq) (x:a)
  : Lemma (EQ?.eq eq x (CM?.mult m (CM?.unit m) x))
  = CM?.identity m x;
    EQ?.symmetry eq (CM?.mult m (CM?.unit m) x) x

let identity_right_diff (#a:Type) (eq:equiv a) (m:cm a eq) (x y:a) : Lemma
  (requires EQ?.eq eq x y)
  (ensures EQ?.eq eq (CM?.mult m x (CM?.unit m)) y)
  = right_identity eq m x;
    EQ?.transitivity eq (CM?.mult m x (CM?.unit m)) x y

let rec dismiss_slprops () : Tac unit =
  match term_as_formula' (cur_goal ()) with
    | App t _ -> if term_eq t (`squash) then () else (dismiss(); dismiss_slprops ())
    | _ -> dismiss(); dismiss_slprops ()

let rec n_identity_left (n:int) (eq m:term) : Tac unit
  = if n = 0 then (
      apply_lemma (`(EQ?.reflexivity (`#eq)));
      // Cleaning up, in case a uvar has been generated here. It'll be solved later
      set_goals [])
    else (
      apply_lemma (`identity_right_diff (`#eq) (`#m));
      // Drop the slprops generated, they will be solved later
      dismiss_slprops ();
      n_identity_left (n-1) eq m
    )

let equivalent_sorted (#a:Type) (eq:equiv a) (m:cm a eq) (am:amap a) (l1 l2 l1' l2':list atom)
    : Lemma (requires
              sort l1 == sort l1' /\
              sort l2 == sort l2' /\
              xsdenote eq m am l1 `EQ?.eq eq` xsdenote eq m am l2)
           (ensures xsdenote eq m am l1' `EQ?.eq eq` xsdenote eq m am l2')
  = sort_correct_aux eq m am l1';
    sort_correct_aux eq m am l1;
    EQ?.symmetry eq (xsdenote eq m am l1) (xsdenote eq m am (sort l1));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l1'))
      (xsdenote eq m am l1);
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l1)
      (xsdenote eq m am l2);
    sort_correct_aux eq m am l2;
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am l2)
      (xsdenote eq m am (sort l2));
    sort_correct_aux eq m am l2';
    EQ?.symmetry eq (xsdenote eq m am l2') (xsdenote eq m am (sort l2'));
    EQ?.transitivity eq
      (xsdenote eq m am l1')
      (xsdenote eq m am (sort l2))
      (xsdenote eq m am l2')

#pop-options

(* Finds the position of first occurrence of x in xs.
   This is now specialized to terms and their funny term_eq. *)
let rec where_aux (n:nat) (x:term) (xs:list term) :
    Tot (option nat) (decreases xs) =
  match xs with
  | [] -> None
  | x'::xs' -> if term_eq x x' then Some n else where_aux (n+1) x xs'
let where = where_aux 0

let fatom (t:term) (ts:list term) (am:amap term) : Tac (exp * list term * amap term) =
  match where t ts with
  | Some v -> (Atom v, ts, am)
  | None ->
    let vfresh = List.Tot.Base.length ts in
    let t = norm_term [iota; zeta] t in
    (Atom vfresh, ts @ [t], update vfresh t am)

// This expects that mult, unit, and t have already been normalized
let rec reification_aux (ts:list term) (am:amap term)
                        (mult unit t : term) : Tac (exp * list term * amap term) =
  let hd, tl = collect_app_ref t in
  match inspect hd, List.Tot.Base.list_unref tl with
  | Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)] ->
    if term_eq (pack (Tv_FVar fv)) mult
    then (let (e1, ts, am) = reification_aux ts am mult unit t1 in
          let (e2, ts, am) = reification_aux ts am mult unit t2 in
          (Mult e1 e2, ts, am))
    else fatom t ts am
  | _, _ ->
    if term_eq t unit
    then (Unit, ts, am)
    else fatom t ts am

let reification (eq: term) (m: term) (ts:list term) (am:amap term) (t:term) :
    Tac (exp * list term * amap term) =
  let mult = norm_term [iota; zeta; delta] (`CM?.mult (`#m)) in
  let unit = norm_term [iota; zeta; delta] (`CM?.unit (`#m)) in
  let t    = norm_term [iota; zeta] t in
  reification_aux ts am mult unit t

let rec convert_map (m : list (atom * term)) : term =
  match m with
  | [] -> `[]
  | (a, t)::ps ->
      let a = pack_ln (Tv_Const (C_Int a)) in
      (* let t = norm_term [delta] t in *)
      `((`#a, (`#t)) :: (`#(convert_map ps)))


(* `am` is an amap (basically a list) of terms, each representing a value
of type `a` (whichever we are canonicalizing). This functions converts
`am` into a single `term` of type `amap a`, suitable to call `mdenote` with *)
let convert_am (am : amap term) : term =
  let (map, def) = am in
  (* let def = norm_term [delta] def in *)
  `( (`#(convert_map map), `#def) )

let rec quote_exp (e:exp) : term =
    match e with
    | Unit -> (`Unit)
    | Mult e1 e2 -> (`Mult (`#(quote_exp e1)) (`#(quote_exp e2)))
    | Atom n -> let nt = pack_ln (Tv_Const (C_Int n)) in
                (`Atom (`#nt))

let rec quote_atoms (l:list atom) = match l with
  | [] -> `[]
  | hd::tl -> let nt = pack_ln (Tv_Const (C_Int hd)) in
              (`Cons (`#nt) (`#(quote_atoms tl)))

let normal_steps = [primops; iota; zeta; delta_only [
          `%mdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
          `%flatten; `%sort;
          `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
          `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%rm]]

let normal_tac (#a:Type) (x:a) : a = FStar.Pervasives.norm normal_steps x

let normal_elim (x:Type0) : Lemma
  (requires x)
  (ensures normal_tac x)
  = ()

let canon_l_r (eq: term) (m: term) (lhs rhs:term) : Tac unit =
  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let am = const m_unit in (* empty map *)
  let (r1_raw, ts, am) = reification eq m [] am lhs in
  let (r2_raw,  _, am) = reification eq m ts am rhs in

  let l1_raw, l2_raw, emp_frame = equivalent_lists (flatten r1_raw) (flatten r2_raw) am in

  let am = convert_am am in
  let r1 = quote_exp r1_raw in
  let r2 = quote_exp r2_raw in
  let l1 = quote_atoms l1_raw in
  let l2 = quote_atoms l2_raw in
  change_sq (`(normal_tac (mdenote (`#eq) (`#m) (`#am) (`#r1)
                 `EQ?.eq (`#eq)`
               mdenote (`#eq) (`#m) (`#am) (`#r2))));
  apply_lemma (`normal_elim);

  apply (`monoid_reflect );


  apply_lemma (`equivalent_sorted (`#eq) (`#m) (`#am) (`#l1) (`#l2));
  let g = goals () in
  if List.Tot.Base.length g = 0 then
    // The application of equivalent_sorted seems to sometimes solve
    // all goals
    ()
  else (
    norm [primops; iota; zeta; delta_only
      [`%xsdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
        `%flatten; `%sort;
        `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
        `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
        `%fst; `%__proj__Mktuple2__item___1;
        `%snd; `%__proj__Mktuple2__item___2;
        `%__proj__CM__item__unit;
        `%__proj__CM__item__mult;
        `%rm

        ]];

    split();
    split();
    // equivalent_lists should have built valid permutations.
    // If that's not the case, it is a bug in equivalent_lists
    or_else trefl (fun _ -> fail "first equivalent_lists did not build a valid permutation");
    or_else trefl (fun _ -> fail "second equivalent_lists did not build a valid permutation");

    if emp_frame then apply_lemma (`identity_left (`#eq) (`#m))
    else apply_lemma (`(EQ?.reflexivity (`#eq)))
  )


let canon_monoid (eq:term) (m:term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app_ref t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let open FStar.List.Tot.Base in
       let rel, xy = collect_app_ref rel_xy in
       if (length xy >= 2)
       then (
         match index xy (length xy - 2) , index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) ->
           canon_l_r eq m lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

(* Try to integrate it into larger tactic *)

let canon' () : Tac unit =
  canon_monoid (`req) (`rm)

(* A Variant of canon to collect all slprops in the context into the return_post term,
   and set all extra uvars to emp *)

let rec slterm_nbr_uvars (t:term) : Tac int =
  match inspect t with
  | Tv_Uvar _ _ -> 1
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    if term_eq hd (`star) then

      // Only count the number of unresolved slprops, not program implicits
      fold_left (fun n (x, _) -> n + slterm_nbr_uvars x) 0 args
    else if is_uvar hd then 1
    else 0
  | Tv_Abs _ t -> slterm_nbr_uvars t
  | _ -> 0


/// Puts the term containing return_post at the top.
/// Returns the atom corresponding to return_post, and the list with the atom removed
let rec return_at_top' (l:list atom) (am:amap term) : Tac (atom * list atom) =
  match l with
  | [] -> fail "Couldn't find return_post term"
  | hd::tl ->
      if term_appears_in (`return_post) (select hd am) then hd, tl else
      let ret, rest = return_at_top' tl am in
      ret, hd::rest

/// Checks whether the return slprop is fully resolved
let return_resolved (l:list atom) (am:amap term) : Tac bool =
  let ret, _ = return_at_top' l am in
  let t = norm_term [delta_only [`%return_post]] (select ret am) in
  slterm_nbr_uvars t = 0

let return_at_top (l:list atom) (am:amap term) : Tac (nat * list atom) =
  let ret, tl = return_at_top' l am in
  List.Tot.Base.length tl, ret :: tl

exception AlreadyGathered

let gather_return (eq: term) (m: term) (lhs rhs:term) : Tac unit =
  let return_lhs = term_appears_in (`return_post) lhs in
  let return_rhs = term_appears_in (`return_post) rhs in
  let two_returns = return_lhs && return_rhs in

  let lhs, rhs =
    // Ensure that the return_post is on the left
    if return_rhs && not (return_lhs) then
      (apply_lemma (`equiv_sym); rhs, lhs) else lhs, rhs
  in


  let m_unit = norm_term [iota; zeta; delta](`CM?.unit (`#m)) in
  let am = const m_unit in (* empty map *)
  let (r1_raw, ts, am) = reification eq m [] am lhs in
  let (r2_raw,  _, am) = reification eq m ts am rhs in

  let l1_raw = flatten r1_raw in
  let l2_raw = flatten r2_raw in

  let resolved1 = return_resolved l1_raw am in
  let resolved2 = if two_returns then return_resolved l2_raw am else true in

  if resolved1 && resolved2 then (
    // The return_post have already been gathered, we will fall back on the normal canon
    raise AlreadyGathered
  ) else (

    let n_l1, l1_raw = return_at_top l1_raw am in

    let n_l2, l2_raw = if two_returns then return_at_top l2_raw am else 0, l2_raw in

    let am = convert_am am in
    let r1 = quote_exp r1_raw in
    let r2 = quote_exp r2_raw in
    change_sq (`(normal_tac (mdenote (`#eq) (`#m) (`#am) (`#r1)
                   `EQ?.eq (`#eq)`
                 mdenote (`#eq) (`#m) (`#am) (`#r2))));
    apply_lemma (`normal_elim);

    apply (`monoid_reflect );

    let l1 = quote_atoms l1_raw in
    let l2 = quote_atoms l2_raw in

    apply_lemma (`equivalent_sorted (`#eq) (`#m) (`#am) (`#l1) (`#l2));
    let g = goals () in
    if List.Tot.Base.length g = 0 then
      // The application of equivalent_sorted seems to sometimes solve
      // all goals
      ()
    else (
      norm [primops; iota; zeta; delta_only
        [`%xsdenote; `%select; `%List.Tot.Base.assoc; `%List.Tot.Base.append;
          `%flatten; `%sort;
          `%return_post;
          `%List.Tot.Base.sortWith; `%List.Tot.Base.partition;
          `%List.Tot.Base.bool_of_compare; `%List.Tot.Base.compare_of_bool;
          `%fst; `%__proj__Mktuple2__item___1;
          `%snd; `%__proj__Mktuple2__item___2;
          `%__proj__CM__item__unit;
          `%__proj__CM__item__mult;
          `%rm

          ]];

      split();
      split();
      // equivalent_lists should have built valid permutations.
      // If that's not the case, it is a bug in equivalent_lists
      or_else trefl (fun _ -> fail "first equivalent_lists did not build a valid permutation");
      or_else trefl (fun _ -> fail "second equivalent_lists did not build a valid permutation");

      if n_l2 > n_l1 then
        (apply_lemma (`(EQ?.symmetry (`#eq)));
         dismiss_slprops();
         let n = n_l2 - n_l1 in
         focus (fun _ -> n_identity_left n eq m))
      else (let n = n_l1 - n_l2 in focus (fun _ -> n_identity_left n eq m))
    )
  )

let canon_return' (eq:term) (m:term) : Tac unit =
  norm [iota; zeta];
  let t = cur_goal () in
  // removing top-level squash application
  let sq, rel_xy = collect_app_ref t in
  // unpacking the application of the equivalence relation (lhs `EQ?.eq eq` rhs)
  (match rel_xy with
   | [(rel_xy,_)] -> (
       let open FStar.List.Tot.Base in
       let rel, xy = collect_app_ref rel_xy in
       if (length xy >= 2)
       then (
         match index xy (length xy - 2) , index xy (length xy - 1) with
         | (lhs, Q_Explicit) , (rhs, Q_Explicit) ->
           gather_return eq m lhs rhs
         | _ -> fail "Goal should have been an application of a binary relation to 2 explicit arguments"
       )
       else (
         fail "Goal should have been an application of a binary relation to n implicit and 2 explicit arguments"
       )
     )
   | _ -> fail "Goal should be squash applied to a binary relation")

let canon_return () : Tac unit =
  canon_return' (`req) (`rm)


let solve_can_be_split (args:list argv) : Tac bool =
  match args with
  | [(t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> apply_lemma (`equiv_can_be_split);
                     dismiss_slprops();
                     // If we have exactly the same term on both side,
                     // equiv_sl_implies would solve the goal immediately
                     or_else (fun _ -> apply_lemma (`equiv_refl))
                      (fun _ ->
                      if rnbr = 0 then apply_lemma (`equiv_sym);

                       norm [delta_only [
                              `%__proj__CM__item__unit;
                              `%__proj__CM__item__mult;
                              `%rm;
                              `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                              `%fst; `%snd];
                            delta_attr [`%__reduce__];
                            primops; iota; zeta];
                       canon'()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

val emp_unit_variant (p:vprop) : Lemma
   (ensures can_be_split p (p `star` vemp))

let solve_can_be_split_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ ->
          ignore (forall_intro());
          apply_lemma (`equiv_can_be_split);
          dismiss_slprops();
          or_else (fun _ -> apply_lemma (`equiv_refl))
            (fun _ ->
            if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
            or_else (fun _ ->  flip()) (fun _ -> ());
            norm [delta_only [
                   `%__proj__CM__item__unit;
                   `%__proj__CM__item__mult;
                   `%rm;
                   `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                   `%fst; `%snd];
                delta_attr [`%__reduce__];
                 primops; iota; zeta];
            canon'()));
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen

let solve_equiv_forall (args:list argv) : Tac bool =
  match args with
  | [_; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        // TODO: Do this count in a better way
                        if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
                        or_else (fun _ ->  flip()) (fun _ -> ());
                        norm [delta_only [
                                `%__proj__CM__item__unit;
                                `%__proj__CM__item__mult;
                                `%rm;
                                `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                `%fst; `%snd];
                              delta_attr [`%__reduce__];
                              primops; iota; zeta];
                        canon'());
        true
      ) else false

  | _ -> false // Ill-formed can_be_split, should not happen


let solve_can_be_split_post (args:list argv) : Tac bool =
  match args with
  | [_; _; (t1, _); (t2, _)] ->
      let lnbr = slterm_nbr_uvars t1 in
      let rnbr = slterm_nbr_uvars t2 in
      if lnbr + rnbr <= 1 then (
        let open FStar.Algebra.CommMonoid.Equiv in
        focus (fun _ -> norm[];
                      let g = _cur_goal () in
                      ignore (forall_intro());
                      apply_lemma (`equiv_forall_elim);
                      match goals () with
                      | [] -> ()
                      | _ ->
                        dismiss_slprops ();
                        ignore (forall_intro());
                        // TODO: Do this count in a better way
                        if lnbr <> 0 && rnbr = 0 then apply_lemma (`equiv_sym);
                        or_else (fun _ ->  flip()) (fun _ -> ());
                        norm [delta_only [
                                `%__proj__CM__item__unit;
                                `%__proj__CM__item__mult;
                                `%rm;
                                `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                                `%fst; `%snd];
                              delta_attr [`%__reduce__];
                              primops; iota; zeta];
                        canon'());
        true
      ) else false

  | _ -> fail "ill-formed can_be_split_post"

let is_return_eq (l r:term) : Tac bool =
  let nl, al = collect_app l in
  let nr, ar = collect_app r in
  term_eq nl (`return_pre) || term_eq nr (`return_pre)

let rec solve_indirection_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        if is_return_eq l r then later() else trefl();
        solve_indirection_eqs tl
    | _ -> later(); solve_indirection_eqs tl


let rec solve_all_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_all_eqs tl
    | _ -> later(); solve_all_eqs tl


let rec solve_return_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
        trefl();
        solve_return_eqs tl
    | _ -> later(); solve_return_eqs tl

// The term corresponds to a goal containing a return_post
let solve_return (t:term) : Tac unit
  = // Remove potential annotations first
    if term_appears_in (`can_be_split) t then (
      apply_lemma (`equiv_can_be_split)
    ) else if term_appears_in (`can_be_split_forall) t then (
      ignore (forall_intro ());
      apply_lemma (`equiv_can_be_split)
    ) else if term_appears_in (`equiv_forall) t then (
      fail "equiv_forall"
      // apply_lemma (`equiv_forall_elim);
      // ignore (forall_intro())
    ) else if term_appears_in (`can_be_split_post) t then (
      apply_lemma (`can_be_split_post_elim);
      dismiss_slprops();
      ignore (forall_intro ());
      ignore (forall_intro ())
    ) else
      // This should never happen
      fail "return_post goal in unexpected position";
    match (goals ()) with
    | [] -> () // Can happen if reflexivity was sufficient here
    | _ -> norm [delta_only [
                     `%CE.__proj__CM__item__unit;
                     `%CE.__proj__CM__item__mult;
                     `%rm;
                     `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
                     `%fst; `%snd];
               delta_attr [`%__reduce__];
               primops; iota; zeta];
           canon_return ()


let rec solve_all_returns (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let t = goal_type hd in
    let f = term_as_formula' t in
    if term_appears_in (`return_post) t then (
      try focus (fun _ -> solve_return t) with
        // If return_post has already been gathered, we remove the annotation, and will solve this constraint normally later
        | AlreadyGathered -> norm [delta_only [`%return_post]]; later()
        | TacticFailure m -> fail m
        | _ -> () // Success
    ) else later();
    solve_all_returns tl


let rec solve_triv_eqs (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl ->
    let f = term_as_formula' (goal_type hd) in
    match f with
    | Comp (Eq _) l r ->
      let lnbr = slterm_nbr_uvars l in
      let rnbr = slterm_nbr_uvars r in
      // Only solve equality if there is only one uvar
      // trefl();
     if lnbr = 0 || rnbr = 0 then trefl () else later();
      solve_triv_eqs tl
    | _ -> later(); solve_triv_eqs tl

// Returns true if the goal has been solved, false if it should be delayed
let solve_or_delay (g:goal) : Tac bool =
  // Beta-reduce the goal first if possible
  norm [];
  let f = term_as_formula' (cur_goal ()) in
  match f with
  | App _ t ->
      let hd, args = collect_app t in
      if term_eq hd (`can_be_split) then solve_can_be_split args
      else if term_eq hd (`can_be_split_forall) then solve_can_be_split_forall args
      else if term_eq hd (`equiv_forall) then solve_equiv_forall args
      else if term_eq hd (`can_be_split_post) then solve_can_be_split_post args
      else false
  | Comp (Eq _) l r ->
    let lnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars l) in
    let rnbr = List.Tot.length (FStar.Reflection.Builtins.free_uvars r) in
    // Only solve equality if one of the terms is completely determined
    if lnbr = 0 || rnbr = 0 then (trefl (); true) else false
  | _ -> false


// Returns true if it successfully solved a goal
// If it returns false, it means it didn't find any solvable goal,
// which should mean only delayed goals are left
let rec pick_next (l:list goal) : Tac bool =
  match l with
  | [] -> false
  | a::q -> if solve_or_delay a then true else (later (); pick_next q)


let rec resolve_tac () : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    norm [];
    // TODO: If it picks a goal it cannot solve yet, try all the other ones?
    if pick_next g then resolve_tac ()
    else fail "Could not make progress, no solvable goal found"


let rec resolve_tac_logical () : Tac unit =
  match goals () with
  | [] -> ()
  | g ->
    if pick_next g then resolve_tac_logical ()
    else
      // This is only for requires/ensures constraints, which are equalities
      // There should always be a scheduling of constraints, but it can happen
      // that some uvar for the type of an equality is not resolved.
      // If we reach this point, we try to simply call the unifier instead of failing directly
      solve_all_eqs g




let typ_contains_req_ens (t:term) : Tac bool =
  let name, _ = collect_app t in
  if term_eq name (`req_t) || term_eq name (`ens_t) then true
  else false

let rec filter_goals (l:list goal) : Tac (list goal * list goal) =
  match l with
  | [] -> [], []
  | hd::tl ->
      let slgoals, loggoals = filter_goals tl in
      match term_as_formula' (goal_type hd) with
      | Comp (Eq t) _ _ ->
        if Some? t then
          let b = typ_contains_req_ens (Some?.v t) in
          if b then slgoals, hd::loggoals
          else hd::slgoals, loggoals
        else hd::slgoals, loggoals
      | App t _ -> if term_eq t (`squash) then hd::slgoals, loggoals else slgoals, loggoals
      | _ -> slgoals, loggoals



let rec norm_return_pre (l:list goal) : Tac unit =
  match l with
  | [] -> ()
  | hd::tl -> norm [delta_only [`%return_pre]]; later(); norm_return_pre tl

[@@ resolve_implicits; framing_implicit]
let init_resolve_tac () : Tac unit =
  // We split goals between framing goals, about slprops (slgs)
  // and goals related to requires/ensures, that depend on slprops (loggs)
  let slgs, loggs = filter_goals (goals()) in

  // We first solve the slprops
  set_goals slgs;

  // We first solve all indirection equalities that will not lead to imprecise unification
  // i.e. we can solve all equalities inserted by layered effects, except the ones corresponding
  // to the preconditions of a pure return
  solve_indirection_eqs (goals());

  // To debug, it is best to look at the goals at this stage. Uncomment the next line
  // dump "initial goals";

  // We now solve all postconditions of pure returns to avoid restricting the uvars
  solve_all_returns (goals ());

  // We can now solve the equalities for returns
  solve_return_eqs (goals());

  // It is important to not normalize the return_pre equalities before solving them
  // Else, we lose some variables dependencies, leading to the tactic being stuck
  // See test7 in FramingTestSuite for more explanations of what is failing
  // Once unification has been done, we can then safely normalize and remove all return_pre
  norm_return_pre (goals());

  // TODO: If we had better handling of lifts from PURE, we might prove a true
  // sl_implies here, "losing" extra assertions"

  resolve_tac ();


  // We now solve the requires/ensures goals, which are all equalities
  // All slprops are resolved by now
  set_goals loggs;
  resolve_tac_logical ()


(* Some helper functions *)

val get (#[@@framing_implicit] p:vprop) (_:unit) : SteelSelF (rmem p)
  p (fun _ -> p)
  (requires fun _ -> True)
  (ensures fun h0 r h1 -> normal (frame_equalities p h0 h1 /\ frame_equalities p r h1))

val change_slprop (p q:vprop) (vp:erased (t_of p)) (vq:erased (t_of q))
  (l:(m:mem) -> Lemma
    (requires interp (hp_of p) m /\ sel_of p m == reveal vp)
    (ensures interp (hp_of q) m /\ sel_of q m == reveal vq)
  ) : SteelSel unit p (fun _ -> q) (fun h -> h p == reveal vp) (fun _ _ h1 -> h1 q == reveal vq)



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



(* AF: There probably is a simpler way to get from p to squash p in a tactic, so that we can use apply_lemma *)
let squash_and p (x:squash (p /\ True)) : (p /\ True) =
  let x : squash (p `c_and` True) = FStar.Squash.join_squash x in
  x

let selector_tactic () : Tac unit =
  apply (`squash_and);
  apply_lemma (`intro_can_be_split_frame);
  flip ();
  norm [delta_only [
         `%__proj__CM__item__unit;
         `%__proj__CM__item__mult;
         `%rm;
         `%__proj__Mktuple2__item___1; `%__proj__Mktuple2__item___2;
         `%fst; `%snd];
       delta_attr [`%__reduce__];
       primops; iota; zeta];
  canon' ()

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
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
    // AF: Uncommenting the following line leads to the error
    // ASSERTION FAILURE: Name not found: pure_null_wp
    // during the encoding to Z3
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
