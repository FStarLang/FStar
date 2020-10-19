(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)


/// An experimental effect for Steel that does framing in binds


module Steel.FramingEffect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
open Steel.Memory
open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

#set-options "--warn_error -330"  //turn off the experimental feature warning

let join_preserves_interp (hp:slprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)

let ens_depends_only_on (#a:Type) (pre:slprop) (post:a -> slprop)
  (q:(hmem pre -> x:a -> hmem (post x) -> prop))

= //can join any disjoint mem to the pre-mem and q is still valid
  (forall x (m_pre:hmem pre) m_post (m:mem{disjoint m_pre m}).
     q m_pre x m_post <==> q (join m_pre m) x m_post) /\  //at this point we need to know interp pre (join m_pre m) -- use join_preserves_interp for that

  //can join any disjoint mem to the post-mem and q is still valid
  (forall x m_pre (m_post:hmem (post x)) (m:mem{disjoint m_post m}).
     q m_pre x m_post <==> q m_pre x (join m_post m))

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1
type req_t (pre:pre_t) = q:(hmem pre -> prop){  //inlining depends only on
  forall (m0:hmem pre) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)
}
type ens_t (pre:pre_t) (a:Type u#a) (post:post_t u#a a) : Type u#(max 2 a) =
  q:(hmem pre -> x:a -> hmem (post x) -> prop){
    ens_depends_only_on pre post q
  }

#push-options "--warn_error -271"
let interp_depends_only_on_post (#a:Type) (hp:a -> slprop)
: Lemma
  (forall (x:a).
     (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1)))
= let aux (x:a)
    : Lemma
      (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1))
      [SMTPat ()]
    = interp_depends_only_on (hp x) in
  ()
#pop-options

let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state pre =
  interp_depends_only_on pre;
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a pre post
= interp_depends_only_on pre;
  interp_depends_only_on_post post;
  fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post (req_to_act_req req) (ens_to_act_ens ens)

assume val sl_implies (p q:slprop u#1) : Type0

assume val sl_implies_reflexive (p:slprop u#1)
: Lemma (p `sl_implies` p)
  [SMTPat (p `sl_implies` p)]

assume val sl_implies_interp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem) (f:slprop). interp (p `star` f) m ==>  interp (q `star` f) m)
  [SMTPat (p `sl_implies` q)]

assume val sl_implies_interp_emp (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem). interp p m ==>  interp q m)
  [SMTPat (p `sl_implies` q)]

assume val sl_implies_preserves_frame (p q:slprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures
    forall (m1 m2:mem) (r frame:slprop).
      Sem.post_preserves_frame #state p frame m1 m2 ==>
      Sem.post_preserves_frame #state q frame m1 m2)
  [SMTPat (p `sl_implies` q)]

// assume val sl_implies_preserves_frame_right (p q:slprop u#1)
// : Lemma
//   (requires p `sl_implies` q)
//   (ensures
//     forall (m1 m2:mem) (r:slprop).
//       Sem.preserves_frame #state r p m1 m2 ==>
//       Sem.preserves_frame #state r q m1 m2)
//   [SMTPat (p `sl_implies` q)]


irreducible let framing_implicit : unit = ()

unfold
let return_req (p:slprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (a:Type) (x:a) (p:a -> slprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

(*
 * Return is parametric in post (cf. return-scoping.txt)
 *)
let return (a:Type) (x:a) (#[@@ framing_implicit] p:a -> slprop)
: repr a (p x) p (return_req (p x)) (return_ens a x p)
= fun _ -> x

(*
 * We allow weakening of post resource of f to pre resource of g
 *)
unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (_:squash (forall (x:a). post_f x `sl_implies` pre_g x))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (_:squash (forall (x:a). post_f x `sl_implies` pre_g x))
: ens_t pre_f b post_g
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (req_g:(x:a -> req_t (pre_g x))) (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit] p:squash (forall (x:a). post_f x `sl_implies` pre_g x))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    post_g
    (bind_req req_f ens_f req_g p)
    (bind_ens req_f ens_f ens_g p)
= fun frame ->
  let x = f frame in
  (g x) frame


(*
 * TODO: bind should do substitution for pure c1 (if bind c1 c2)
 *         applications might be ok, but let bindings may fail currently
 *)

(*
 * f <: g
 *)

unfold
let subcomp_pre (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a) (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (pre_g `sl_implies` pre_f))
  (_:squash (forall (x:a). post_f x `sl_implies` post_g x))
: pure_pre
= (forall (m0:hmem pre_g). req_g m0 ==> req_f m0) /\
  (forall (m0:hmem pre_g) (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> ens_g m0 x m1)

let subcomp (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (#[@@ framing_implicit] p1:squash (pre_g `sl_implies` pre_f))
  (#[@@ framing_implicit] p2:squash (forall (x:a). post_f x `sl_implies` post_g x))
  (f:repr a pre_f post_f req_f ens_f)
: Pure (repr a pre_g post_g req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g p1 p2)
  (ensures fun _ -> True)
= f

unfold
let if_then_else_req (#pre:pre_t)
  (req_then:req_t pre) (req_else:req_t pre)
  (p:Type0)
: req_t pre
= fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h)

unfold
let if_then_else_ens (#a:Type) (#pre:pre_t) (#post:post_t a)
  (ens_then:ens_t pre a post) (ens_else:ens_t pre a post)
  (p:Type0)
: ens_t pre a post
= fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1)

let if_then_else (a:Type)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t a)
  (req_then:req_t pre) (ens_then:ens_t pre a post)
  (req_else:req_t pre) (ens_else:ens_t pre a post)
  (f:repr a pre post req_then ens_then)
  (g:repr a pre post req_else ens_else)
  (p:bool)
: Type
= repr a pre post
    (if_then_else_req req_then req_else p)
    (if_then_else_ens ens_then ens_else p)

reifiable reflectable
layered_effect {
  SteelF: a:Type -> pre:pre_t -> post:post_t a -> req_t pre -> ens_t pre a post -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
}

new_effect Steel = SteelF

(*
 * Keeping f_frame aside for now
 *)
let frame_aux (#a:Type)
  (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:repr a pre post req ens) (frame:slprop)
: repr a (pre `star` frame) (fun x -> post x `star` frame) req ens
= fun frame' ->
  Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) frame (fun _ -> True))


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
  (frame_f:slprop) (frame_g:slprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` (pre_g x `star` frame_g)))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_f:slprop) (frame_g:slprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` (pre_g x `star` frame_g)))
: ens_t (pre_f `star` frame_f) b (fun y -> post_g y `star` frame_g)
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steel_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (req_g:(x:a -> req_t (pre_g x))) (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    (fun y -> post_g y `star` frame_g)
    (bind_steel_steel_req req_f ens_f req_g frame_f frame_g p)
    (bind_steel_steel_ens req_f ens_f ens_g frame_f frame_g p)
= fun frame ->
  let x = frame_aux f frame_f frame in
  frame_aux (g x) frame_g frame


(*
 * Note that the output is a framed computation, hence SteelF
 *)

polymonadic_bind (Steel, Steel) |> SteelF = bind_steel_steel


(*
 * Steel, SteelF: frame the first computation
 *)

unfold
let bind_steel_steelf_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_f:slprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` pre_g x))
: req_t (pre_f `star` frame_f)
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steel_steelf_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_f:slprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` pre_g x))
: ens_t (pre_f `star` frame_f) b post_g
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x `star` frame_f)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steel_steelf (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (req_g:(x:a -> req_t (pre_g x))) (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] p:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` pre_g x))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    (pre_f `star` frame_f)
    post_g
    (bind_steel_steelf_req req_f ens_f req_g frame_f p)
    (bind_steel_steelf_ens req_f ens_f ens_g frame_f p)
= fun frame ->
  let x = frame_aux f frame_f frame in
  (g x) frame


polymonadic_bind (Steel, SteelF) |> SteelF = bind_steel_steelf


(*
 * SteelF, Steel: frame the second computation
 *)

unfold
let bind_steelf_steel_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t)
  (req_g:(x:a -> req_t (pre_g x)))
  (frame_g:slprop)
  (_:squash (forall (x:a). post_f x `sl_implies` (pre_g x `star` frame_g)))
: req_t pre_f
= fun m0 ->
  req_f m0 /\
  (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_steelf_steel_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#pre_g:a -> pre_t) (#post_g:post_t b)
  (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (frame_g:slprop)
  (_:squash (forall (x:a). post_f x `sl_implies` (pre_g x `star` frame_g)))
: ens_t pre_f b (fun y -> post_g y `star` frame_g)
= fun m0 y m2 ->
  req_f m0 /\
  (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

let bind_steelf_steel (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)  
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (req_g:(x:a -> req_t (pre_g x))) (ens_g:(x:a -> ens_t (pre_g x) b post_g))
  (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (forall (x:a). post_f x `sl_implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f req_f ens_f)
  (g:(x:a -> repr b (pre_g x) post_g (req_g x) (ens_g x)))
: repr b
    pre_f
    (fun y -> post_g y `star` frame_g)
    (bind_steelf_steel_req req_f ens_f req_g frame_g p)
    (bind_steelf_steel_ens req_f ens_f ens_g frame_g p)
= fun frame ->
  let x = f frame in
  frame_aux (g x) frame_g frame


polymonadic_bind (SteelF, Steel) |> SteelF = bind_steelf_steel


(*
//  * SteelF, SteelF: no framing, use the effect bind
//  *)

(*
//  * PURE, Steel(F) bind
//  *)

assume WP_monotonic :
  forall (a:Type) (wp:pure_wp a).
    (forall p q. (forall x. p x ==>  q x) ==>  (wp p ==>  wp q))


(*
 * The indices of the second computation need not be dependent on a,
 * the result of the first computation, I think ...
 *
 * Since before bind is called, the typechecker has already substituted them
 * with the pure f computation
 *)

unfold
let bind_pure_steel__req (#a:Type) (wp:pure_wp a)
  (#pre:pre_t) (req:a -> req_t pre)
: req_t pre
= fun m -> wp (fun x -> (req x) m) /\ as_requires wp

unfold
let bind_pure_steel__ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre:pre_t) (#post:post_t b) (ens:a -> ens_t pre b post)
: ens_t pre b post
= fun m0 r m1 -> as_requires wp /\ (exists (x:a). as_ensures wp x /\ (ens x) m0 r m1)

let bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (req:a -> req_t pre) (ens:a -> ens_t pre b post)
  (f:eqtype_as_type unit -> PURE a wp) (g:(x:a -> repr b pre post (req x) (ens x)))
: repr b
    pre
    post
    (bind_pure_steel__req wp req)
    (bind_pure_steel__ens wp ens)
= fun frame ->
  let x = f () in
  (g x) frame

polymonadic_bind (PURE, SteelF) |> SteelF = bind_pure_steel_

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel_


(*
//  * subcomp relation from SteelF to Steel
//  *)

polymonadic_subcomp SteelF <: Steel = subcomp


(*
//  * Annotations without the req and ens
//  *)

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)


//scratch space


// (*
//  * How we would like to see the Steel(F)/PURE bind
//  *)

// unfold
// let bind_steel__pure_req (#a:Type) (#pre:pre_t) (#post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
//   (#b:Type) (wp:a -> pure_wp b)
// : req_t pre
// = fun m0 -> req m0 /\ (forall (x:a) (m1:hmem (post x)). ens m0 x m1 ==> as_requires (wp x))

// // unfold
// // let bind_steel__pure_ens (#a:Type) (#pre:pre_t) (#post:post_t a) (req:req_t pre) (ens:ens_t pre a post)
// //   (#b:Type) (wp:a -> pure_wp b) (f:(x:a -> unit -> PURE b (wp x)))
// // : ens_t pre b (fun _ -> post)
// // = fun m0 r m1 ->



// (*
// //  * No Steel(F), PURE bind
// //  *
// //  * Use the steel_ret function below to return the PURE computation
// //  *
// //  * Note it is in SteelF (i.e. framed already)
// //  *)
// let steel_ret (#a:Type) (#[@@ framing_implicit] p:a -> slprop u#1) (x:a)
// : SteelF a (p x) p (fun _ -> True) (fun _ r _ -> r == x)
// = SteelF?.reflect (fun _ -> x)
