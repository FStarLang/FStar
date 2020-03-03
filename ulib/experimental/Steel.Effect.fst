(*
   Copyright 2019 Microsoft Research

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

module Steel.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module Act = Steel.Actions

open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

open Steel.Memory

#set-options "--print_implicits --print_universes"

let join_preserves_interp (hp:hprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)


let ens_depends_only_on (#a:Type) (pre:Mem.hprop) (post:a -> Mem.hprop)
  (q:(hmem pre -> x:a -> hmem (post x) -> prop))

= //can join any disjoint heap to the pre-heap and q is still valid
  (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
     q h_pre x h_post <==> q (join h_pre h) x h_post) /\  //at this point we need to know interp pre (join h_pre h) -- use join_preserves_interp for that

  //can join any disjoint heap to the post-heap and q is still valid
  (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
     q h_pre x h_post <==> q h_pre x (join h_post h))

type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1
type req_t (pre:pre_t) = q:(hmem pre -> prop){
  forall (m0:hmem pre) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)
}

type ens_t (pre:pre_t) (a:Type u#a) (post:post_t u#a a) : Type u#(max 2 a) =
  q:(hmem pre -> x:a -> hmem (post x) -> prop){
    ens_depends_only_on pre post q
  }

#push-options "--warn_error -271"
let interp_depends_only_on_post (#a:Type) (hp:a -> hprop)
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

type repr (a:Type u#a) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post
    (req_to_act_req req)
    (ens_to_act_ens ens)

unfold
let return_req (p:hprop) : req_t p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> hprop) : ens_t (p x) a p = fun _ r _ -> r == x

let returnc (a:Type u#a) (x:a) (p:a -> hprop)
: repr a (p x) p (return_req (p x)) (return_ens x p)
= fun _ -> x

unfold
let bind_req (#a:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (req_g:(x:a -> req_t (post_f x)))
: req_t pre_f
= fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#post_g:post_t b) (ens_g:(x:a -> ens_t (post_f x) b post_g))
: ens_t pre_f b post_g
= fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2)

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g
    (bind_req req_f ens_f req_g)
    (bind_ens req_f ens_f ens_g)
= fun m0 ->
  let x = f () in
  g x ()

unfold
let subcomp_pre (#a:Type) (#pre:pre_t) (#post:post_t a)
  (req_f:req_t pre) (ens_f:ens_t pre a post)
  (req_g:req_t pre) (ens_g:ens_t pre a post)
: pure_pre
= (forall h. req_g h ==> req_f h) /\
  (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1)

let subcomp (a:Type) (pre:pre_t) (post:post_t a)
  (req_f:req_t pre) (ens_f:ens_t pre a post)
  (req_g:req_t pre) (ens_g:ens_t pre a post)
  (f:repr a pre post req_f ens_f)
: Pure (repr a pre post req_g ens_g)
  (requires subcomp_pre req_f ens_f req_g ens_g)
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

let if_then_else (a:Type) (pre:pre_t) (post:post_t a)
  (req_then:req_t pre) (ens_then:ens_t pre a post)
  (req_else:req_t pre) (ens_else:ens_t pre a post)
  (f:repr a pre post req_then ens_then)
  (g:repr a pre post req_else ens_else)
  (p:Type0)
: Type
= repr a pre post
    (if_then_else_req req_then req_else p)
    (if_then_else_ens ens_then ens_else p)

reflectable
layered_effect {
  Steel : a:Type -> pre:pre_t -> post:post_t a -> req:req_t pre -> ens:ens_t pre a post -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

assume WP_monotonic_pure:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall x. p x ==> q x) ==>
       (wp p ==> wp q))

unfold
let bind_pure_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True)

unfold
let bind_pure_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (bind_pure_steel_req wp req_g)
    (bind_pure_steel_ens wp ens_g)
= fun m0 ->
  let x = f () in
  g x m0
#pop-options

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel

#push-options "--warn_error -271"
unfold
let polymonadic_bind_steel_pure_pre (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
: req_t pre_f
= let aux (m0:hmem pre_f) (m1:mem{disjoint m0 m1})
    : Lemma
      (requires
        forall (x:a) (h1:hmem post_f). ens_f (join m0 m1) x h1 ==> (wp_g x) (fun _ -> True))
      (ensures
        forall (x:a) (h1:hmem post_f). ens_f m0 x h1 ==> (wp_g x) (fun _ -> True))
      [SMTPat ()]
    = assert (forall (x:a) (h1:hmem post_f). ens_f m0 x h1 <==> ens_f (join m0 m1) x h1) in
  fun h -> req_f h /\ (forall (x:a) (h1:hmem post_f). ens_f h x h1 ==> (wp_g x) (fun _ -> True))
#pop-options

unfold
let polymonadic_bind_steel_pure_post
  (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:Mem.hprop) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
: ens_t pre_f b (fun _ -> post_f)
= fun h0 r h1 -> exists x. (ens_f h0 x h1 /\ (~ ((wp_g x) (fun y -> y =!= r))))

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let bind_steel_pure (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
  (f:repr a pre_f (fun _ -> post_f) req_f ens_f) (g:(x:a -> unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
    (polymonadic_bind_steel_pure_pre req_f ens_f wp_g)
    (polymonadic_bind_steel_pure_post ens_f wp_g)
= fun _ ->
  let x = f () in
  g x ()
#pop-options

polymonadic_bind (Steel, PURE) |> Steel = bind_steel_pure


// let return_emp (#a:Type) (x:a)
// : Steel a Mem.emp (fun _ -> Mem.emp) (fun _ -> True) (fun _ r _ -> r == x)
// = Steel?.reflect (returnc a x)

assume val steel_reify (#a:Type) (#pre:pre_t) (#post:post_t a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
: repr a pre post req ens

(*
 * This proof relies on core_mem_interp lemma from Steel.Memory
 *)
let par0 (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  (f:repr aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  (g:repr aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= Steel?.reflect (fun _ -> Sem.run #state #_ #_ #_ #_ #_ (Sem.Par (Sem.Act f) (Sem.Act g)))

(*
 * We need affine_star_smt even to typecheck the signature
 *)
let par (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  ($f:unit -> Steel aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  ($g:unit -> Steel aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= par0 (steel_reify f) (steel_reify g)

let frame0 (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  (f:repr a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:mprop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= Steel?.reflect (fun _ -> Sem.run #state #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame f_frame))

let steel_frame (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:mprop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= frame0 (steel_reify f) frame f_frame

(*** Lifting actions to MST and then to Steel ***)

open Steel.Actions

(**** Specialize to trivial req and ens ****)

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)

(*
 * We are going to work with instiation of MSTATE with mem and mem_evolves
 *
 * Define abbreviations to ease the implicit inference for them
*)

effect Mst (a:Type) (req:mem -> Type0) (ens:mem -> a -> mem -> Type0) =
  RMST.RMSTATE a mem mem_evolves req ens

let mst_get ()
: Mst mem (fun _ -> True) (fun m0 r m1 -> m0 == r /\ r == m1)
= RMST.get ()

let mst_put (m:mem)
: Mst unit (fun m0 -> mem_evolves m0 m) (fun _ _ m1 -> m1 == m)
= RMST.put m

let mst_assume (p:Type)
: Mst unit (fun _ -> True) (fun m0 _ m1 -> p /\ m0 == m1)
= RMST.rmst_assume p

let mst_admit (#a:Type) ()
: Mst a (fun _ -> True) (fun _ _ _ -> False)
= RMST.rmst_admit ()

let mst_assert (p:Type)
: Mst unit (fun _ -> p) (fun m0 _ m1 -> p /\ m0 == m1)
= RMST.rmst_assert p

let intro_emp_left (p1 p2:hprop) (m:mem)
: Lemma
  (requires interp (p1 `star` p2) m)
  (ensures interp ((p1 `star` emp) `star` p2) m)
= emp_unit p1;
  equiv_symmetric (p1 `star` emp) p1;
  equiv_extensional_on_star p1 (p1 `star` emp) p2

let act_preserves_frame_and_preorder
  (#a:Type)
  (#pre:hprop)
  (#post:a -> hprop)
  (act:m_action pre a post)
  (m0:hmem_with_inv pre)
: Lemma
  (let (| x, m1 |) = act m0 in
   Sem.preserves_frame #state pre (post x) m0 m1 /\
   mem_evolves m0 m1)
= let (| x, m1 |) = act m0 in
  let frame : hprop = emp in
  intro_emp_left pre (locks_invariant Set.empty m0) m0;
  let m0 : hmem_with_inv (pre `star` emp) = m0 in  //instantiate the quantifier in is_m_frame_preserving
  ()

module G = FStar.Ghost
module P = FStar.Preorder

#push-options "--z3rlimit 50"
let read (#a:Type) (#pre:P.preorder a) (r:reference a pre) (p:perm{readable p})
: Steel a (ref_perm r p) (fun x -> pts_to_ref r p x)
    (fun _ -> True) (fun _ _ _ -> True)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let act = promote_atomic_m_action (get_ref Set.empty r p) in
    let (| x, m1 |) = act m0 in
    act_preserves_frame_and_preorder act m0;
    mst_put m1;
    mst_assume (interp (ref_perm r p) m1);
    sel_ref_lemma r p m1;
    pts_to_ref_injective r p x (sel_ref r m1) m1;
    mst_assert (x == sel_ref r m1);
    x)
#pop-options

let read_refine
  (#a:Type)
  (#pre:P.preorder a)
  (q:a -> hprop)
  (r:reference a pre)
  (p:perm{readable p})
: Steel a (h_exists (fun (v:a) -> pts_to_ref r p v `star` q v))
          (fun v -> pts_to_ref r p v `star` q v)
          (fun _ -> True) (fun _ _ _ -> True)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let act = promote_atomic_m_action (get_ref_refine Set.empty r p q) in
    let (| x, m1 |) = act m0 in
    act_preserves_frame_and_preorder act m0;
    mst_put m1;
    x)

let write (#a:Type) (#pre:P.preorder a) (r:reference a pre) (curr:G.erased a) (x:a{pre curr x})
: Steel unit (pts_to_ref r full_perm curr) (fun _ -> pts_to_ref r full_perm x)
    (fun _ -> True) (fun _ _ _ -> True)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let act = promote_atomic_m_action (set_ref Set.empty r curr x) in
    let (| _, m1 |) = act m0 in
    act_preserves_frame_and_preorder act m0;
    mst_put m1)


// let alloc (#a:Type0) (x:a)
// : SteelT (reference a) emp (fun r -> pts_to_ref r full_perm x)
// = Steel?.reflect (fun _ ->
//     let m0 = mst_get () in
//     let (| r, m1 |) = alloc_ref #a x m0 in
//     act_preserves_frame_and_preorder (alloc_ref #a x) m0;
//     mst_put m1;
//     r)


// let free (#a:Type0) (r:reference a)
// : SteelT unit (ref_perm r full_perm) (fun _ -> emp)
// = Steel?.reflect (fun _ ->
//     let m0 = mst_get () in
//     let (| _, m1 |) = free_ref r m0 in
//     act_preserves_frame_and_preorder (free_ref r) m0;
//     mst_put m1)


// assume val upd (#a:Type) (r:ref a) (prev:a) (v:a)
// : Steel unit (pts_to r full_perm prev) (fun _ -> pts_to r full_perm v)
//     (fun _ -> True) (fun _ _ _ -> True)

// assume val alloc (#a:Type) (v:a)
// : Steel (ref a) emp (fun x -> pts_to x full_perm v)
//     (fun _ -> True) (fun _ _ _ -> True)

// assume val return (#a:Type) (#hp:a -> hprop) (x:a)
// : Steel a (hp x) hp (fun _ -> True) (fun _ r _ -> r == x)


// let alloc_and_upd (n:int)
// : Steel (ref int) emp (fun x -> pts_to x full_perm (n+1))
//     (fun _ -> True) (fun _ _ _ -> True)
// = let r = alloc n in
//   upd r n (n+1);
//   return r


// let ( || ) (#aL:Type) (#preL:pre_t) (#postL:post_t aL)
//   ($f:unit -> SteelT aL preL postL)
//   (#aR:Type) (#preR:pre_t) (#postR:post_t aR)
//   ($g:unit -> SteelT aR preR postR)
// : SteelT (aL & aR)
//   (preL `Mem.star` preR)
//   (fun (xL, xR) -> postL xL `Mem.star` postR xR)
// = par f g

// let incr (r:ref int) (prev:int) ()
// : SteelT unit (pts_to r full_perm prev) (fun _ -> pts_to r full_perm (prev+1))
// = upd r prev (prev+1)

// let incr2 (r1 r2:ref int) (prev1 prev2:int)
// : SteelT (unit & unit)
//   (pts_to r1 full_perm prev1 `star` pts_to r2 full_perm prev2)
//   (fun _ -> pts_to r1 full_perm (prev1+1) `star` pts_to r2 full_perm (prev2+1))
// = incr r1 prev1 || incr r2 prev2


(*** Small examples for frame inference ***)

open Steel.Memory.Tactics

#push-options "--no_tactics"

let rassert
  (#h_in:hprop)
  (h_out:hprop{
    FStar.Tactics.with_tactic
    reprove_frame
    (can_be_split_into h_in h_out emp /\ True)})
  : SteelT unit h_in (fun _ -> h_out)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into h_in h_out emp /\ True);
      let (| _, m1 |) = rewrite_hprop h_in h_out m0 in
      act_preserves_frame_and_preorder (rewrite_hprop h_in h_out) m0;
      mst_put m1)

(*
let steel_frame_t
  (#outer:hprop)
  (#a:Type) (#pre:pre_t) (#post:post_t a)
  (#[resolve_frame()]
    frame:hprop{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer pre frame /\ True)}
  )
  ($f:unit -> Steel a pre post (fun _ -> True) (fun _ _ _ -> True))
: SteelT a
  outer
  (fun x -> post x `Mem.star` frame)
= FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into outer pre frame /\ True);
  Mem.emp_unit (pre `Mem.star` frame);
  FStar.Tactics.unfold_with_tactic reprove_frame
    (can_be_split_into outer (pre `Mem.star` frame) emp /\ True);
  rassert (pre `Mem.star` frame);
  steel_frame f frame (fun _ -> True)
*)
#pop-options

assume val r1 : hprop
assume val r2 : hprop
assume val r3 : hprop

assume val f1 (_:unit) : SteelT unit r1 (fun _ -> r1)
assume val f12 (_:unit) : SteelT unit (r1 `star` r2) (fun _ -> r1 `star` r2)
assume val f123 (_:unit) : SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)

module T = FStar.Tactics

(*
let test_frame1 (_:unit)
: SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)
= steel_frame_t f12;
  steel_frame_t f1;
  steel_frame_t f123;
  steel_frame_t f1;
  rassert ((r1 `star` r2) `star` r3)
*)

(*
 * A crash testcase
 *)

#push-options "--admit_smt_queries true"
assume
val crash_h_commute (p:hprop)
  : SteelT unit emp (fun _ -> p)

assume
val crash_h_assert (_:unit)
  : SteelT unit emp (fun _ -> emp)

assume val crash_get_prop : int -> hprop

let crash_test (_:unit)
  : SteelT unit emp (fun _ -> emp)
  = let r = 0 in
    crash_h_commute (crash_get_prop r);
    crash_h_assert ()
#pop-options

let cond_aux (#a:Type) (b:bool) (p: bool -> hprop) (q: bool -> a -> hprop)
  (then_:unit -> Steel a (p b) (q b) (fun _ -> b==true) (fun _ _ _ -> True))
  (else_:unit -> Steel a (p b) (q b) (fun _ -> b==false) (fun _ _ _ -> True))
: SteelT a (p b) (q b)
= if b then then_ () else else_ ()


let aux1 (#a:Type) (b:bool{b == true}) (p: bool -> hprop) (q: bool -> a -> hprop)
  (then_: (unit -> SteelT a (p true) (q true)))
: unit -> SteelT a (p b) (q b)
= fun _ -> then_ ()

let aux2 (#a:Type) (b:bool) (p: bool -> hprop) (q: bool -> a -> hprop)
  (then_: (unit -> SteelT a (p true) (q true)))
: unit -> Steel a (p b) (q b) (fun _ -> b == true) (fun _ _ _ -> True)
= fun _ -> (aux1 b p q then_) ()

let aux3 (#a:Type) (b:bool{b == false}) (p: bool -> hprop) (q: bool -> a -> hprop)
  (else_: (unit -> SteelT a (p false) (q false)))
: unit -> SteelT a (p b) (q b)
= fun _ -> else_ ()

let aux4 (#a:Type) (b:bool) (p: bool -> hprop) (q: bool -> a -> hprop)
  (else_: (unit -> SteelT a (p false) (q false)))
: unit -> Steel a (p b) (q b) (fun _ -> b == false) (fun _ _ _ -> True)
= fun _ -> (aux3 b p q else_) ()


let cond (#a:Type) (b:bool) (p: bool -> hprop) (q: bool -> a -> hprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
: SteelT a (p b) (q b)
= let a1 = aux2 b p q then_ in
  let a2 = aux4 b p q else_ in
  cond_aux b p q a1 a2
