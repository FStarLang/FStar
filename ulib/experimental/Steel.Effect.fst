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

#set-options "--print_implicits --print_universes"

let mem_affine_star_smt (p q:Mem.hprop) (m:Mem.heap)
: Lemma (Mem.interp (p `Mem.star` q) m ==> Mem.interp p m /\ Mem.interp q m)
  [SMTPat (Mem.interp (p `Mem.star` q) m)]
= Mem.affine_star p q m

let interp_join_smt (p:Mem.hprop) (h0:Mem.hheap p) (h1:Mem.heap)
: Lemma
  (requires Mem.disjoint h0 h1)
  (ensures Mem.interp p (Mem.join h0 h1))
  [SMTPat (Mem.interp p (Mem.join h0 h1))]
= admit ()

let ens_depends_only_on (#a:Type) (pre:Mem.hprop) (post:a -> Mem.hprop)
  (q:(Mem.hheap pre -> x:a -> Mem.hheap (post x) -> prop))

= //can join any disjoint heap to the pre-heap and q is still valid
  (forall x (h_pre:Mem.hheap pre) h_post (h:Mem.heap{Mem.disjoint h_pre h}).
     q h_pre x h_post <==> q (Mem.join h_pre h) x h_post) /\

  //can join any disjoint heap to the post-heap and q is still valid
  (forall x h_pre (h_post:Mem.hheap (post x)) (h:Mem.heap{Mem.disjoint h_post h}).
     q h_pre x h_post <==> q h_pre x (Mem.join h_post h))

// type fp_prop (pre:Mem.hprop) = q:(Mem.hheap pre -> prop){
//   forall (h0:Mem.hheap pre) (h1:Mem.heap{Mem.disjoint h0 h1}). q h0 <==> q (Mem.join h0 h1)
// }

type pre_t = Mem.hprop
type post_t (a:Type) = a -> Mem.hprop
type req_t (pre:Mem.hprop) = q:(Mem.hheap pre -> prop){
  forall (h0:Mem.hheap pre) (h1:Mem.heap{Mem.disjoint h0 h1}). q h0 <==> q (Mem.join h0 h1)
}
#set-options "--print_universes --print_implicits --ugly"
type ens_t (pre:pre_t) (a:Type u#a) (post:post_t a) =
  q:(Mem.hheap pre -> x:a -> Mem.hheap (post x) -> prop){ens_depends_only_on pre post q}

type repr (a:Type u#a) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post
    (fun h0 -> Mem.interp pre h0 /\ req h0)
    (fun h0 x h1 ->
      Mem.interp pre h0 /\
      Mem.interp (post x) h1 /\
      ens h0 x h1)

let returnc (a:Type u#a) (x:a)
: repr a Mem.emp (fun _ -> Mem.emp) (fun _ -> True) (fun _ r _ -> r == x)
= fun _ -> x

#push-options "--z3rlimit 50"
let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b post_g))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g
    (fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1))
    (fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2))
= fun m0 ->
  let x = f () in
  g x ()
#pop-options

let subcomp (a:Type) (pre:pre_t) (post:post_t a)
  (req_f:req_t pre) (ens_f:ens_t pre a post)
  (req_g:req_t pre) (ens_g:ens_t pre a post)
  (f:repr a pre post req_f ens_f)
: Pure (repr a pre post req_g ens_g)
  (requires
    (forall h. req_g h ==> req_f h) /\
    (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1))
  (ensures fun _ -> True)
= f

let if_then_else (a:Type) (pre:pre_t) (post:post_t a)
  (req_then:req_t pre) (ens_then:ens_t pre a post)
  (req_else:req_t pre) (ens_else:ens_t pre a post)
  (f:repr a pre post req_then ens_then)
  (g:repr a pre post req_else ens_else)
  (p:Type0)
: Type
= repr a pre post
    (fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h))
    (fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1))

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

let bind_pure_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:unit -> PURE a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True))
    (fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1))
= fun m0 ->
  let x = f () in
  g x m0

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel

unfold
let polymonadic_bind_steel_pure_pre (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
: req_t pre_f
= // assert (forall x (h0:Mem.hheap pre_f) h1 (h2:Mem.heap{Mem.disjoint h0 h2}).
  //           ens_f h0 x h1 <==> ens_f (Mem.join h0 h2) x h1);
  // assert (forall x h1 (h0:Mem.hheap pre_f) (h2:Mem.heap{Mem.disjoint h0 h2}).
  //         (ens_f h0 x h1 ==> p) <==> (ens_f (Mem.join h0 h2) x h1 ==> p));
  admit ();          
  fun h -> req_f h /\ (forall x h1. ens_f h x h1 ==> (wp_g x) (fun _ -> True))

let bind_steel_pure (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:Mem.hprop) (req_f:req_t pre_f) (ens_f:ens_t pre_f a (fun _ -> post_f))
  (wp_g:a -> pure_wp b)
  (f:repr a pre_f (fun _ -> post_f) req_f ens_f) (g:(x:a -> unit -> PURE b (wp_g x)))
: repr b pre_f (fun _ -> post_f)
    (polymonadic_bind_steel_pure_pre req_f ens_f wp_g)
    (fun h0 r h1 -> exists x. ens_f h0 x h1 /\ (~ ((wp_g x) (fun y -> y =!= r))))
= fun m0 ->
  let x = f () in
  g x ()


polymonadic_bind (Steel, PURE) |> Steel = bind_steel_pure


// let return_emp (#a:Type) (x:a)
// : Steel a Mem.emp (fun _ -> Mem.emp) (fun _ -> True) (fun _ r _ -> r == x)
// = Steel?.reflect (returnc a x)

assume val steel_reify (#a:Type) (#pre:pre_t) (#post:post_t a)
  (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
: repr a pre post req ens

#push-options "--z3rlimit 100"
let par0 (#aL:Type) (#preL:pre_t) (#postL:post_t aL) (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
  (f:repr aL preL postL lpreL lpostL)
  (#aR:Type) (#preR:pre_t) (#postR:post_t aR) (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
  (g:repr aR preR postR lpreR lpostR)
: Steel (aL & aR)
  (preL `Mem.star` preR)
  (fun (xL, xR) -> postL xL `Mem.star` postR xR)
  (fun h -> lpreL h /\ lpreR h)
  (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
= Steel?.reflect (fun _ -> Sem.run #state 0 #_ #_ #_ #_ #_ (Sem.Par (Sem.Act f) (Sem.Act g)))
#pop-options

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

type fp_prop (hp:Mem.hprop) =
  q:(Mem.heap -> prop){q `Act.depends_only_on_without_affinity` hp}

#push-options "--z3rlimit 100"
let frame0 (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  (f:repr a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:fp_prop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= Steel?.reflect (fun _ -> Sem.run #state 0 #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame f_frame))
#pop-options

let steel_frame (#a:Type) (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:unit -> Steel a pre post req ens)
  (frame:Mem.hprop)
  (f_frame:fp_prop frame)
: Steel a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
  (fun h -> req h /\ f_frame h)
  (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
= frame0 (steel_reify f) frame f_frame

(*** Small examples for frame inference ***)

(**** Specialize to trivial req and ens ****)

open Steel.Memory

effect SteelT (a:Type) (pre:pre_t) (post:post_t a) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)


let steel_frame_t (#a:Type) (#pre:pre_t) (#post:post_t a)
  ($f:unit -> Steel a pre post (fun _ -> True) (fun _ _ _ -> True))
  (frame:hprop)
: SteelT a
  (pre `Mem.star` frame)
  (fun x -> post x `Mem.star` frame)
= steel_frame f frame (fun _ -> True)


assume val r1 : hprop
assume val r2 : hprop
assume val r3 : hprop


assume val f1 (_:unit) : SteelT unit r1 (fun _ -> r1)
assume val f12 (_:unit) : SteelT unit (r1 `star` r2) (fun _ -> r1 `star` r2)
assume val f123 (_:unit) : SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)

[@expect_failure]
let test_frame1 (_:unit)
: SteelT unit ((r1 `star` r2) `star` r3) (fun _ -> (r1 `star` r2) `star` r3)
= steel_frame_t f12 _;  //this succeeds, simple unification
  steel_frame_t f1 _  //this fails to infer frame


(**** How we were framing framing earlier ****)

let can_be_split_into (p q r:hprop) = equiv p (q `star` r)

let star_can_be_split_into0 (p q:hprop)
: Lemma (can_be_split_into (p `star` q) p q)
  [SMTPat (can_be_split_into (p `star` q) p q)]
= ()

let star_can_be_split_into1 (p q:hprop)
: Lemma (can_be_split_into (p `star` q) q p)
  [SMTPat (can_be_split_into (p `star` q) q p)]
= star_commutative p q

let can_be_split_into_emp_left (p:hprop)
: Lemma (can_be_split_into p emp p)
  [SMTPat (can_be_split_into p emp p)]
= star_commutative p emp;
  emp_unit p

let can_be_split_into_emp_right (p:hprop)
: Lemma (can_be_split_into p p emp)
  [SMTPat (can_be_split_into p p emp)]
= emp_unit p


assume val steel_frame_delta (#a:Type)
  (outer0:hprop) (#inner0:hprop)
  (#inner1:a -> hprop)
  (outer1:a -> hprop)
  (delta:hprop{
    can_be_split_into outer0 inner0 delta /\
    (forall x. can_be_split_into (outer1 x) (inner1 x) delta)})
  (#req:req_t inner0) (#ens:ens_t inner0 a inner1)
  ($f:unit -> Steel a inner0 inner1 req ens)
: Steel a outer0 outer1 req ens


(*** Lifting actions to MST and then to Steel ***)

open Steel.Permissions
open Steel.Actions


(*
 * We are going to work with instiation of MSTATE with mem and mem_evolves
 *
 * Define abbreviations to ease the implicit inference for them
 *)


effect Mst (a:Type) (req:mem -> Type0) (ens:mem -> a -> mem -> Type0) =
  MST.MSTATE a mem mem_evolves req ens

let mst_get ()
: Mst mem (fun _ -> True) (fun m0 r m1 -> m0 == r /\ r == m1)
= MST.get ()

let mst_put (m:mem)
: Mst unit (fun m0 -> mem_evolves m0 m) (fun _ _ m1 -> m1 == m)
= MST.put m

let mst_assume (p:Type)
: Mst unit (fun _ -> True) (fun m0 _ m1 -> p /\ m0 == m1)
= MST.mst_assume p

let mst_admit (#a:Type) ()
: Mst a (fun _ -> True) (fun _ _ _ -> False)
= MST.mst_admit ()

let mst_assert (p:Type)
: Mst unit (fun _ -> p) (fun m0 _ m1 -> p /\ m0 == m1)
= MST.mst_assert p

#push-options "--z3rlimit 50"
let act_preserves_frame_and_preorder (#a:Type) (#pre:hprop) (#post:a -> hprop) (act:m_action pre a post)
  (m0:hmem pre)
: Lemma
  (let (| x, m1 |) = act m0 in
   Sem.preserves_frame #state pre (post x) m0 m1 /\
   mem_evolves m0 m1)
= ()
#pop-options

module G = FStar.Ghost

let pts_to_implies_ref_perm (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:G.erased a)
  (h:heap)
: Lemma
  (requires interp (pts_to_ref r p x) h)
  (ensures interp (ref_perm r p) h)
  [SMTPat (interp (pts_to_ref r p x) h)]
= admit ()

let pts_to_implies_ref (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:G.erased a)
  (h:heap)
: Lemma
  (requires interp (pts_to_ref r p x) h)
  (ensures interp (ref r) h)
  [SMTPat (interp (pts_to_ref r p x) h)]
= admit ()

let ref_perm_implies_ref (#a:Type0) (r:reference a) (p:permission{allows_read p})
  (h:heap)
: Lemma
  (requires interp (ref_perm r p) h)
  (ensures interp (ref r) h)
  [SMTPat (interp (ref_perm r p) h)]
= admit ()

let sel_ref_depends_only_on (#a:Type0) (r:reference a) (x:G.erased a) (p:permission{allows_read p}) (h:hheap (pts_to_ref r p x)) (h1:heap{disjoint h h1})
: Lemma
  ((sel_ref r h == G.reveal x) <==> (sel_ref r (join h h1) == G.reveal x))
  [SMTPat (sel_ref r (join h h1)); SMTPat (pts_to_ref r p x)]
= admit ()

let sel_ref_depends_only_on_ref_perm (#a:Type0) (r:reference a) (p:permission{allows_read p}) (h:hheap (ref_perm r p)) (h1:heap{disjoint h h1})
: Lemma
  (forall x. (sel_ref r h == x) <==> (sel_ref r (join h h1) == x))
  [SMTPat (sel_ref r (join h h1)); SMTPat (ref_perm r p)]
= admit ()

assume val weaken
  (#a:Type0)
  (#pre1:hprop) (#post1:a -> hprop) (#req1:req_t pre1)(#ens1:ens_t pre1 a post1)
  (#pre2:hprop{forall h. interp pre2 h ==> interp pre1 h})
  (#post2:(a -> hprop){forall x h. interp (post1 x) h ==> interp (post2 x) h})
  (#req2:req_t pre2{forall (h:hheap pre2). req2 h ==> req1 h})
  (#ens2:ens_t pre2 a post2{forall (h0:hheap pre2) (x:a) (h1:hheap (post1 x)). ens1 h0 x h1 ==> ens2 h0 x h1})
  ($f:unit -> Steel a pre1 post1 req1 ens1)
: Steel a pre2 post2 req2 ens2


let read (#a:Type0) (r:reference a) (p:permission{allows_read p})
: Steel a
    (ref_perm r p) (fun x -> pts_to_ref r p (G.hide x))
    (fun _ -> True)
    (fun _ x m1 -> sel_ref r m1 == x)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let (| x, m1 |) = get_ref r p m0 in
    act_preserves_frame_and_preorder (get_ref r p) m0;
    pts_to_implies_ref_perm r p x (heap_of_mem m1);
    sel_ref_lemma a p r (heap_of_mem m1);
    pts_to_ref_injective r p (sel_ref r (heap_of_mem m1)) x (heap_of_mem m1);
    mst_put m1;
    x)

let read0 (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:G.erased a)
: Steel a
    (pts_to_ref r p x) (fun x -> pts_to_ref r p (G.hide x))
    (fun _ -> True)
    (fun _ _ _ -> True)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    mst_assume (interp (ref_perm r p `star` locks_invariant m0) (heap_of_mem m0));
    let (| x, m1 |) = get_ref r p m0 in
    act_preserves_frame_and_preorder (get_ref r p) m0;
    mst_put m1;
    mst_admit ();
    x)

let read_s (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:G.erased a)
: unit -> Steel a (pts_to_ref r p x) (fun x -> pts_to_ref r p (G.hide x)) (fun _ -> True) (fun _ _ _ -> True)
= fun _ -> weaken (fun _ -> read r p)

let write (#a:Type0) (r:reference a) (x:a)
: Steel unit (ref_perm r full_permission) (fun _ -> pts_to_ref r full_permission x)
    (fun _ -> True)
    (fun _ _ m1 -> sel_ref r m1 == x)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let (| _, m1 |) = set_ref r x m0 in
    act_preserves_frame_and_preorder (set_ref r x) m0;
    sel_ref_lemma a full_permission r (heap_of_mem m1);
    pts_to_ref_injective r full_permission (sel_ref r (heap_of_mem m1)) x (heap_of_mem m1);
    mst_put m1)

let one_ref (#a:Type0) (r:reference a) (x:G.erased a) : hprop = pts_to_ref r full_permission x

let two_refs (#a:Type0) (r1 r2:reference a) (x1 x2:G.erased a) : hprop =
  pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2

let read_two (#a:Type0) (r1 r2:reference a) (x1 x2:G.erased a)
: SteelT a
  (two_refs r1 r2 x1 x2)
  (fun x2 -> two_refs r1 r2 x1 (G.hide x2))
= 
  let _ = steel_frame_delta
    (two_refs r1 r2 x1 x2)
    (fun x1 -> two_refs r1 r2 (G.hide x1) x2)
    (one_ref r2 x2)
    (read_s r1 full_permission x1) in
  steel_frame_delta
    (two_refs r1 r2 x1 x2)
    (fun x2 -> two_refs r1 r2 x1 (G.hide x2))
    (one_ref r1 x1)
    (read_s r2 full_permission x2)

  
  steel_frame_delta
    (two_refs r1 r2 x1 x2)
    (two_refs r1 r2 x1 x2)
    (one_ref r1 x1)
    (fun _ -> read_s r2 full_permission x2)

let swap (#a:Type0) (r1 r2:reference a) (x1 x2:Ghost.erased a)
: Steel unit
  (pts_to_ref r1 full_permission (G.reveal x1) `star` pts_to_ref r2 full_permission (G.reveal x2))
  (fun _ -> pts_to_ref r1 full_permission (G.reveal x2) `star` pts_to_ref r2 full_permission (G.reveal x1))
  (fun _ -> True) (fun _ _ _ -> True)
= let x1 = steel_frame_delta
    (pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2)  
    (fun _ -> pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2)
    (pts_to_ref r2 full_permission x2)
    (fun _ -> read_s r1 full_permission x1) in
  let x2 = steel_frame_delta
    (pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2)  
    (fun _ -> pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2)
    (pts_to_ref r1 full_permission x1)
    (fun _ -> read_s r2 full_permission x2) in
  steel_frame
    (pts_to_ref r1 full_permission x1 `star` pts_to_ref r2 full_permission x2)  
    (fun _ -> pts_to_ref r1 full_permission x2 `star` pts_to_ref r2 full_permission x2)
    (pts_to_ref r2 full_permission x2)
    (fun _ -> write r1 x2);
  steel_frame
    (pts_to_ref r1 full_permission x2 `star` pts_to_ref r2 full_permission x2)  
    (fun _ -> pts_to_ref r1 full_permission x2 `star` pts_to_ref r2 full_permission x1)
    (pts_to_ref r1 full_permission x2)
    (fun _ -> write r2 x1)


let read_w (#a:Type0) (r:reference a) (p:permission{allows_read p})
: Steel a
  (ref_perm r p) (fun _ -> ref_perm r p)
  (fun _ -> True)
  (fun _ x m1 -> sel_ref r m1 == x)
= weaken (fun _ -> read r p)



let write_w (#a:Type0) (r:reference a) (x:a)
: Steel unit
  (ref_perm r full_permission) (fun _ -> ref_perm r full_permission)
  (fun _ -> True)
  (fun _ _ m1 -> sel_ref r m1 == x)
= weaken (fun _ -> write r x)


let swap (#a:Type0) (r1 r2:reference a)
: Steel unit
  (ref_perm r1 full_permission `star` ref_perm r2 full_permission)
  (fun _ -> ref_perm r1 full_permission `star` ref_perm r2 full_permission)
  (fun _ -> True)
  (fun m0 _ m1 -> sel_ref r1 m1 == sel_ref r2 m0 /\ sel_ref r2 m1 == sel_ref r1 m0)
= 


let alloc (#a:Type0) (x:a)
: SteelT (reference a) emp (fun r -> pts_to_ref r full_permission x)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let (| r, m1 |) = alloc_ref #a x m0 in
    act_preserves_frame_and_preorder (alloc_ref #a x) m0;
    mst_put m1;
    r)
    

let free (#a:Type0) (r:reference a)
: SteelT unit (ref_perm r full_permission) (fun _ -> emp)
= Steel?.reflect (fun _ ->
    let m0 = mst_get () in
    let (| _, m1 |) = free_ref r m0 in
    act_preserves_frame_and_preorder (free_ref r) m0;
    mst_put m1)

let writable (#a:Type) (r:reference a) (x:a) = pts_to_ref r full_permission x

let swap (#a:Type0) (r1 r2:reference a) (x1 x2:a)
: SteelT unit (writable r1 x1 `star` writable r2 x2) (fun _ -> writable r1 x2 `star` writable r2 x2)
= steel_frame_delta #unit
    (writable r1 x1 `star` writable r2 x2)
    #(writable r1 x1)
    #(fun _ -> writable r1 x2)
    (fun _ -> writable r1 x2 `star` writable r2 x2)
    (writable r2 x2)
    (fun _ -> write r1 x2)



// assume val upd (#a:Type) (r:ref a) (prev:a) (v:a)
// : Steel unit (pts_to r full_permission prev) (fun _ -> pts_to r full_permission v)
//     (fun _ -> True) (fun _ _ _ -> True)

// assume val alloc (#a:Type) (v:a)
// : Steel (ref a) emp (fun x -> pts_to x full_permission v)
//     (fun _ -> True) (fun _ _ _ -> True)

// assume val return (#a:Type) (#hp:a -> hprop) (x:a)
// : Steel a (hp x) hp (fun _ -> True) (fun _ r _ -> r == x)


// let alloc_and_upd (n:int)
// : Steel (ref int) emp (fun x -> pts_to x full_permission (n+1))
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
// : SteelT unit (pts_to r full_permission prev) (fun _ -> pts_to r full_permission (prev+1))
// = upd r prev (prev+1)

// let incr2 (r1 r2:ref int) (prev1 prev2:int)
// : SteelT (unit & unit)
//   (pts_to r1 full_permission prev1 `star` pts_to r2 full_permission prev2)
//   (fun _ -> pts_to r1 full_permission (prev1+1) `star` pts_to r2 full_permission (prev2+1))
// = incr r1 prev1 || incr r2 prev2
