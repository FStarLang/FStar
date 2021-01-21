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

module Steel.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module Ins = Steel.Semantics.Instantiate
open Steel.Memory

val join_preserves_interp (hp:slprop) (m0 m1:mem)
  : Lemma
    (requires (interp hp m0 /\ disjoint m0 m1))
    (ensures (interp hp (join m0 m1)))
    [SMTPat (interp hp (join m0 m1))]

val respects_fp (#fp:slprop) (p: hmem fp -> prop) : prop
#push-options "--query_stats"
val reveal_respects_fp (#fp:_) (p:hmem fp -> prop)
  : Lemma (respects_fp p <==>
           (forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)))
          [SMTPat (respects_fp #fp p)]
#pop-options
let fp_mprop (fp:slprop) = p:(hmem fp -> prop) { respects_fp p }

val respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                       (q:(hmem pre -> x:a -> hmem (post x) -> prop)) : prop

val reveal_respects_binary_fp (#a:Type) (#pre:slprop) (#post:a -> slprop)
                              (q:(hmem pre -> x:a -> hmem (post x) -> prop))
  : Lemma (respects_binary_fp q <==>
            //at this point we need to know interp pre (join h_pre h) -- use join_preserves_interp for that
            (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
              q h_pre x h_post <==> q (join h_pre h) x h_post) /\
            //can join any disjoint heap to the post-heap and q is still valid
            (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
              q h_pre x h_post <==> q h_pre x (join h_post h)))
           [SMTPat (respects_binary_fp #a #pre #post q)]

let fp_binary_mprop #a (pre:slprop) (post: a -> slprop) =
  p:(hmem pre -> x:a -> hmem (post x) -> prop){ respects_binary_fp p }

val repr (a:Type u#a)
         (pre:slprop u#1)
         (post:a -> slprop u#1)
         (req:fp_mprop pre)
         (ens:fp_binary_mprop pre post)
  : Type u#2 //Note, we leak the universe of the representation, which currently must be universe 0

unfold
let return_req (p:slprop) : fp_mprop p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> slprop) : fp_binary_mprop (p x) p = fun _ r _ -> r == x

val return (a:Type u#a) (x:a) (p:a -> slprop)
  : repr a (p x) p (return_req (p x)) (return_ens x p)

unfold
let bind_req (#a:Type) (#pre_f:slprop) (#post_f:a -> slprop)
             (req_f:fp_mprop pre_f) (ens_f:fp_binary_mprop pre_f post_f)
             (req_g:(x:a -> fp_mprop (post_f x)))
  : fp_mprop pre_f
  = fun h -> req_f h /\ (forall (x:a) h1. ens_f h x h1 ==> req_g x h1)

unfold
let bind_ens (#a:Type) (#b:Type) (#pre_f:slprop) (#post_f:a -> slprop)
             (req_f:fp_mprop pre_f) (ens_f:fp_binary_mprop pre_f post_f)
             (#post_g:b -> slprop) (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
  : fp_binary_mprop pre_f post_g
  = fun h0 y h2 -> req_f h0 /\ (exists x h1. ens_f h0 x h1 /\ (ens_g x) h1 y h2)

val bind (a:Type)
         (b:Type)
         (pre_f:slprop)
         (post_f:a -> slprop)
         (req_f:fp_mprop pre_f)
         (ens_f:fp_binary_mprop pre_f post_f)
         (post_g:b -> slprop)
         (req_g:(x:a -> fp_mprop (post_f x)))
         (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
         (f:repr a pre_f post_f req_f ens_f)
         (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
   : repr b pre_f post_g
          (bind_req req_f ens_f req_g)
          (bind_ens req_f ens_f ens_g)

unfold
let subcomp_pre (#a:Type)
                (#pre:slprop)
                (#post:a -> slprop)
                (req_f:fp_mprop pre)
                (ens_f:fp_binary_mprop pre post)
                (req_g:fp_mprop pre)
                (ens_g:fp_binary_mprop pre post)
   : pure_pre
   = (forall h. req_g h ==> req_f h) /\
     (forall h0 x h1. (req_g h0 /\ ens_f h0 x h1) ==> ens_g h0 x h1)

val subcomp (a:Type)
            (pre:slprop)
            (post:a -> slprop)
            (req_f:fp_mprop pre)
            (ens_f:fp_binary_mprop pre post)
            (req_g:fp_mprop pre)
            (ens_g:fp_binary_mprop pre post)
            (f:repr a pre post req_f ens_f)
  : Pure (repr a pre post req_g ens_g)
         (requires subcomp_pre req_f ens_f req_g ens_g)
         (ensures fun _ -> True)

unfold
let if_then_else_req (#pre:slprop)
                     (req_then:fp_mprop pre)
                     (req_else:fp_mprop pre)
                     (p:Type0)
  : fp_mprop pre
  = fun h -> (p ==> req_then h) /\ ((~ p) ==> req_else h)

unfold
let if_then_else_ens (#a:Type)
                     (#pre:slprop)
                     (#post:a -> slprop)
                     (ens_then:fp_binary_mprop pre post)
                     (ens_else:fp_binary_mprop pre post)
                     (p:Type0)
  : fp_binary_mprop pre post
  = fun h0 x h1 -> (p ==> ens_then h0 x h1) /\ ((~ p) ==> ens_else h0 x h1)

let if_then_else (a:Type)
                 (pre:slprop)
                 (post:a -> slprop)
                 (req_then:fp_mprop pre)
                 (ens_then:fp_binary_mprop pre post)
                 (req_else:fp_mprop pre)
                 (ens_else:fp_binary_mprop pre post)
                 (f:repr a pre post req_then ens_then)
                 (g:repr a pre post req_else ens_else)
                 (p:bool)
  : Type
  = repr a pre post
         (if_then_else_req req_then req_else p)
         (if_then_else_ens ens_then ens_else p)

[@@ allow_informative_binders]
reifiable reflectable
effect {
  Steel (a:Type)
        (pre:slprop u#1)
        (post:a -> slprop u#1)
        (req:fp_mprop pre)
        (ens:fp_binary_mprop pre post)
  with { repr; return; bind; subcomp; if_then_else }
}

effect SteelT (a:Type) (pre:slprop) (post:a -> slprop) =
  Steel a pre post (fun _ -> True) (fun _ _ _ -> True)

unfold
let bind_pure_steel_req (#a:Type)
                        (wp:pure_wp a)
                        (#pre_g:slprop)
                        (req_g:a -> fp_mprop pre_g)
  : fp_mprop pre_g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun h -> wp (fun x -> req_g x h) /\ wp (fun _ -> True)

unfold
let bind_pure_steel_ens (#a:Type)
                        (#b:Type)
                        (wp:pure_wp a)
                        (#pre_g:slprop)
                        (#post_g:b -> slprop)
                        (ens_g:a -> fp_binary_mprop pre_g post_g)
   : fp_binary_mprop pre_g post_g
   = fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. (~ (wp (fun r -> r =!= x))) /\ ens_g x h0 r h1)

val bind_pure_steel (a:Type)
                    (b:Type)
                    (wp:pure_wp a)
                    (pre_g:slprop)
                    (post_g:b -> slprop)
                    (req_g:a -> fp_mprop pre_g)
                    (ens_g:a -> fp_binary_mprop pre_g post_g)
                    (f:eqtype_as_type unit -> PURE a wp)
                    (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
  : repr b pre_g post_g
         (bind_pure_steel_req wp req_g)
         (bind_pure_steel_ens wp ens_g)

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel

unfold
let polymonadic_bind_steel_pure_pre (#a:Type)
                                    (#b:Type)
                                    (#pre_f:slprop)
                                    (#post_f:slprop)
                                    (req_f:fp_mprop pre_f)
                                    (ens_f:fp_binary_mprop pre_f (fun _ -> post_f))
                                    (wp_g:a -> pure_wp b)
  : fp_mprop pre_f
  = let aux (m0:hmem pre_f) (m1:mem{disjoint m0 m1})
      : Lemma
        (requires
          forall (x:a) (h1:hmem post_f). ens_f (join m0 m1) x h1 ==> (wp_g x) (fun _ -> True))
        (ensures
          forall (x:a) (h1:hmem post_f). ens_f m0 x h1 ==> (wp_g x) (fun _ -> True))
        [SMTPat (disjoint m0 m1)]
      = assert (forall (x:a) (h1:hmem post_f). ens_f m0 x h1 <==> ens_f (join m0 m1) x h1) in
    fun h -> req_f h /\ (forall (x:a) (h1:hmem post_f). ens_f h x h1 ==> (wp_g x) (fun _ -> True))

unfold
let polymonadic_bind_steel_pure_post (#a:Type)
                                     (#b:Type)
                                     (#pre_f:slprop)
                                     (#post_f:Mem.slprop)
                                     (ens_f:fp_binary_mprop pre_f (fun _ -> post_f))
                                     (wp_g:a -> pure_wp b)
  : fp_binary_mprop pre_f (fun _ -> post_f)
  = fun h0 r h1 -> exists x. (ens_f h0 x h1 /\ (~ ((wp_g x) (fun y -> y =!= r))))

val bind_steel_pure (a:Type)
                    (b:Type)
                    (pre_f:slprop)
                    (post_f:slprop)
                    (req_f:fp_mprop pre_f)
                    (ens_f:fp_binary_mprop pre_f (fun _ -> post_f))
                    (wp_g:a -> pure_wp b)
                    (f:repr a pre_f (fun _ -> post_f) req_f ens_f)
                    (g:(x:a -> eqtype_as_type unit -> PURE b (wp_g x)))
  : repr b pre_f (fun _ -> post_f)
         (polymonadic_bind_steel_pure_pre req_f ens_f wp_g)
         (polymonadic_bind_steel_pure_post ens_f wp_g)

polymonadic_bind (Steel, PURE) |> Steel = bind_steel_pure

val par (#aL:Type u#a)
        (#preL:slprop u#1)
        (#postL:aL -> slprop u#1)
        (#lpreL:fp_mprop preL)
        (#lpostL:fp_binary_mprop preL postL)
        ($f:unit -> Steel aL preL postL lpreL lpostL)
        (#aR:Type u#a)
        (#preR:slprop u#1)
        (#postR:aR -> slprop u#1)
        (#lpreR:fp_mprop preR)
        (#lpostR:fp_binary_mprop preR postR)
        ($g:unit -> Steel aR preR postR lpreR lpostR)
  : Steel (aL & aR)
    (preL `Mem.star` preR)
    (fun (xL, xR) -> postL xL `Mem.star` postR xR)
    (fun h -> lpreL h /\ lpreR h)
    (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)

val ( || ) (#aL:Type u#a)
          (#preL:slprop)
          (#postL:aL -> slprop)
          ($f:unit -> SteelT aL preL postL)
          (#aR:Type u#a)
          (#preR:slprop)
          (#postR:aR -> slprop)
          ($g:unit -> SteelT aR preR postR)
 : SteelT (aL & aR)
          (preL `Mem.star` preR)
          (fun (xL, xR) -> postL xL `Mem.star` postR xR)

val frame (#a:Type)
          (#pre:slprop)
          (#post:a -> slprop)
          (#req:fp_mprop pre)
          (#ens:fp_binary_mprop pre post)
          ($f:unit -> Steel a pre post req ens)
          (frame:slprop)
          (f_frame:mprop frame)
  : Steel a
    (pre `Mem.star` frame)
    (fun x -> post x `Mem.star` frame)
    (fun h -> req h /\ f_frame h)
    (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)

val read (#a:Type)
         (#pcm:_)
         (r:ref a pcm)
         (v0:Ghost.erased a)
  : SteelT (v:a { FStar.PCM.compatible pcm v0 v })
           (pts_to r v0)
           (fun _ -> pts_to r v0)

val write (#a:Type)
          (#pcm:_)
          (r:ref a pcm)
          (v0:Ghost.erased a)
          (v1:a{FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.FStar.PCM.refine v1})
  : SteelT unit
           (pts_to r v0)
           (fun _ -> pts_to r v1)

val alloc (#a:Type)
          (#pcm:_)
          (x:a{FStar.PCM.compatible pcm x x /\ pcm.FStar.PCM.refine x })
  : SteelT (ref a pcm)
           emp
           (fun r -> pts_to r x)

val free (#a:Type)
         (#p:FStar.PCM.pcm a)
         (r:ref a p)
         (x:Ghost.erased a{FStar.PCM.exclusive p x /\ FStar.PCM.(p.refine p.p.one)})
  : SteelT unit (pts_to r x) (fun _ -> pts_to r FStar.PCM.(p.p.one))

val split (#a:Type)
          (#p:FStar.PCM.pcm a)
          (r:ref a p)
          (v0:Ghost.erased a)
          (v1:Ghost.erased a{FStar.PCM.composable p v0 v1})
  : SteelT unit (pts_to r (FStar.PCM.op p v0 v1))
                (fun _ -> pts_to r v0 `star` pts_to r v1)

val gather (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:Ghost.erased a)
           (v1:Ghost.erased a)
  : SteelT (_:unit{FStar.PCM.composable p v0 v1})
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (FStar.PCM.op p v0 v1))

let fact_valid_compat (#a:Type) (#pcm:FStar.PCM.pcm a)
                      (fact:stable_property pcm)
                      (v:Ghost.erased a)
  = squash (forall z. FStar.PCM.compatible pcm v z ==> fact z)

val witness (#a:Type) (#pcm:FStar.PCM.pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:Ghost.erased a)
            (_:fact_valid_compat fact v)
  : SteelT unit (pts_to r v)
                (fun _ -> pts_to r v `star` pure (witnessed r fact))

val recall (#a:Type u#1) (#pcm:FStar.PCM.pcm a) (#fact:property a)
           (r:ref a pcm)
           (v:Ghost.erased a)
  : SteelT (v1:Ghost.erased a{FStar.PCM.compatible pcm v v1})
           (pts_to r v `star` pure (witnessed r fact))
           (fun v1 -> pts_to r v `star` pure (fact v1))

val cond (#a:Type)
         (b:bool)
         (p: bool -> slprop)
         (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)

val add_action (#a:Type)
               (#p:slprop)
               (#q:a -> slprop)
               (f:action_except a Set.empty p q)
  : SteelT a p q


(***** Bind and Subcomp relation with Steel.Atomic *****)

module Atomic = Steel.Effect.Atomic

unfold
let bind_req_atomic_steel (#a:Type) (#pre_f:slprop) (#post_f:a -> slprop) (req_g:(x:a -> fp_mprop (post_f x)))
: fp_mprop pre_f
= fun _ -> forall (x:a) h1. req_g x h1

unfold
let bind_ens_atomic_steel (#a:Type) (#b:Type)
  (#pre_f:slprop) (#post_f:a -> slprop) (#post_g:b -> slprop) (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
: fp_binary_mprop pre_f post_g
= fun _ y h2 -> exists x h1. (ens_g x) h1 y h2

val bind_atomic_steel (a:Type) (b:Type)
  (pre_f:slprop) (post_f:a -> slprop) (obs:Atomic.observability)
  (post_g:b -> slprop) (req_g:(x:a -> fp_mprop (post_f x))) (ens_g:(x:a -> fp_binary_mprop (post_f x) post_g))
  (f:Atomic.repr a Set.empty obs pre_f post_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g
    (bind_req_atomic_steel req_g)
    (bind_ens_atomic_steel ens_g)

polymonadic_bind (Atomic.SteelAtomic, Steel) |> Steel = bind_atomic_steel

unfold
let subcomp_req_atomic_steel (a:Type) (pre_f:slprop) : fp_mprop pre_f = fun _ -> True

unfold
let subcomp_ens_atomic_steel (#a:Type) (pre_f:slprop) (post_f:a -> slprop)
: fp_binary_mprop pre_f post_f
= fun _ _ _ -> True

val subcomp_atomic_steel (a:Type)
  (pre_f:slprop) (post_f:a -> slprop) (obs:Atomic.observability)
  (f:Atomic.repr a Set.empty obs pre_f post_f)
: repr a pre_f post_f (subcomp_req_atomic_steel a pre_f) (subcomp_ens_atomic_steel pre_f post_f)

polymonadic_subcomp Atomic.SteelAtomic <: Steel = subcomp_atomic_steel
