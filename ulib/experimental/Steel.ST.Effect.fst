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

module Steel.ST.Effect
friend Steel.Effect
open Steel.Memory
open FStar.Ghost
module Mem = Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
open Steel.Effect
#set-options "--warn_error -330"  //turn off the experimental feature warning
#set-options "--ide_id_info_off"

let repr a framed pre post req ens : Type u#2 =
  Steel.Effect.repr a framed pre post (fun _ -> req) (fun _ v _ -> ens v)

let equiv_star_emp_r (p:vprop)
  : Lemma ((p `star` emp) `equiv` p)
  = cm_identity p;
    assert ((emp `star` p) `equiv` p);
    star_commutative p emp;
    equiv_trans (p `star` emp) (emp `star` p) p

let weaken_repr a framed
                (pre:pre_t)
                (post:post_t a)
                (req req':req_t pre)
                (ens ens':ens_t pre a post)
                (f:Steel.Effect.repr a framed pre post req ens)
                (_:squash (forall (h0:hmem pre).
                            req' (mk_rmem _ h0) ==>
                            req (mk_rmem _ h0)))
                (_:squash (forall (h0:hmem pre) x (h1:hmem (post x)).
                            ens (mk_rmem _ h0)
                                x
                                (mk_rmem _ h1) ==>
                            ens' (mk_rmem _ h0) x (mk_rmem _ h1)))
  : Tot (Steel.Effect.repr a framed pre post req' ens')
  = let focus_rmem_refl (r:vprop) (h:rmem r)
      : Lemma (ensures focus_rmem #r h r == h)
              [SMTPat (focus_rmem #r h r)]
      = focus_rmem_refl r h
    in
    let equiv_trans (x y z:vprop) : Lemma
      (requires equiv x y /\ equiv y z)
      (ensures equiv x z)
      [SMTPat (equiv x z);
       SMTPat (equiv x y)]
     = equiv_trans x y z
    in
    let cbs (p:vprop)
      : Lemma (p `can_be_split` (p `star` emp))
              [SMTPat (p `can_be_split` (p `star` emp))]
      = star_commutative p emp;
        cm_identity p;
        equiv_sym (p `star` emp) p;
        equiv_can_be_split p (p `star` emp)
    in
    let epost ()
      : Lemma (equiv_forall post (fun x -> star (post x) emp))
      = introduce forall x. post x `equiv` (post x `star` emp)
        with (
          equiv_star_emp_r (post x);
          equiv_sym (post x `star` emp) (post x)
        );
        equiv_forall_elim post (fun x -> star (post x) emp)
    in
    epost ();
    Steel.Effect.subcomp_opaque a #framed #framed
                         #pre #post
                         #req #ens
                         #pre #post
                         #req' #ens'
                         #emp
                         #True
                         #()
                         #()
                         #()
                         f


let return_ (a:Type)
            (x:a)
            (#[@@@ framing_implicit] p:a -> vprop)
  : Tot (repr a true (return_pre (p x)) p True (fun v -> v == x))
  = let k : Steel.Effect.repr a true
            (p x)
            p
            (fun _ -> True)
            (return_ens a x p)
          = Steel.Effect.return_ a x #p
    in
    weaken_repr _ _ _ _ _ _ _ _ k () ()

let bind (a:Type) (b:Type)
         (#framed_f:eqtype_as_type bool)
         (#framed_g:eqtype_as_type bool)
         (#[@@@ framing_implicit] pre_f:pre_t)
         (#[@@@ framing_implicit] post_f:post_t a)
         (#[@@@ framing_implicit] req_f:Type0)
         (#[@@@ framing_implicit] ens_f:a -> Type0)
         (#[@@@ framing_implicit] pre_g:a -> pre_t)
         (#[@@@ framing_implicit] post_g:a -> post_t b)
         (#[@@@ framing_implicit] req_g:(a -> Type0))
         (#[@@@ framing_implicit] ens_g:(a -> b -> Type0))
         (#[@@@ framing_implicit] frame_f:vprop)
         (#[@@@ framing_implicit] frame_g:a -> vprop)
         (#[@@@ framing_implicit] post:post_t b)
         (#[@@@ framing_implicit] _x1: squash (maybe_emp framed_f frame_f))
         (#[@@@ framing_implicit] _x2: squash (maybe_emp_dep framed_g frame_g))
         (#[@@@ framing_implicit] pr:a -> prop)
         (#[@@@ framing_implicit] p1:squash
           (can_be_split_forall_dep pr
             (fun x -> post_f x `star` frame_f)
             (fun x -> pre_g x `star` frame_g x)))
         (#[@@@ framing_implicit] p2:squash
           (can_be_split_post (fun x y -> post_g x y `star` frame_g x) post))
         (f:repr a framed_f pre_f post_f req_f ens_f)
         (g:(x:a -> repr b framed_g (pre_g x) (post_g x) (req_g x) (ens_g x)))
    = let c = Steel.Effect.bind a b #framed_f #framed_g
                                #pre_f
                                #post_f
                                #(fun _ -> req_f)
                                #(fun _ x _ -> ens_f x)
                                #pre_g
                                #post_g
                                #(fun x _ -> req_g x)
                                #(fun x _ y _ -> ens_g x y)
                                #frame_f
                                #frame_g
                                #post
                                #_x1
                                #_x2
                                #pr
                                #p1
                                #p2
                                f g
      in
      weaken_repr _ _ _ _ _ _ _ _ c () ()

let subcomp (a:Type)
            (#framed_f:eqtype_as_type bool)
            (#framed_g:eqtype_as_type bool)
            (#[@@@ framing_implicit] pre_f:pre_t)
            (#[@@@ framing_implicit] post_f:post_t a)
            (#[@@@ framing_implicit] req_f:Type0)
            (#[@@@ framing_implicit] ens_f:a -> Type0)
            (#[@@@ framing_implicit] pre_g:pre_t)
            (#[@@@ framing_implicit] post_g:post_t a)
            (#[@@@ framing_implicit] req_g:Type0)
            (#[@@@ framing_implicit] ens_g:a -> Type0)
            (#[@@@ framing_implicit] frame:vprop)
            (#[@@@ framing_implicit] _x1 : squash (maybe_emp framed_f frame))
            (#[@@@ framing_implicit] p1:squash (
              can_be_split pre_g (pre_f `star` frame)))
            (#[@@@ framing_implicit] p2:squash (
              equiv_forall post_g (fun x -> post_f x `star` frame)))
            (f:repr a framed_f pre_f post_f req_f ens_f)
    : Pure (repr a framed_g pre_g post_g req_g ens_g)
      (requires
        req_g ==> (req_f /\ (forall x. ens_f x ==> ens_g x)))
      (ensures fun _ -> True)
    = weaken_repr _ _ _ _ _ _ _ _
                  (Steel.Effect.subcomp
                      a
                      #framed_f
                      #framed_g
                      #pre_f
                      #post_f
                      #(fun _ -> req_f)
                      #(fun _ x _ -> ens_f x)
                      #pre_g
                      #post_g
                      #(fun _ -> req_g)
                      #(fun _ x _ -> ens_g x)
                      #frame
                      #_x1
                      #True
                      #p1
                      #p2
                      f)
                      () ()

let bind_pure_st_ (a:Type) (b:Type)
                  (#[@@@ framing_implicit] wp:pure_wp a)
                  (#framed:eqtype_as_type bool)
                  (#[@@@ framing_implicit] pre:pre_t)
                  (#[@@@ framing_implicit] post:post_t b)
                  (#[@@@ framing_implicit] req:a -> Type0)
                  (#[@@@ framing_implicit] ens:a -> b -> Type0)
                  (f:eqtype_as_type unit -> PURE a wp)
                  (g:(x:a -> repr b framed pre post (req x) (ens x)))
    : repr b
           framed
           pre
           post
           (bind_pure_st_req wp req)
           (bind_pure_st_ens wp ens)
  = let c
      : Steel.Effect.repr b
                   framed
                   pre
                   post
                   (bind_pure_steel__req wp (fun x _ -> req x))
                   (bind_pure_steel__ens wp (fun x _ y _ -> ens x y))
      =(Steel.Effect.bind_pure_steel_ a b
                  #wp
                  #framed
                  #pre
                  #post
                  #(fun x _ -> req x)
                  #(fun x _ y _ -> ens x y)
                  f
                  g)
    in
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity #a wp;
    weaken_repr _ _ _ _ _ _ _ _ c () ()
