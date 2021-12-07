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

module Steel.ST.Effect.AtomicAndGhost
friend Steel.Effect.Atomic
friend Steel.ST.Effect
module C = Steel.Effect.Common
open Steel.Memory
module T = FStar.Tactics
module STF = Steel.ST.Effect
module SEA = Steel.Effect.Atomic
open Steel.Effect.Atomic

/// This module defines atomic and ghost variants of the Steel effect

#set-options "--warn_error -330 --ide_id_info_off"  //turn off the experimental feature warning

let repr (a:Type u#a)
         (already_framed:bool)
         (opened_invariants:inames)
         (g:observability)
         (pre:pre_t)
         (post:post_t a)
         (req:Type0)
         (ens:a -> Type0)
  : Type u#(max a 2)
  = SEA.repr a already_framed opened_invariants g pre post
             (fun _ -> req)
             (fun _ x _ -> ens x)



let equiv_star_emp_r (p:vprop)
  : Lemma ((p `star` emp) `equiv` p)
  = cm_identity p;
    assert ((emp `star` p) `equiv` p);
    star_commutative p emp;
    equiv_trans (p `star` emp) (emp `star` p) p

let weaken_repr #a #framed #o #g
                (#pre:pre_t)
                (#post:post_t a)
                (#req #req':req_t pre)
                (#ens #ens':ens_t pre a post)
                ($f:SEA.repr a framed o g pre post req ens)
                (_:squash (forall (h0:hmem pre).
                            req' (mk_rmem _ h0) ==>
                            req (mk_rmem _ h0)))
                (_:squash (forall (h0:hmem pre) x (h1:hmem (post x)).
                            ens (mk_rmem _ h0)
                                x
                                (mk_rmem _ h1) ==>
                            ens' (mk_rmem _ h0) x (mk_rmem _ h1)))
  : Tot (SEA.repr a framed o g pre post req' ens')
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
    SEA.subcomp_opaque a o g g #framed #framed
                         #pre #post
                         #req #ens
                         #pre #post
                         #req' #ens'
                         #emp
                         #()
                         #()
                         #()
                         f

let return_ (a:Type u#a)
            (x:a)
            (opened_invariants:inames)
            (#[@@@ framing_implicit] p:a -> vprop)
  : repr a true opened_invariants Unobservable
         (return_pre (p x)) p
         True
         (fun v -> v == x)
  = weaken_repr (SEA.return_ a x opened_invariants #p) () ()


let bind (a:Type) (b:Type)
         (opened_invariants:inames)
         (o1:eqtype_as_type observability)
         (o2:eqtype_as_type observability)
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
         (#[@@@ framing_implicit] _x1 : squash (maybe_emp framed_f frame_f))
         (#[@@@ framing_implicit] _x2 : squash (maybe_emp_dep framed_g frame_g))
         (#[@@@ framing_implicit] pr:a -> prop)
         (#[@@@ framing_implicit] p1:squash
           (can_be_split_forall_dep pr
             (fun x -> post_f x `star` frame_f)
             (fun x -> pre_g x `star` frame_g x)))
         (#[@@@ framing_implicit] p2:squash
           (can_be_split_post
             (fun x y -> post_g x y `star` frame_g x) post))
         (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
         (g:(x:a -> repr b framed_g opened_invariants o2 (pre_g x) (post_g x) (req_g x) (ens_g x)))
 = weaken_repr (SEA.bind a b opened_invariants o1 o2
                         #framed_f
                         #framed_g
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
                         f g) () ()

let subcomp (a:Type)
            (opened_invariants:inames)
            (o1:eqtype_as_type observability)
            (o2:eqtype_as_type observability)
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
            (#[@@@ framing_implicit] _x : squash (maybe_emp framed_f frame))
            (#[@@@ framing_implicit] p1:squash (can_be_split pre_g (pre_f `star` frame)))
            (#[@@@ framing_implicit] p2:squash (equiv_forall post_g (fun x -> post_f x `star` frame)))
            (f:repr a framed_f opened_invariants o1 pre_f post_f req_f ens_f)
    : Pure (repr a framed_g opened_invariants o2 pre_g post_g req_g ens_g)
      (requires
        (o1 = Unobservable || o2 = Observable) /\
        (req_g ==> (req_f /\ (forall x. ens_f x ==> ens_g x))))
      (ensures fun _ -> True)
    = weaken_repr (SEA.subcomp a opened_invariants o1 o2
                         #framed_f
                         #framed_g
                         #pre_f
                         #post_f
                         #(fun _ -> req_f)
                         #(fun _ x _ -> ens_f x)
                         #pre_g
                         #post_g
                         #(fun _ -> req_g)
                         #(fun _ y _ -> ens_g y)
                         #frame
                         #_x
                         #p1
                         #p2
                         f) () ()

/// The composition combinator.
let bind_pure_stag (a:Type) (b:Type)
                   (opened_invariants:inames)
                   (o:eqtype_as_type observability)
                   (#[@@@ framing_implicit] wp:pure_wp a)
                   (#framed:eqtype_as_type bool)
                   (#[@@@ framing_implicit] pre:pre_t)
                   (#[@@@ framing_implicit] post:post_t b)
                   (#[@@@ framing_implicit] req:a -> Type0)
                   (#[@@@ framing_implicit] ens:a -> b -> Type0)
                   (f:eqtype_as_type unit -> PURE a wp)
                   (g:(x:a -> repr b framed opened_invariants o pre post (req x) (ens x)))
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    weaken_repr (SEA.bind_pure_steela_ a b opened_invariants o #wp #framed #pre #post #(fun x _ -> req x) #(fun x _ y _ -> ens x y) f g) () ()

let lift_atomic_st
    (a:Type)
    (o:eqtype_as_type observability)
    (#framed:eqtype_as_type bool)
    (#[@@@ framing_implicit] pre:pre_t)
    (#[@@@ framing_implicit] post:post_t a)
    (#[@@@ framing_implicit] req:Type0)
    (#[@@@ framing_implicit] ens:a -> Type0)
    (f:repr a framed Set.empty o pre post req ens)
  : Steel.ST.Effect.repr a framed pre post req ens
  = let ff : Steel.Effect.repr a framed pre post (fun _ -> req) (fun _ x _ -> ens x)
        =  SEA.lift_atomic_steel a o #framed #pre #post #(fun _ -> req) #(fun _ x _ -> ens x) f
    in
    ff
