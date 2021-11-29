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
module Steel.ST.Coercions
(** This module aggregates several of the core effects and utilities
    associated with the Steel.ST namespace.

    Client modules should typically just [open Steel.ST.Util] and
    that should bring most of what they need in scope.
*)
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe

module SF = Steel.Effect
module SA = Steel.Effect.Atomic

module STF = Steel.ST.Effect
module STG = Steel.ST.Effect.Ghost
module STA = Steel.ST.Effect.Atomic
module STAG = Steel.ST.Effect.AtomicAndGhost

friend Steel.ST.Effect.AtomicAndGhost
friend Steel.Effect.Atomic
friend Steel.Effect
friend Steel.ST.Effect
friend Steel.ST.Effect.Ghost
friend Steel.ST.Effect.Atomic

unfold
let bind_div_st_req (#a:Type) (wp:pure_wp a)
                    (req_g:a -> Type0)
  : Type0
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    wp (fun _ -> True) /\ (forall x. req_g x)

unfold
let bind_div_st_ens (#a:Type) (#b:Type)
                       (wp:pure_wp a)
                       (ens_g:a -> b -> Type0)
    : b -> Type0
    = fun y -> wp (fun _ -> True) /\ (exists x. ens_g x y)

let bind_div_st_ (a:Type) (b:Type)
                  (#[@@@ framing_implicit] wp:pure_wp a)
                  (#framed:eqtype_as_type bool)
                  (#[@@@ framing_implicit] pre:pre_t)
                  (#[@@@ framing_implicit] post:post_t b)
                  (#[@@@ framing_implicit] req:a -> Type0)
                  (#[@@@ framing_implicit] ens:a -> b -> Type0)
                  (f:eqtype_as_type unit -> DIV a wp)
                  (g:(x:a -> STF.repr b framed pre post (req x) (ens x)))
  : STF.repr b
         framed
         pre
         post
         (bind_div_st_req wp req)
         (bind_div_st_ens wp ens)
  = let c
      : SF.repr b
                   framed
                   pre
                   post
                   (SF.bind_div_steel_req wp (fun x _ -> req x))
                   (SF.bind_div_steel_ens wp (fun x _ y _ -> ens x y))
      =(SF.bind_div_steel a b
                  wp
                  framed
                  pre
                  post
                  (fun x _ -> req x)
                  (fun x _ y _ -> ens x y)
                  f
                  g)
    in
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity #a wp;
    STF.weaken_repr _ _ _ _ _ _ _ _ c () ()

polymonadic_bind (DIV, STF.STBase) |> STF.STBase = bind_div_st_

let reify_steel_comp (#a:Type)
                     (#pre:pre_t)
                     (#post:post_t a)
                     (#req:Type0)
                     (#ens:a -> Type0)
                     ($f:unit -> SF.SteelBase a false pre post (fun _ -> req) (fun _ x _ -> ens x))
  : Dv (STF.repr a false pre post req ens)
  = SF.reify_steel_comp f

let reflect (#a:Type)
            (#pre:pre_t)
            (#post:post_t a)
            (#req:Type0)
            (#ens:a -> Type0)
            ($f:STF.repr a false pre post req ens)
  : STF.ST a pre post req ens
  = STF.STBase?.reflect f

let coerce_steel (#a:Type)
                 (#pre:pre_t)
                 (#post:post_t a)
                 (#req:st_req_t)
                 (#ens:st_ens_t a)
                 ($f:unit -> SF.SteelBase a false pre post
                          (fun _ -> req)
                          (fun _ x _ -> ens x))
   : STF.ST a pre post req ens
   = reflect (reify_steel_comp f)

let coerce_atomic #a #o #obs
                 (#p:vprop)
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SA.SteelAtomicBase a false o obs p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STA.STAtomicBase a false o obs p q pre post
  = STA.STAtomicBase?.reflect (SA.reify_steel_atomic_comp f)

let coerce_atomicF #a #o #p #q #pre #post f
  = STA.STAtomicBase?.reflect (SA.reify_steel_atomic_comp f)

let coerce_ghost (#a:Type)
                 (#o:inames)
                 (#p:vprop)
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SA.SteelGhostBase a false o Unobservable p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STG.STGhostBase a false o Unobservable p q pre post
  = STG.STGhostBase?.reflect (SA.reify_steel_ghost_comp f)

let coerce_ghostF #a #o #p #q #pre #post f
  = STGhostBase?.reflect (SA.reify_steel_ghost_comp f)

let lift_st_steel
      (a:Type)
      (#framed:eqtype_as_type bool)
      (#pre:pre_t)
      (#post:post_t a)
      (#req:Type0)
      (#ens:a -> Type0)
      (f:STF.repr a framed pre post req ens)
  : SF.repr a framed pre post (fun _ -> req) (fun _ x _ -> ens x)
  = f


let lift_sta_sa
      (a:Type)
      (#framed:eqtype_as_type bool)
      (#o:inames)
      (#obs:eqtype_as_type observability)
      (#pre:pre_t)
      (#post:post_t a)
      (#req:Type0)
      (#ens:a -> Type0)
      (f:STAG.repr a framed o obs pre post req ens)
  : SA.repr a framed o obs pre post (fun _ -> req) (fun _ x _ -> ens x)
  = f


let lift_stag_sa
      (a:Type)
      (#framed:eqtype_as_type bool)
      (#o:inames)
      (#obs:eqtype_as_type observability)
      (#pre:pre_t)
      (#post:post_t a)
      (#req:Type0)
      (#ens:a -> Type0)
      (f:STAG.repr a framed o obs pre post req ens)
  : SA.repr a framed o obs pre post (fun _ -> req) (fun _ x _ -> ens x)
  = f

let lift_stg_steelg (#a:Type)
                     #o #p
                     (#q:a -> vprop)
                     (#pre:Type0)
                     (#post: a -> Type0)
                     (f:unit -> STGhost a o p q pre post)
                     (_:unit)
  : SA.SteelGhost a o p q (fun _ -> pre) (fun _ x _ -> post x)
  = f()

(* I would like to define this, but I cannot
   because of an effect ordering constraint *)
// sub_effect STA.STAtomicBase ~> SA.SteelAtomicBase = lift_sta_sa

(* So, instead, I assume a reification of STAtomicBase *)
assume
val reify_st_atomic_base(#a:Type)
                        (#framed:eqtype_as_type bool)
                        (#obs:eqtype_as_type observability)
                        (#o:inames)
                        (#p:vprop)
                        (#q:a -> vprop)
                        (#pre:Type0)
                        (#post: a -> Type0)
                        ($f:unit -> STA.STAtomicBase a framed o obs p q pre post)
  : STAG.repr a framed o obs p q pre post

let lift_sta_steela (#a:Type)
                     #o #p
                     (#q:a -> vprop)
                     (#pre:Type0)
                     (#post: a -> Type0)
                     (f:unit -> STA.STAtomic a o p q pre post)
                     (_:unit)
  : SA.SteelAtomic a o p q (fun _ -> pre) (fun _ x _ -> post x)
  = SA.SteelAtomicBase?.reflect (reify_st_atomic_base f)
