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
(**
    This module relates the ST, STAtomic, and STGhost effects to their
    selector counterparts, Steel, SteelAtomic, and SteelGhost.
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

/// Coerce SteelBase to ST
val coerce_steel (#a:Type)
                 (#pre:pre_t)
                 (#post:post_t a)
                 (#req:pure_pre)
                 (#ens:pure_post a)
                 ($f:unit -> SF.SteelBase a false pre post
                          (fun _ -> req)
                          (fun _ x _ -> ens x))
   : STF.ST a pre post req ens

/// Coerce SteelAtomicBase to STAtomic
val coerce_atomic (#a:Type)
                  (#o:inames)
                  (#obs:observability)
                  (#p:vprop)
                  (#q:a -> vprop)
                  (#pre:Type0)
                  (#post: a -> Type0)
                  ($f:unit -> SA.SteelAtomicBase a false o obs p q
                           (fun _ -> pre)
                           (fun _ x _ -> post x))
  : STA.STAtomicBase a false o obs p q pre post

/// Coerce framed SteelAtomicBase to STAtomic
val coerce_atomicF (#a:Type)
                   (#o:inames)
                   (#obs:observability)
                   (#p:vprop)
                   (#q:a -> vprop)
                   (#pre:Type0)
                   (#post: a -> Type0)
                   ($f:unit -> SA.SteelAtomicBase a true o obs p q
                     (fun _ -> pre)
                     (fun _ x _ -> post x))
  : STA.STAtomicBase a true o obs p q pre post

/// Coerce framed SteelGhostBase to STGhost
val coerce_ghost (#a:Type)
                 (#o:inames)
                 (#p:vprop)
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SA.SteelGhostBase a false o Unobservable p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STG.STGhostBase a false o Unobservable p q pre post

/// Coerce framed SteelGhostBase to STGhost
val coerce_ghostF (#a:Type)
                  (#o:inames)
                  (#p:vprop)
                  (#q:a -> vprop)
                  (#pre:Type0)
                  (#post: a -> Type0)
                  ($f:unit -> SA.SteelGhostBase a true o Unobservable p q
                    (fun _ -> pre)
                    (fun _ x _ -> post x))
  : STG.STGhostBase a true o Unobservable p q pre post

(*** Sub effects *)

/// A sub-effect from ST to Steel
val lift_st_steel
      (a:Type)
      (#framed:eqtype_as_type bool)
      (#pre:pre_t)
      (#post:post_t a)
      (#req:pure_pre)
      (#ens:pure_post a)
      (f:STF.repr a framed pre post req ens)
  : SF.repr a framed pre post (fun _ -> req) (fun _ x _ -> ens x)

sub_effect STF.STBase ~> SF.SteelBase = lift_st_steel


/// A sub-effect from STGhost to SteelGhost
val lift_stag_sa
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

sub_effect STG.STGhostBase ~> SA.SteelGhostBase = lift_stag_sa

/// Also a coercion for the same, in case it needs to be applied explicitly
val lift_stg_steelg (#a:Type)
                    (#o:inames)
                    (#p:vprop)
                    (#q:a -> vprop)
                    (#pre:Type0)
                    (#post: a -> Type0)
                    (f:unit -> STG.STGhost a o p q pre post)
                    (_:unit)
  : SA.SteelGhost a o p q (fun _ -> pre) (fun _ x _ -> post x)

(** At the moment, we are unable to define a sub-effect from STAtomic to SteelAtomic *)

/// An explicit coercion from STAtomic to SteelAtomic
val lift_sta_steela (#a:Type)
                    (#o:inames)
                    (#p:vprop)
                    (#q:a -> vprop)
                    (#pre:Type0)
                    (#post: a -> Type0)
                    (f:unit -> STA.STAtomic a o p q pre post)
                    (_:unit)
  : SA.SteelAtomic a o p q (fun _ -> pre) (fun _ x _ -> post x)
