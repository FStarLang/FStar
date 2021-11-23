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
module Steel.ST.Util
friend Steel.Effect.Atomic
friend Steel.ST.Effect.AtomicAndGhost
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe
include Steel.ST.Effect.Atomic
include Steel.ST.Effect.Ghost
module SEA = Steel.Effect.Atomic
module STG = Steel.ST.Effect.Ghost
module STAG = Steel.ST.Effect.AtomicAndGhost

assume
val reify_st_atomic_base(#a:Type)
                        (#framed:eqtype_as_type bool)
                        (#obs:eqtype_as_type observability)
                        (#o:inames)
                        (#p:vprop)
                        (#q:a -> vprop)
                        (#pre:Type0)
                        (#post: a -> Type0)
                        ($f:unit -> STAtomicBase a framed o obs p q pre post)
  : STAG.repr a framed o obs p q pre post


assume
val reify_st_ghost_base (#a:Type)
                        (#framed:eqtype_as_type bool)
                        (#obs:eqtype_as_type observability)
                        (#o:inames)
                        (#p:vprop)
                        (#q:a -> vprop)
                        (#pre:Type0)
                        (#post: a -> Type0)
                        ($f:unit -> STGhostBase a framed o obs p q pre post)
  : STAG.repr a framed o obs p q pre post

let lift_sta_steela (a:Type)
                    (#framed:eqtype_as_type bool)
                    (#obs:eqtype_as_type observability)
                    #o #p
                    (#q:a -> vprop)
                    (#pre:Type0)
                    (#post: a -> Type0)
                    (f:unit -> STAtomicBase a framed o obs p q pre post)
                    (_:unit)
  : SEA.SteelAtomicBase a framed o obs p q (fun _ -> pre) (fun _ x _ -> post x)
  = SEA.SteelAtomicBase?.reflect (reify_st_atomic_base f)

let lift_stg_steelg (a:Type)
                    (#framed:eqtype_as_type bool)
                    (#obs:eqtype_as_type observability)
                    #o #p
                    (#q:a -> vprop)
                    (#pre:Type0)
                    (#post: a -> Type0)
                    (f:unit -> STGhostBase a framed o obs p q pre post)
                    (_:unit)
  : SEA.SteelGhostBase a framed o obs p q (fun _ -> pre) (fun _ x _ -> post x)
  = SEA.SteelGhostBase?.reflect (reify_st_ghost_base f)

let coerce_repr #a (#framed:bool) #obs #o #p
                   (#q:a -> vprop)
                   (#pre:Type0)
                   (#post: a -> Type0)
                   ($f:unit -> SEA.SteelAtomicBase a framed o obs p q
                        (fun _ -> pre)
                        (fun _ x _ -> post x))
  : STAG.repr a framed o obs p q pre post
   = SEA.reify_steel_atomic_comp f

let coerce #a #framed #o #obs #p
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SEA.SteelAtomicBase a framed o obs p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STAtomicBase a framed o obs p q pre post
  = STAtomicBase?.reflect (coerce_repr f)

let coerce_ghost_repr #a #framed #o  #p
                      (#q:a -> vprop)
                      (#pre:Type0)
                      (#post: a -> Type0)
                      ($f:unit -> SEA.SteelGhostBase a framed o Unobservable p q
                        (fun _ -> pre)
                        (fun _ x _ -> post x))
  : STAG.repr a framed o Unobservable p q pre post
  = SEA.reify_steel_ghost_comp f

let coerce_ghost #a #framed #o #p
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SEA.SteelGhostBase a framed o Unobservable p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STGhostBase a framed o Unobservable p q pre post
  = STGhostBase?.reflect (coerce_ghost_repr f)

let weaken #o p q l =
    coerce_ghost (fun () -> SEA.rewrite_slprop p q l)

let rewrite #o p q =
    weaken p q (fun _ -> ()); ()

let extract_fact0 (#opened:inames)
                  (p:vprop)
                  (fact:prop)
                  (l:(m:mem) -> Lemma
                      (requires interp (hp_of p) m)
                      (ensures fact))
  : STAG.repr unit false opened Unobservable p (fun _ -> p) True (fun _ -> fact)
  = fun frame ->
      let m0:full_mem = NMSTTotal.get () in
      Classical.forall_intro_3 reveal_mk_rmem;
      let h0 = mk_rmem p (core_mem m0) in
      l (core_mem m0)

let extract_fact (#opened:inames)
                 (p:vprop)
                 (fact:prop)
                 (l:(m:mem) -> Lemma
                                (requires interp (hp_of p) m)
                                (ensures fact))
  : STGhost unit opened p (fun _ -> p) True (fun _ -> fact)
  = STGhostBase?.reflect (extract_fact0 p fact l)

let noop #o _ = rewrite #o emp emp

let admit _ = STGhostF?.reflect (fun _ -> NMSTTotal.nmst_tot_admit ())

let slassert0 #o (p:vprop)
  : SEA.SteelGhostT unit o p (fun _ -> p)
  = SEA.slassert p

let assert_ #o p = coerce_ghost (fun _ -> slassert0 p)
let drop #o p = coerce_ghost (fun _ -> SEA.drop p)
let intro_pure #o p = coerce_ghost (fun _ -> SEA.intro_pure p)
let elim_pure #o p = coerce_ghost (fun _ -> SEA.elim_pure p)

let return0 #a #o #p (x:a)
  : SEA.SteelAtomicBase a true o Unobservable
                        (return_pre (p x)) p
                        (fun _ -> True)
                        (fun _ v _ -> v == x)
  = let _ = () in SEA.return x

let return #a #o #p x = coerce (fun _ -> return0 x)

(* Lifting the separation logic exists combinator to vprop *)
let exists_ (#a:Type u#a) (p:a -> vprop)
  : vprop
  = SEA.h_exists p

/// Introducing an existential if the predicate [p] currently holds for value [x]
let intro_exists #a #o x p
  = coerce_ghost (fun _ -> SEA.intro_exists x p)

/// Variant of intro_exists above, when the witness is a ghost value
let intro_exists_erased #a #o x p
  = coerce_ghost (fun _ -> SEA.intro_exists_erased x p)

let elim_exists #a #o #p _
  = coerce_ghost (fun _ -> SEA.witness_exists #a #o #p ())

let lift_exists (#a:_) (#u:_) (p:a -> vprop)
  = coerce_ghost (fun _ -> SEA.lift_exists #a #u p)

let exists_cong #a #u p q
  = coerce_ghost (fun _ -> SEA.exists_cong #a #u p q)

let new_invariant #u p
  = coerce_ghost (fun _ -> SEA.new_invariant #u p)

let with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> STAtomicT a (add_inv opened_invariants i)
                                          (p `star` fp)
                                          (fun x -> p `star` fp' x))
  = coerce
    (fun _ ->
      SEA.with_invariant i
        (lift_sta_steela a
          #false
          #Observable
          #(add_inv opened_invariants i)
          #(p `star` fp)
          #(fun x -> p `star` fp' x)
          #True
          #(fun _ -> True)
          f))

let with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  = coerce_ghost
    (fun _ ->
       SEA.with_invariant_g i
        (lift_stg_steelg a
          #false
          #Unobservable
          #(add_inv opened_invariants i)
          #(p `star` fp)
          #(fun x -> p `star` fp' x)
          #True
          #(fun _ -> True)
          f))
