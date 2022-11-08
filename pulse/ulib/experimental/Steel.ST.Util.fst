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
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe
module SEA = Steel.Effect.Atomic
module SE = Steel.Effect
module STG = Steel.ST.Effect.Ghost
module STAG = Steel.ST.Effect.AtomicAndGhost
open Steel.ST.Coercions

#set-options "--ide_id_info_off"

let weaken #o p q l =
  coerce_ghost (fun () -> SEA.rewrite_slprop p q l)

let rewrite #o p q =
  weaken p q (fun _ -> ()); ()

let rewrite_with_tactic #opened p q =
  weaken p q (fun _ -> reveal_equiv p q)

let rewrite_equiv #opened p q =
  FStar.Algebra.CommMonoid.Equiv.elim_eq_laws Steel.Effect.Common.req;
  assert (Steel.Effect.Common.req.eq == equiv);
  reveal_equiv p q;
  weaken p q (fun _ -> ())

let noop #o _ = rewrite #o emp emp

let slassert0 #o (p:vprop)
  : SEA.SteelGhostT unit o p (fun _ -> p)
  = SEA.slassert p

let assert_ #o p = coerce_ghost (fun _ -> slassert0 p)
let assume_ #o p = admit_ ()
let drop #o p = coerce_ghost (fun _ -> SEA.drop p)
let pure = pure
let reveal_pure _ = ()
let intro_pure #o p = coerce_ghost (fun _ -> SEA.intro_pure p)
let elim_pure #o p = coerce_ghost (fun _ -> SEA.elim_pure p)

/// Extracting a proposition from a [pure p] while retaining [pure p]
let extract_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> pure p) True (fun _ -> p)
  = let _ = elim_pure p in
    intro_pure p

let intro_can_be_split_pure'
  (p: prop)
: Lemma
  (p ==> emp `can_be_split` pure p)
= reveal_can_be_split ();
  Classical.forall_intro (pure_interp p)

let intro_can_be_split_pure
  (p: prop)
  (sq: squash p)
: Tot (squash (emp `can_be_split` pure p))
= intro_can_be_split_pure' p

let intro_can_be_split_forall_dep_pure
  p
= Classical.forall_intro (fun x -> intro_can_be_split_pure' (p x))

[@@noextract_to "Plugin"]
let return0 #a #o #p (x:a)
  : SEA.SteelAtomicBase a true o Unobservable
                        (return_pre (p x)) p
                        (fun _ -> True)
                        (fun _ v _ -> v == x)
  = let _ = () in SEA.return x

[@@noextract_to "Plugin"]
let return #a #o #p x = coerce_atomicF (fun _ -> return0 x)

(* Lifting the separation logic exists combinator to vprop *)
let exists_ (#a:Type u#a) (p:a -> vprop)
  : vprop
  = SEA.h_exists p

let intro_can_be_split_exists
  a x p
=
  SEA.reveal_can_be_split ();
  Classical.forall_intro (Steel.Memory.intro_h_exists x (SEA.h_exists_sl' p))

let intro_can_be_split_forall_dep_exists
  b a x p
=
  let prf
    (y: b)
  : Lemma
    (p y (x y) `can_be_split` exists_ (p y))
  =
    intro_can_be_split_exists (a y) (x y) (p y)
  in
  Classical.forall_intro prf

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

let exists_equiv #a p1 p2
  = SEA.exists_equiv p1 p2

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
  = let f (x:unit)
      : SEA.SteelAtomicT a (add_inv opened_invariants i)
                           (p `star` fp)
                           (fun x -> p `star` fp' x) 
      = f () in
    coerce_atomic (fun _ -> SEA.with_invariant i f)

let with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  = let f (x:unit)
      : SEA.SteelGhostT a (add_inv opened_invariants i)
                          (p `star` fp)
                          (fun x -> p `star` fp' x) 
      = f () in
    coerce_ghost (fun _ -> SEA.with_invariant_g i f)

let par #aL #aR #preL #postL #preR #postR f g =
  let f : unit -> SE.SteelT aL preL postL = fun _ -> f () in
  let g : unit -> SE.SteelT aR preR postR = fun _ -> g () in    
  let p
    : unit -> SE.SteelT (aL & aR)
                       (preL `star` preR)
                       (fun y -> postL (fst y) `star` postR (snd y))
    = fun _ -> SE.par f g in
  coerce_steel p

let vpattern
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun _ -> p x) True (fun res -> res == x)
= noop ();
  x

let vpattern_replace
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun res -> p res) True (fun res -> res == x)
= noop ();
  x

let vpattern_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun _ -> p x) True (fun res -> Ghost.reveal res == x)
= noop ();
  x

let vpattern_replace_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun res -> p (Ghost.reveal res)) True (fun res -> Ghost.reveal res == x)
= noop ();
  x

let vpattern_replace_erased_global
  #opened #a #x #q p
= noop ();
  x

let vpattern_rewrite
  (#opened: _)
  (#a: Type)
  (#x1: a)
  (p: a -> vprop)
  (x2: a)
: STGhost unit opened
    (p x1)
    (fun _ -> p x2)
    (x1 == x2)
    (fun _ -> True)
= rewrite (p x1) (p x2)
