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

[@@ resolve_implicits; framing_implicit]
let init_resolve_tac0 () = init_resolve_tac ()

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
  a b x p
=
  let prf
    (y: b)
  : Lemma
    (p y (x y) `can_be_split` exists_ (p y))
  =
    intro_can_be_split_exists a (x y) (p y)
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
  = let f
      : unit -> SEA.SteelAtomicT a (add_inv opened_invariants i)
                                  (p `star` fp)
                                  (fun x -> p `star` fp' x) = f in
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
  = let f
      : unit -> SEA.SteelGhostT a (add_inv opened_invariants i)
                                 (p `star` fp)
                                 (fun x -> p `star` fp' x) = f in
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

let frame_gen_elim_f
  (#p: vprop)
  (#a: Type0) // FIXME: generalize this universe
  (#q: (a -> vprop))
  (#post: (a -> prop))
  (g: gen_elim_f p a q post)
  (opened: inames)
: STGhost (Ghost.erased a) opened p (fun x -> q (Ghost.reveal x)) True (fun x -> post x)
= g opened

let gen_unit_elim_id'
  (p: vprop)
: Tot (gen_unit_elim_f p p True)
= (fun _ -> noop (); Ghost.hide ())

let gen_elim_exists_unit_body'
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_unit_elim_t (p x))
: Tot (gen_elim_f (exists_ p) a (fun x -> gen_unit_elim_q (g x)) (fun x -> gen_unit_elim_post (g x)))
= fun opened ->
  let x = elim_exists () in
  let _ = GenUnitElim?.f (g x) opened in
  x

let gen_elim_exists''
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
  ()
: Tot (gen_elim_f (exists_ p) (dtuple2 a (fun x -> GenElim?.a (g x))) (fun y -> GenElim?.q (g (dfstp y)) (dsndp y)) (fun y -> GenElim?.post (g (dfstp y)) (dsndp y)))
= fun opened ->
  let x = elim_exists () in
  let y = GenElim?.f (g x) opened in
  let res = Ghost.hide (| Ghost.reveal x, Ghost.reveal y |) in
  res

let coerce_with_trefl (#tfrom tto: Type) (x: tfrom) : Pure tto (requires (T.with_tactic T.trefl (tfrom == tto))) (ensures (fun _ -> True)) = x

let gen_elim_exists'
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
: Tot (unit ->
      Tot (gen_elim_f (exists_ p) (dtuple2 a (fun x -> gen_elim_a (g x))) (fun y -> gen_elim_q (g (dfstp y)) (dsndp y)) (fun y -> gen_elim_post (g (dfstp y)) (dsndp y)))
  )
=
  coerce_with_trefl _ (gen_elim_exists'' a p g)

let gen_unit_elim_pure'
  (p: prop)
: Tot (gen_unit_elim_f (pure p) emp p)
= fun _ -> elim_pure _; ()

let gen_elim_star''
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
  ()
: Tot (gen_elim_f (p `star` q) (GenElim?.a gp & GenElim?.a gq) (fun x -> GenElim?.q gp (fstp x) `star` GenElim?.q gq (sndp x)) (fun x -> GenElim?.post gp (fstp x) /\ GenElim?.post gq (sndp x)))
= fun opened ->
  let xp = frame_gen_elim_f (GenElim?.f gp) opened in
  let xq = frame_gen_elim_f (GenElim?.f gq) opened in
  let res = Ghost.hide (Ghost.reveal xp, Ghost.reveal xq) in
  res

let gen_elim_star'
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gp & gen_elim_a gq) (fun x -> gen_elim_q gp (fstp x) `star` gen_elim_q gq (sndp x)) (fun x -> gen_elim_post gp (fstp x) /\ gen_elim_post gq (sndp x)))
=
  coerce_with_trefl _ (gen_elim_star'' p q gp gq)

let gen_elim_star_l''
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_unit_elim_t q)
  ()
: Tot (gen_elim_f (p `star` q) (GenElim?.a gp) (fun x -> GenElim?.q gp x `star` GenUnitElim?.q gq) (fun x -> GenElim?.post gp x /\ GenUnitElim?.post gq))
= fun opened ->
  let xp = frame_gen_elim_f (GenElim?.f gp) opened in
  let _ = frame_gen_elim_f (GenUnitElim?.f gq) opened in
  xp

let gen_elim_star_l'
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_unit_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gp) (fun x -> gen_elim_q gp x `star` gen_unit_elim_q gq) (fun x -> gen_elim_post gp x /\ gen_unit_elim_post gq))
=
  coerce_with_trefl _ (gen_elim_star_l'' p q gp gq)

let gen_elim_star_r''
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_elim_t q)
  ()
: Tot (gen_elim_f (p `star` q) (GenElim?.a gq) (fun x -> GenUnitElim?.q gp `star` GenElim?.q gq x) (fun x -> GenUnitElim?.post gp /\ GenElim?.post gq x))
= fun opened ->
  let _ = frame_gen_elim_f (GenUnitElim?.f gp) opened in
  let xq = frame_gen_elim_f (GenElim?.f gq) opened in
  xq

let gen_elim_star_r'
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gq) (fun x -> gen_unit_elim_q gp `star` gen_elim_q gq x) (fun x -> gen_unit_elim_post gp /\ gen_elim_post gq x))
=
  coerce_with_trefl _ (gen_elim_star_r'' p q gp gq)

let gen_unit_elim_star''
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_unit_elim_t q)
  ()
: Tot (gen_unit_elim_f (p `star` q) (GenUnitElim?.q gp `star` GenUnitElim?.q gq) (GenUnitElim?.post gp /\ GenUnitElim?.post gq))
= fun opened ->
  let _ = frame_gen_elim_f (GenUnitElim?.f gp) opened in
  let _ = frame_gen_elim_f (GenUnitElim?.f gq) opened in
  ()

let gen_unit_elim_star'
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_unit_elim_t q)
: unit ->
  Tot (gen_unit_elim_f (p `star` q) (gen_unit_elim_q gp `star` gen_unit_elim_q gq) (gen_unit_elim_post gp /\ gen_unit_elim_post gq))
=
  coerce_with_trefl _ (gen_unit_elim_star'' p q gp gq)

let gen_elim_prop
  p a q post
=
  exists (i: gen_elim_t p) .
  a == GenElim?.a i /\
  q == (fun (x: Ghost.erased a) -> GenElim?.q i x) /\
  post == (fun (x: Ghost.erased a) -> GenElim?.post i x)

let gen_elim_prop_intro
  p i dummy a sq_a post sq_post q sq_q
= ()

let gen_elim_prop_elim_
  (opened: _)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq: squash (gen_elim_prop p a q post))
: STGhost (Ghost.erased a) opened p q True post
= let f = FStar.IndefiniteDescription.indefinite_description_ghost (gen_elim_t p) (fun i -> a == GenElim?.a i /\ q == (fun (x: Ghost.erased a) -> GenElim?.q i x) /\ post == (fun (x: Ghost.erased a) -> GenElim?.post i x)) in
  let z : Ghost.erased (GenElim?.a f) = frame_gen_elim_f (GenElim?.f f) opened in
  let z' : Ghost.erased a = z in
  weaken (GenElim?.q f (Ghost.reveal z)) (q z') (fun _ -> reveal_can_be_split ());
  z'

let gen_elim_prop_elim
  #opened p a q post sq _
=
  gen_elim_prop_elim_ opened p a q post sq

let gen_elim
  #opened #p #a #q #post #sq _
= gen_elim_prop_elim p a q post () ()

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
