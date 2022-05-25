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
let pure = pure
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

irreducible let gen_elim_reduce = ()

let compute_gen_elim_a' = compute_gen_elim_a

let compute_gen_elim_q' = compute_gen_elim_q

let compute_gen_elim_post' = compute_gen_elim_post

let gen_elim_pred
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (ij: (gen_elim_i & gen_elim_nondep_t))
: Tot prop
= let (i, j) = ij in
  p == compute_gen_elim_p' i /\
  check_gen_elim_nondep_sem i j /\ 
  a == compute_gen_elim_nondep_a i j /\
  post == compute_gen_elim_nondep_post i j /\
  q == compute_gen_elim_nondep_q i j

let gen_elim_prop
  enable_nondep_opt p a q post
= exists ij . gen_elim_pred enable_nondep_opt p a q post ij

let gen_elim_prop_intro'
  i j enable_nondep_opt p a q post sq_p sq_j sq_a sq_q sq_post
= assert (gen_elim_pred enable_nondep_opt p a q post (i, j))

let gen_elim_prop_placeholder
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop
= True

let gen_elim_prop_placeholder_intro
  (enable_nondep_opt: bool)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot (squash (gen_elim_prop_placeholder enable_nondep_opt p a q post))
= ()

let gen_elim_f
  (p: vprop)
  (a: Type0) // FIXME: generalize this universe
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhost a opened p q True post)

let gen_unit_elim_t (i: gen_unit_elim_i) : Tot Type =
  gen_elim_f (compute_gen_unit_elim_p' i) unit (fun _ -> compute_gen_unit_elim_q' i) (fun _ -> compute_gen_unit_elim_post' i)

let compute_gen_unit_elim_f_id
  (v: vprop)
: Tot (gen_unit_elim_t (GUEId v))
= fun _ -> noop ()

let compute_gen_unit_elim_f_pure
  (p: prop)
: Tot (gen_unit_elim_t (GUEPure p))
= fun _ ->
  rewrite (compute_gen_unit_elim_p' (GUEPure p)) (pure p);
  elim_pure p

let compute_gen_unit_elim_f_star
  (i1 i2: gen_unit_elim_i)
  (f1: gen_unit_elim_t i1)
  (f2: gen_unit_elim_t i2)
: Tot (gen_unit_elim_t (GUEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_unit_elim_p' (GUEStar i1 i2)) (compute_gen_unit_elim_p' i1 `star` compute_gen_unit_elim_p' i2);
  f1 _; f2 _;
  rewrite (compute_gen_unit_elim_q' i1 `star` compute_gen_unit_elim_q' i2) (compute_gen_unit_elim_q' (GUEStar i1 i2))

let rec compute_gen_unit_elim_f
  (i: gen_unit_elim_i)
: Tot (gen_unit_elim_t i)
= match i returns (gen_unit_elim_t i) with
  | GUEId v -> compute_gen_unit_elim_f_id v
  | GUEPure p -> compute_gen_unit_elim_f_pure p
  | GUEStar i1 i2 -> compute_gen_unit_elim_f_star i1 i2 (compute_gen_unit_elim_f i1) (compute_gen_unit_elim_f i2)

let gen_elim_t (i: gen_elim_i) : Tot Type =
  gen_elim_f (compute_gen_elim_p' i) (compute_gen_elim_a' i) (compute_gen_elim_q' i) (compute_gen_elim_post' i)

let compute_gen_elim_f_unit
  (i: gen_unit_elim_i)
: Tot (gen_elim_t (GEUnit i))
= compute_gen_unit_elim_f i

let compute_gen_elim_f_star_l
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_unit_elim_i)
: Tot (gen_elim_t (GEStarL i1 i2))
= let f2 = compute_gen_unit_elim_f i2 in
  fun _ ->
  rewrite (compute_gen_elim_p' (GEStarL i1 i2)) (compute_gen_elim_p' i1 `star` compute_gen_unit_elim_p' i2);
  let res = f1 _ in
  f2 _;
  let res' : compute_gen_elim_a' (GEStarL i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_elim_q' i1 res `star` compute_gen_unit_elim_q' i2) (compute_gen_elim_q' (GEStarL i1 i2) res');
  res'

let compute_gen_elim_f_star_r
  (i1: gen_unit_elim_i)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: Tot (gen_elim_t (GEStarR i1 i2))
= let f1 = compute_gen_unit_elim_f i1 in
  fun _ ->
  rewrite (compute_gen_elim_p' (GEStarR i1 i2)) (compute_gen_unit_elim_p' i1 `star` compute_gen_elim_p' i2);
  f1 _;
  let res = f2 _ in
  let res' : compute_gen_elim_a' (GEStarR i1 i2) = coerce_with_trefl res in
  rewrite (compute_gen_unit_elim_q' i1 `star` compute_gen_elim_q' i2 res) (compute_gen_elim_q' (GEStarR i1 i2) res');
  res'

let compute_gen_elim_f_star
  (i1: gen_elim_i)
  (f1: gen_elim_t i1)
  (i2: gen_elim_i)
  (f2: gen_elim_t i2)
: Tot (gen_elim_t (GEStar i1 i2))
= fun _ ->
  rewrite (compute_gen_elim_p' (GEStar i1 i2)) (compute_gen_elim_p' i1 `star` compute_gen_elim_p' i2);
  let res1 = f1 _ in
  let res2 = f2 _ in
  let res : compute_gen_elim_a' (GEStar i1 i2) = coerce_with_trefl (res1, res2) in
  rewrite (compute_gen_elim_q' i1 res1 `star` compute_gen_elim_q' i2 res2) (compute_gen_elim_q' (GEStar i1 i2) res);
  res

let compute_gen_elim_f_exists_no_abs
  (a: Type0)
  (body: (a -> vprop))
: Tot (gen_elim_t (GEExistsNoAbs body))
= fun _ ->
  rewrite (compute_gen_elim_p' (GEExistsNoAbs body)) (exists_ body);
  let gres = elim_exists () in
  let res : compute_gen_elim_a' (GEExistsNoAbs body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (body gres) (compute_gen_elim_q' (GEExistsNoAbs body) res);
  res

let rewrite_with_trefl (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic T.trefl (p == q))
      (ensures fun _ -> True)
= rewrite p q

let compute_gen_elim_f_exists_unit
  (a: Type0)
  (body: a -> gen_unit_elim_i)
: Tot (gen_elim_t (GEExistsUnit body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p' (GEExistsUnit body)) (exists_ (fun x -> compute_gen_unit_elim_p' (body x)));
  let gres = elim_exists () in
  compute_gen_unit_elim_f (body gres) _;
  let res : compute_gen_elim_a' (GEExistsUnit body) = coerce_with_trefl (Ghost.reveal gres) in
  rewrite (compute_gen_unit_elim_q' (body gres)) (compute_gen_elim_q' (GEExistsUnit body) res);
  res

let compute_gen_elim_f_exists
  (a: Type0)
  (body: a -> gen_elim_i)
  (f: (x: a) -> gen_elim_t (body x))
: Tot (gen_elim_t (GEExists body))
= fun _ ->
  rewrite_with_trefl (compute_gen_elim_p' (GEExists body)) (exists_ (fun x -> compute_gen_elim_p' (body x)));
  let gres1 = elim_exists () in
  let gres2 = f gres1 _ in
  let res : compute_gen_elim_a' (GEExists body) = coerce_with_trefl (Mkdtuple2 #a #(fun x -> compute_gen_elim_a' (body x)) (Ghost.reveal gres1) (Ghost.reveal gres2)) in
  rewrite (compute_gen_elim_q' (body gres1) gres2) (compute_gen_elim_q' (GEExists body) res);
  res

let rec compute_gen_elim_f
  (i: gen_elim_i)
: Tot (gen_elim_t i)
= match i returns (gen_elim_t i) with
  | GEUnit i -> compute_gen_elim_f_unit i
  | GEStarL i1 i2 -> compute_gen_elim_f_star_l i1 (compute_gen_elim_f i1) i2
  | GEStarR i1 i2 -> compute_gen_elim_f_star_r i1 i2 (compute_gen_elim_f i2)
  | GEStar i1 i2 -> compute_gen_elim_f_star i1 (compute_gen_elim_f i1) i2 (compute_gen_elim_f i2)
  | GEExistsNoAbs body -> compute_gen_elim_f_exists_no_abs _ body
  | GEExistsUnit body -> compute_gen_elim_f_exists_unit _ body
  | GEExists body -> compute_gen_elim_f_exists _ body (fun x -> compute_gen_elim_f (body x))

let coerce_with_smt (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires ( (tfrom == tto))) (ensures (fun _ -> True)) = x

let gen_elim' = admit ()
(*
  #opened p i a q post sq _
= rewrite p (compute_gen_elim_p' i);
  let vres' : compute_gen_elim_a' i = compute_gen_elim_f i _ in
  let vres : a = coerce_with_smt #(compute_gen_elim_a' i) vres' in
  let res : Ghost.erased a = Ghost.hide vres in
  rewrite (compute_gen_elim_q' i vres') (q res);
  res
*)

let gen_elim
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()

let gen_elim_dep
  #opened #p #a #q #post #sq _
= gen_elim' #opened _ p a q post sq ()

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
