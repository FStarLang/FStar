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
(** This module aggregates several of the core effects and utilities
    associated with the Steel.ST namespace.

    Client modules should typically just [open Steel.ST.Util] and
    that should bring most of what they need in scope.
*)
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe
include Steel.FractionalPermission
include Steel.Memory
include Steel.Effect.Common
include Steel.ST.Effect
include Steel.ST.Effect.Atomic
include Steel.ST.Effect.Ghost

module T = FStar.Tactics

/// Weaken a vprop from [p] to [q]
/// of every memory validating [p] also validates [q]
val weaken (#opened:inames)
           (p q:vprop)
           (l:(m:mem) -> Lemma
                           (requires interp (hp_of p) m)
                           (ensures interp (hp_of q) m))
  : STGhostT unit opened p (fun _ -> q)

/// Rewrite [p] to [q] when they are equal
val rewrite (#opened:inames)
            (p q: vprop)
  : STGhost unit opened p (fun _ -> q) (p == q) (fun _ -> True)

/// Rewrite p to q, proving their equivalence using the framing tactic
/// Most places, this rewriting kicks in automatically in the framework,
///   but sometimes it is useful to explicitly rewrite, while farming AC reasoning
///   to the tactic
val rewrite_with_tactic (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic init_resolve_tac (squash (p `equiv` q)))
      (ensures fun _ -> True)

/// This rewrite is useful when you have equiv predicate in the logical context
/// Internally implemented using `weaken`
val rewrite_equiv (#opened:_) (p q:vprop)
  : STGhost unit opened p (fun _ -> q)
      (requires equiv p q \/ equiv q p)
      (ensures fun _ -> True)

/// A noop operator, occasionally useful for forcing framing of a
/// subsequent computation
val noop (#opened:inames) (_:unit)
  : STGhostT unit opened emp (fun _ -> emp)

/// Asserts the validity of vprop [p] in the current context
val assert_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants p (fun _ -> p)

/// Allows assuming [p] for free
/// See also Steel.ST.Effect.Ghost.admit_
[@@warn_on_use "uses an axiom"]
val assume_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants emp (fun _ -> p)

/// Drops vprop [p] from the context. Although our separation logic is
/// affine, the frame inference tactic treats it as linear.
/// Leveraging affinity requires a call from the user to this helper,
/// to avoid implicit memory leaks.  This should only be used for pure
/// and ghost vprops
val drop (#opened:inames) (p:vprop) : STGhostT unit opened p (fun _ -> emp)

/// A pure vprop
val pure (p: prop) : vprop

/// Introduce a pure vprop, when [p] is valid in the context
val intro_pure (#uses:_) (p:prop)
  : STGhost unit uses emp (fun _ -> pure p) p (fun _ -> True)

/// Eliminate a pure vprop, gaining that p is valid in the context
val elim_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> emp) True (fun _ -> p)

/// Extracting a proposition from a [pure p] while retaining [pure p]
val extract_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> pure p) True (fun _ -> p)

/// Useful lemmas to make the framing tactic automatically handle `pure`

[@@solve_can_be_split_lookup; (solve_can_be_split_for pure)]
val intro_can_be_split_pure
  (p: prop)
  (sq: squash p)
: Lemma (emp `can_be_split` pure p)

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for pure)]
val intro_can_be_split_forall_dep_pure
  (#a: Type)
  (p: a -> Tot prop)
: Lemma (can_be_split_forall_dep p (fun _ -> emp) (fun x -> pure (p x)))

/// It's generally good practice to end a computation with a [return].
///
/// It becomes necessary when combining ghost and non-ghost
/// computations, so it is often less surprising to always write it.
///
/// Because of the left-associative structure of F* computations, this
/// is necessary when a computation is atomic and returning a value
/// with an informative type, but the previous computation was ghost.
/// Else, the returned value will be given type SteelGhost, and F*
/// will fail to typecheck the program as it will try to lift a
/// SteelGhost computation with an informative return type
[@@noextract_to "Plugin"]
val return (#a:Type u#a)
           (#opened_invariants:inames)
           (#p:a -> vprop)
           (x:a)
  : STAtomicBase a true opened_invariants Unobservable
                 (return_pre (p x)) p
                 True
                 (fun v -> v == x)

/// An existential quantifier for vprop
val exists_ (#a:Type u#a) (p:a -> vprop) : vprop

/// Useful lemmas to make the framing tactic automatically handle `exists_`
[@@solve_can_be_split_lookup; (solve_can_be_split_for exists_)]
val intro_can_be_split_exists (a:Type) (x:a) (p: a -> vprop)
  : Lemma
    (ensures (p x `can_be_split` (exists_ p)))

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for exists_)]
val intro_can_be_split_forall_dep_exists (b:Type) (a: b -> Type)
                           (x: (u: b) -> GTot (a u))
                           (p: (u: b) -> a u -> vprop)
  : Lemma
    (ensures (fun (y:b) -> p y (x y)) `(can_be_split_forall_dep (fun _ -> True))` (fun (y:b) -> exists_ (p y)))

/// Introducing an existential if the predicate [p] currently holds for value [x]
val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Variant of intro_exists above, when the witness is a ghost value
val intro_exists_erased (#a:Type)
                        (#opened_invariants:_)
                        (x:Ghost.erased a)
                        (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Extracting a witness for predicate [p] if it currently holds for some [x]
val elim_exists (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT (Ghost.erased a) opened_invariants
             (exists_ p)
             (fun x -> p x)

/// Lifting the existentially quantified predicate to a higher universe
val lift_exists (#a:_)
                (#u:_)
                (p:a -> vprop)
  : STGhostT unit u
             (exists_ p)
             (fun _a -> exists_ #(U.raise_t a) (U.lift_dom p))

/// If two predicates [p] and [q] are equivalent, then their existentially quantified versions
/// are equivalent, and we can switch from `h_exists p` to `h_exists q`
val exists_cong (#a:_)
                (#u:_)
                (p:a -> vprop)
                (q:a -> vprop {forall x. equiv (p x) (q x) })
  : STGhostT unit u
             (exists_ p)
             (fun _ -> exists_ q)

/// Creation of a new invariant associated to vprop [p].
/// After execution of this function, [p] is consumed and not available in the context anymore
val new_invariant (#opened_invariants:inames) (p:vprop)
  : STGhostT (inv p) opened_invariants p (fun _ -> emp)

/// Atomically executing function [f] which relies on the predicate [p] stored in invariant [i]
/// as long as it maintains the validity of [p]
/// This requires invariant [i] to not belong to the set of currently opened invariants.
[@@noextract_to "Plugin"]
val with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> STAtomicT a (add_inv opened_invariants i)
                                          (p `star` fp)
                                          (fun x -> p `star` fp' x))
  : STAtomicT a opened_invariants fp fp'

/// Variant of the above combinator for ghost computations
val with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostT a opened_invariants fp fp'

/// Parallel composition of two STT functions
[@@noextract_to "Plugin"]
val par
  (#aL:Type u#a)
  (#aR:Type u#a)
  (#preL:vprop)
  (#postL:aL -> vprop)
  (#preR:vprop)
  (#postR:aR -> vprop)
  ($f:unit -> STT aL preL postL)
  ($g:unit -> STT aR preR postR)
  : STT (aL & aR)
        (preL `star` preR)
        (fun y -> postL (fst y) `star` postR (snd y))

/// A tactic to automatically generate a unique binder

noeq
type gen_unit_elim_i
= | GUEId: (v: vprop) -> gen_unit_elim_i
  | GUEPure: (p: prop) -> gen_unit_elim_i
  | GUEStar: (left: gen_unit_elim_i) -> (right: gen_unit_elim_i) -> gen_unit_elim_i

noeq
type gen_elim_i =
  | GEUnit: (i: gen_unit_elim_i) -> gen_elim_i
  | GEStarL: (left: gen_elim_i) -> (right: gen_unit_elim_i) -> gen_elim_i
  | GEStarR: (left: gen_unit_elim_i) -> (right: gen_elim_i) -> gen_elim_i
  | GEStar: (left: gen_elim_i) -> (right: gen_elim_i) -> gen_elim_i
  | GEExistsNoAbs: (#a: Type0) -> (body: (a -> vprop)) -> gen_elim_i // FIXME: generalize the universe
  | GEExistsUnit: (#a: Type0) -> (body: (a -> gen_unit_elim_i)) -> gen_elim_i
  | GEExists: (#a: Type0) -> (body: (a -> gen_elim_i)) -> gen_elim_i

[@__reduce__]
let rec compute_gen_unit_elim_p
  (x: gen_unit_elim_i)
: Tot vprop
= match x with
  | GUEId v -> v
  | GUEPure p -> pure p
  | GUEStar left right -> compute_gen_unit_elim_p left `star` compute_gen_unit_elim_p right

let compute_gen_unit_elim_p' = compute_gen_unit_elim_p

[@__reduce__]
let rec compute_gen_unit_elim_q
  (x: gen_unit_elim_i)
: Tot vprop
= match x with
  | GUEId v -> v
  | GUEPure _ -> emp
  | GUEStar left right -> compute_gen_unit_elim_q left `star` compute_gen_unit_elim_q right

let compute_gen_unit_elim_q' = compute_gen_unit_elim_q

[@@__reduce__; __steel_reduce__]
let rec compute_gen_unit_elim_post
  (x: gen_unit_elim_i)
: Tot prop
= match x with
  | GUEId _ -> True
  | GUEPure p -> p
  | GUEStar left right -> compute_gen_unit_elim_post left /\ compute_gen_unit_elim_post right

let compute_gen_unit_elim_post' = compute_gen_unit_elim_post

[@@__reduce__]
let rec compute_gen_elim_p
  (x: gen_elim_i)
: Tot vprop
= match x with
  | GEUnit i -> compute_gen_unit_elim_p i
  | GEStarL left right -> compute_gen_elim_p left `star` compute_gen_unit_elim_p right
  | GEStarR left right -> compute_gen_unit_elim_p left `star` compute_gen_elim_p right
  | GEStar left right -> compute_gen_elim_p left `star` compute_gen_elim_p right
  | GEExistsNoAbs #a p -> exists_ p
  | GEExistsUnit #a p -> exists_ (fun x -> compute_gen_unit_elim_p (p x))
  | GEExists #a body -> exists_ (fun x -> compute_gen_elim_p (body x))

[@@ __reduce__; __steel_reduce__]
let rec compute_gen_elim_a
  (x: gen_elim_i)
: Tot Type0
= match x with
  | GEUnit _ -> unit
  | GEStarL left _ -> compute_gen_elim_a left
  | GEStarR _ right -> compute_gen_elim_a right
  | GEStar left right -> (compute_gen_elim_a left & compute_gen_elim_a right)
  | GEExistsNoAbs #a _
  | GEExistsUnit #a _ -> a
  | GEExists #a body -> dtuple2 a (fun x -> compute_gen_elim_a (body x))

let dfstp #a #b t = dfst #a #b t
let dsndp #a #b t = dsnd #a #b t
let fstp #a #b t = fst #a #b t
let sndp #a #b t = snd #a #b t

[@@__reduce__; __steel_reduce__]
let coerce_with_trefl (#tfrom #tto: Type) (x: tfrom) : Pure tto (requires (T.with_tactic T.trefl (tfrom == tto))) (ensures (fun _ -> True)) = x

[@@__reduce__]
let rec compute_gen_elim_q
  (x: gen_elim_i)
: Tot (compute_gen_elim_a x -> Tot vprop)
  (decreases x)
= match x as x' returns (compute_gen_elim_a x' -> Tot vprop) with
  | GEUnit u -> fun _ -> compute_gen_unit_elim_q u
  | GEStarL left right -> fun v -> compute_gen_elim_q left (coerce_with_trefl v) `star` compute_gen_unit_elim_q right
  | GEStarR left right -> fun v -> compute_gen_unit_elim_q left `star` compute_gen_elim_q right (coerce_with_trefl v)
  | GEStar left right -> fun v -> compute_gen_elim_q left (fstp #(compute_gen_elim_a left) #(compute_gen_elim_a right) (coerce_with_trefl v)) `star` compute_gen_elim_q right (sndp #(compute_gen_elim_a left) #(compute_gen_elim_a right) (coerce_with_trefl v))
  | GEExistsNoAbs #a p -> p
  | GEExistsUnit #a p -> fun v -> compute_gen_unit_elim_q (p v)
  | GEExists #a body -> fun v ->
    compute_gen_elim_q
      (body (dfstp #a #(fun x -> compute_gen_elim_a (body x)) (coerce_with_trefl v)))
      (dsndp #a #(fun x -> compute_gen_elim_a (body x)) (coerce_with_trefl v))

[@@__reduce__; __steel_reduce__]
let rec compute_gen_elim_post
  (x: gen_elim_i)
: Tot (compute_gen_elim_a x -> Tot prop)
  (decreases x)
= match x as x' returns (compute_gen_elim_a x' -> Tot prop) with
  | GEUnit u -> fun _ -> compute_gen_unit_elim_post u
  | GEStarL left right -> fun v -> compute_gen_elim_post left (coerce_with_trefl v) /\ compute_gen_unit_elim_post right
  | GEStarR left right -> fun v -> compute_gen_unit_elim_post left /\ compute_gen_elim_post right (coerce_with_trefl v)
  | GEStar left right -> fun v -> compute_gen_elim_post left (fstp #(compute_gen_elim_a left) #(compute_gen_elim_a right) (coerce_with_trefl v)) /\ compute_gen_elim_post right (sndp #(compute_gen_elim_a left) #(compute_gen_elim_a right) (coerce_with_trefl v))
  | GEExistsNoAbs #a p -> fun _ -> True
  | GEExistsUnit #a p -> fun v -> compute_gen_unit_elim_post (p v)
  | GEExists #a body -> fun v ->
    compute_gen_elim_post
      (body (dfstp #a #(fun x -> compute_gen_elim_a (body x)) (coerce_with_trefl v)))
      (dsndp #a #(fun x -> compute_gen_elim_a (body x)) (coerce_with_trefl v))

module T = FStar.Tactics

let rec term_has_head
  (t: T.term)
  (head: T.term)
: T.Tac bool
= let (hd, tl) = T.collect_app t in
  if hd `T.term_eq` head
  then true
  else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
  then
    match tl with
    | [tg, T.Q_Explicit; td, T.Q_Explicit] ->
      if term_has_head tg head
      then true
      else term_has_head td head
    | _ -> false
  else false

let rec solve_gen_unit_elim
  (tl': T.term)
: T.Tac T.term
= 
      if not (term_has_head tl' (`pure))
      then T.mk_app (`GUEId) [tl', T.Q_Explicit]
      else
        let (hd, tl) = T.collect_app tl' in
        if hd `T.term_eq` (`pure)
        then T.mk_app (`GUEPure) tl
        else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
        then match tl with
        | [t1, T.Q_Explicit; t2, T.Q_Explicit] ->
          let t1' = solve_gen_unit_elim t1 in
          let t2' = solve_gen_unit_elim t2 in
          T.mk_app (`GUEStar) [t1', T.Q_Explicit; t2', T.Q_Explicit]
        | _ -> T.fail "ill-formed star"
        else
          T.mk_app (`GUEId) [tl', T.Q_Explicit]

let abstr_has_exists
  (t: T.term)
: T.Tac bool
= match T.inspect t with
  | T.Tv_Abs _ body -> term_has_head body (`exists_)
  | _ -> false

let rec solve_gen_elim
  (tl': T.term)
: T.Tac T.term
= 
      if not (term_has_head tl' (`exists_))
      then begin
        let t' = solve_gen_unit_elim tl' in
        T.mk_app (`GEUnit) [t', T.Q_Explicit]
      end else
        let (hd, lbody) = T.collect_app tl' in
        if hd `T.term_eq` (`exists_)
        then
          let (ty, body) =
            match lbody with
            | [(ty, T.Q_Implicit); (body, T.Q_Explicit)] -> ([(ty, T.Q_Implicit)], body)
            | [(body, T.Q_Explicit)] -> ([], body)
            | _ -> T.fail "ill-formed exists_"
          in
          begin match T.inspect body with
            | T.Tv_Abs b abody ->
              if not (term_has_head abody (`exists_))
              then
                let body' = solve_gen_unit_elim abody in
                T.mk_app (`GEExistsUnit) (ty `List.Tot.append` [T.mk_abs [b] body', T.Q_Explicit])
              else
                let body' = solve_gen_elim abody in
                T.mk_app (`GEExists) (ty `List.Tot.append` [T.mk_abs [b] body', T.Q_Explicit])
            | _ ->
              T.mk_app (`GEExistsNoAbs) lbody
          end
        else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
        then
          match lbody with
          | [(tl, T.Q_Explicit); (tr, T.Q_Explicit)] ->
            if term_has_head tl (`exists_)
            then
              let tl' = solve_gen_elim tl in
              if term_has_head tr (`exists_)
              then
                let tr' = solve_gen_elim tr in
                T.mk_app (`GEStar) [tl', T.Q_Explicit; tr', T.Q_Explicit]
              else
                let tr' = solve_gen_unit_elim tr in
                T.mk_app (`GEStarL) [tl', T.Q_Explicit; tr', T.Q_Explicit]
            else (* here, term_has_head tr (`exists_) holds, because otherwise we are in case (not (term_has_head tl (`exists_))) above *)
              let tl' = solve_gen_unit_elim tl in
              let tr' = solve_gen_elim tr in
              T.mk_app (`GEStarR) [tl', T.Q_Explicit; tr', T.Q_Explicit]
          | _ -> T.fail "ill-formed star"
        else
          T.mk_app (`GEUnit) [T.mk_app (`GUEId) lbody, T.Q_Explicit]

val gen_elim_prop
  (p: vprop)
  (i: gen_elim_i)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop

val gen_elim_prop_intro
  (p: vprop)
  (i: gen_elim_i)
  (sq_p: squash (p == compute_gen_elim_p i))
  (a: Type0)
  (sq_a: squash (a == compute_gen_elim_a i))
  (post: Ghost.erased a -> Tot prop)
  (sq_post: squash (post == (fun (x: Ghost.erased a) -> compute_gen_elim_post i x)))
  (q: Ghost.erased a -> Tot vprop)
  (sq_q: squash (q == (fun (x: Ghost.erased a) -> compute_gen_elim_q i x)))
: Lemma (gen_elim_prop p i a q post)

let gen_elim_prop_placeholder
  (p: vprop)
  (i: gen_elim_i)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop
= True

let gen_elim_dummy
  (p: vprop)
  (i: gen_elim_i)
: Tot prop
= True

let gen_elim_dummy_intro
  (p: vprop)
  (i: gen_elim_i)
: Tot (squash (gen_elim_dummy p i))
= ()

let gen_elim_prop_placeholder_intro
  (p: vprop)
  (i: gen_elim_i)
  (dummy: squash (gen_elim_dummy p i))
  (sq_p: squash (p == compute_gen_elim_p i))
  (a: Type0)
  (sq_a: squash (a == compute_gen_elim_a i))
  (post: Ghost.erased a -> Tot prop)
  (sq_post: squash (post == (fun (x: Ghost.erased a) -> compute_gen_elim_post i x)))
  (q: Ghost.erased a -> Tot vprop)
  (sq_q: squash (q == (fun (x: Ghost.erased a) -> compute_gen_elim_q i x)))
: Lemma (gen_elim_prop_placeholder p i a q post)
= ()

let solve_gen_elim_dummy
  ()
: T.Tac unit
=
      let (hd, tl) = T.collect_app (T.cur_goal ()) in
      if not (hd `T.term_eq` (`squash) || hd `T.term_eq` (`auto_squash))
      then T.fail "not a squash goal";
      match tl with
      | [body1, T.Q_Explicit] ->
        let (hd1, tl1) = T.collect_app body1 in
        if not (hd1 `T.term_eq` (`gen_elim_dummy))
        then T.fail "not a gen_elim_dummy goal";
        begin match List.Tot.filter (fun (_, x) -> T.Q_Explicit? x) tl1 with
        | [(p, _); (i, _)] ->
          if slterm_nbr_uvars p <> 0
          then T.fail "pre-resource not solved yet";
          if not (T.Tv_Uvar? (T.inspect i))
          then T.fail "gen_elim_dummy is already solved";
          let i' = solve_gen_elim p in
          T.exact (T.mk_app (`gen_elim_dummy_intro) [(p, T.Q_Explicit); (i', T.Q_Explicit)])
        | _ -> T.fail "ill-formed gen_elim_dummy"
        end
      | _ -> T.fail "ill-formed squash"

let solve_gen_elim_prop
  ()
: T.Tac unit
=
  let (hd, tl) = T.collect_app (T.cur_goal ()) in
  if not (hd `T.term_eq` (`squash) || hd `T.term_eq` (`auto_squash))
  then T.fail "not a squash goal";
  match tl with
  | [body1, T.Q_Explicit] ->
    let (hd1, tl1) = T.collect_app body1 in
    if not (hd1 `T.term_eq` (`gen_elim_prop))
    then T.fail "not a gen_elim_prop goal";
    T.apply_lemma (`gen_elim_prop_intro);
    let norm () = T.norm [delta_attr [(`%__reduce__)]; zeta; iota] in
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ())
  | _ -> T.fail "ill-formed squash"

val gen_elim'
  (#opened: _)
  (p: vprop)
  (i: gen_elim_i)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq: squash (gen_elim_prop_placeholder p i a q post))
  (_: unit)
: STGhost (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) (gen_elim_prop p i a q post) post

val gen_elim
  (#opened: _)
  (#[@@@ framing_implicit] p: vprop)
  (#[@@@ framing_implicit] i: gen_elim_i)
  (#[@@@ framing_implicit] a: Type0)
  (#[@@@ framing_implicit] q: Ghost.erased a -> Tot vprop)
  (#[@@@ framing_implicit] post: Ghost.erased a -> Tot prop)
  (#[@@@ framing_implicit] sq: squash (gen_elim_prop_placeholder p i a q post))
  (_: unit)
: STGhostF (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) ( (T.with_tactic solve_gen_elim_prop) (squash (gen_elim_prop p i a q post))) post

let solve_gen_elim_prop_placeholder
  ()
: T.Tac bool
=
  let (hd, tl) = T.collect_app (T.cur_goal ()) in
  if not (hd `T.term_eq` (`squash) || hd `T.term_eq` (`auto_squash))
  then T.fail "not a squash goal";
  match tl with
  | [body1, T.Q_Explicit] ->
    let (hd1, tl1) = T.collect_app body1 in
    if not (hd1 `T.term_eq` (`gen_elim_prop_placeholder))
    then T.fail "not a gen_elim_prop_placeholder goal";
    T.apply_lemma (`gen_elim_prop_placeholder_intro);
    T.focus solve_gen_elim_dummy;
    let norm () = T.norm [delta_attr [(`%__reduce__)]; zeta; iota] in
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    true
  | _ -> T.fail "ill-formed squash"

/// Extracts an argument to a vprop from the context. This can be useful if we do need binders for some of the existentials opened by gen_elim.

val vpattern
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun _ -> p x) True (fun res -> res == x)

val vpattern_replace
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun res -> p res) True (fun res -> res == x)

val vpattern_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun _ -> p x) True (fun res -> Ghost.reveal res == x)

val vpattern_replace_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun res -> p (Ghost.reveal res)) True (fun res -> Ghost.reveal res == x)

val vpattern_replace_erased_global
  (#opened: _)
  (#a: Type)
  (#x: a)
  (#q: a -> vprop)
  (p: a -> vprop)
: STGhostF (Ghost.erased a) opened (p x `star` q x) (fun res -> p (Ghost.reveal res) `star` q (Ghost.reveal res)) True (fun res -> Ghost.reveal res == x)

[@@ resolve_implicits; framing_implicit; plugin]
let init_resolve_tac () = init_resolve_tac'
  [(`gen_elim_prop_placeholder), solve_gen_elim_prop_placeholder]
