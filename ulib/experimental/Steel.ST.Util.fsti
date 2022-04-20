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
val intro_can_be_split_forall_dep_exists (a:Type) (b:Type)
                           (x:b -> GTot a)
                           (p: b -> a -> vprop)
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

let gen_elim_f
  (p: vprop)
  (a: Type0) // FIXME: generalize this universe
  (q: (a -> vprop))
  (post: (a -> prop))
: Tot Type
= ((opened: inames) -> STGhostF (Ghost.erased a) opened p (fun x -> q (Ghost.reveal x)) True (fun x -> post x))

val frame_gen_elim_f
  (#p: vprop)
  (#a: Type0) // FIXME: generalize this universe
  (#q: (a -> vprop))
  (#post: (a -> prop))
  (g: gen_elim_f p a q post)
  (opened: inames)
: STGhost (Ghost.erased a) opened p (fun x -> q (Ghost.reveal x)) True (fun x -> post x)

[@@erasable]
noeq
type gen_elim_t
  (p: vprop)
= | GenElim:
    a: Type0 ->
    q: (a -> vprop) ->
    post: (a -> prop) ->
    f: gen_elim_f p a q post ->
    gen_elim_t p

[@@__reduce__; __steel_reduce__]
let gen_elim_a
  (#p: vprop)
  (g: gen_elim_t p)
: Tot Type0
= match g with
  | GenElim a _ _ _ -> a

[@@__reduce__]
let gen_elim_q
  (#p: vprop)
  (g: gen_elim_t p)
: Tot (gen_elim_a g -> Tot vprop)
= match g with
  | GenElim _ q _ _ -> q

[@@__reduce__]
let gen_elim_post
  (#p: vprop)
  (g: gen_elim_t p)
: Tot (gen_elim_a g -> Tot prop)
= match g with
  | GenElim _ _ post _ -> post

let gen_unit_elim_f
  (p: vprop)
  (q: vprop)
  (post: prop)
: Tot Type
= gen_elim_f p unit (fun _ -> q) (fun _ -> post)

[@@erasable]
noeq
type gen_unit_elim_t
  (p: vprop)
= | GenUnitElim:
    q: vprop ->
    post: prop ->
    f: gen_unit_elim_f p q post ->
    gen_unit_elim_t p

[@@__reduce__]
let gen_unit_elim_q
  (#p: vprop)
  (g: gen_unit_elim_t p)
: Tot vprop
= match g with
  | GenUnitElim q _ _ -> q

[@@__reduce__]
let gen_unit_elim_post
  (#p: vprop)
  (g: gen_unit_elim_t p)
: Tot prop
= match g with
  | GenUnitElim _ post _ -> post

[@@__reduce__; __steel_reduce__]
let gen_elim_of_gen_unit_elim
  (#p: vprop)
  (g: gen_unit_elim_t p)
: Tot (gen_elim_t p)
= GenElim unit (fun _ -> gen_unit_elim_q g) (fun _ -> gen_unit_elim_post g) (GenUnitElim?.f g)

val gen_unit_elim_id'
  (p: vprop)
: Tot (gen_unit_elim_f p p True)

[@@ __reduce__; __steel_reduce__]
let gen_unit_elim_id
  (p: vprop)
: Tot (gen_unit_elim_t p)
= GenUnitElim
    _
    _
    (gen_unit_elim_id' p)

[@@ __reduce__; __steel_reduce__]
let gen_elim_id
  (p: vprop)
: Tot (gen_elim_t p)
= gen_elim_of_gen_unit_elim (gen_unit_elim_id p)

val gen_elim_exists_unit_body'
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_unit_elim_t (p x))
: Tot (gen_elim_f (exists_ p) a (fun x -> gen_unit_elim_q (g x)) (fun x -> gen_unit_elim_post (g x)))

[@@__reduce__; __steel_reduce__]
let gen_elim_exists_unit_body
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_unit_elim_t (p x))
: Tot (gen_elim_t (exists_ p))
= GenElim
    _
    _
    _
    (gen_elim_exists_unit_body' a p g)

[@@__reduce__; __steel_reduce__]
let gen_elim_exists_simple
  (a: Type0)
  (p: a -> Tot vprop)
: Tot (gen_elim_t (exists_ p))
= gen_elim_exists_unit_body a p (fun x -> gen_unit_elim_id (p x))

let dfstp #a #b t = dfst #a #b t
let dsndp #a #b t = dsnd #a #b t
let fstp #a #b t = fst #a #b t
let sndp #a #b t = snd #a #b t

val gen_elim_exists'
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
: Tot (unit ->
      Tot (gen_elim_f (exists_ p) (dtuple2 a (fun x -> gen_elim_a (g x))) (fun y -> gen_elim_q (g (dfstp y)) (dsndp y)) (fun y -> gen_elim_post (g (dfstp y)) (dsndp y)))
  )

[@@__reduce__; __steel_reduce__]
let gen_elim_exists
  (a: Type0)
  (p: a -> Tot vprop)
  (g: (x: a) -> gen_elim_t (p x))
: Tot (gen_elim_t (exists_ p))
= GenElim _ _ _ (gen_elim_exists' a p g ())

#set-options "--ide_id_info_off"

val gen_unit_elim_pure'
  (p: prop)
: Tot (gen_unit_elim_f (pure p) emp p)

[@@__reduce__; __steel_reduce__]
let gen_unit_elim_pure
  (p: prop)
: Tot (gen_unit_elim_t (pure p))
= GenUnitElim _ _ (gen_unit_elim_pure' p)

[@@__reduce__; __steel_reduce__]
let gen_elim_pure
  (p: prop)
: Tot (gen_elim_t (pure p))
= gen_elim_of_gen_unit_elim (gen_unit_elim_pure p)

val gen_elim_star'
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gp & gen_elim_a gq) (fun x -> gen_elim_q gp (fstp x) `star` gen_elim_q gq (sndp x)) (fun x -> gen_elim_post gp (fstp x) /\ gen_elim_post gq (sndp x)))

[@@__reduce__; __steel_reduce__]
let gen_elim_star
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_elim_t q)
: Tot (gen_elim_t (p `star` q))
= GenElim _ _ _ (gen_elim_star' p q gp gq ())

val gen_elim_star_l'
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_unit_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gp) (fun x -> gen_elim_q gp x `star` gen_unit_elim_q gq) (fun x -> gen_elim_post gp x /\ gen_unit_elim_post gq))

[@@__reduce__; __steel_reduce__]
let gen_elim_star_l
  (p q: vprop)
  (gp: gen_elim_t p)
  (gq: gen_unit_elim_t q)
: Tot (gen_elim_t (p `star` q))
= GenElim _ _ _ (gen_elim_star_l' p q gp gq ())

val gen_elim_star_r'
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_elim_t q)
: unit ->
  Tot (gen_elim_f (p `star` q) (gen_elim_a gq) (fun x -> gen_unit_elim_q gp `star` gen_elim_q gq x) (fun x -> gen_unit_elim_post gp /\ gen_elim_post gq x))

[@@__reduce__; __steel_reduce__]
let gen_elim_star_r
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_elim_t q)
: Tot (gen_elim_t (p `star` q))
= GenElim _ _ _ (gen_elim_star_r' p q gp gq ())

val gen_unit_elim_star'
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_unit_elim_t q)
: unit ->
  Tot (gen_unit_elim_f (p `star` q) (gen_unit_elim_q gp `star` gen_unit_elim_q gq) (gen_unit_elim_post gp /\ gen_unit_elim_post gq))

[@@__reduce__; __steel_reduce__]
let gen_unit_elim_star
  (p q: vprop)
  (gp: gen_unit_elim_t p)
  (gq: gen_unit_elim_t q)
: Tot (gen_unit_elim_t (p `star` q))
= GenUnitElim _ _ (gen_unit_elim_star' p q gp gq ())

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
  ()
: T.Tac unit
= 
  T.focus (fun _ ->
    T.norm [];
    let g = T.cur_goal () in
    let (hd, tl) = T.collect_app g in
    if not (hd `T.term_eq` (`gen_unit_elim_t))
    then T.fail "solve_gen_unit_elim: not a gen_unit_elim_t goal";
    match tl with
    | [tl', T.Q_Explicit] ->
      if not (term_has_head tl' (`pure))
      then T.apply (`gen_unit_elim_id)
      else
        let (hd, _) = T.collect_app tl' in
        if hd `T.term_eq` (`pure)
        then T.apply (`gen_unit_elim_pure)
        else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
        then begin
          T.apply (`gen_unit_elim_star);
          T.iseq [
            solve_gen_unit_elim;
            solve_gen_unit_elim;
          ];
          T.qed ()
        end
        else
          T.apply (`gen_unit_elim_id)
    | _ -> T.fail "ill-formed gen_unit_elim_t"
  )

let abstr_has_exists
  (t: T.term)
: T.Tac bool
= match T.inspect t with
  | T.Tv_Abs _ body -> term_has_head body (`exists_)
  | _ -> false

let rec solve_gen_elim
  ()
: T.Tac unit
= 
  T.focus (fun _ ->
    T.norm [];    
    let g = T.cur_goal () in
    let (hd, tl) = T.collect_app g in
    if not (hd `T.term_eq` (`gen_elim_t))
    then T.fail "solve_gen_elim: not a gen_elim_t goal";
    match tl with
    | [tl', T.Q_Explicit] ->
      if not (term_has_head tl' (`exists_))
      then begin
        T.apply (`gen_elim_of_gen_unit_elim);
        solve_gen_unit_elim ()
      end else
        let (hd, body) = T.collect_app tl' in
        if hd `T.term_eq` (`exists_)
        then
          match body with
          | [(_, T.Q_Implicit); (body, T.Q_Explicit)]
          | [(body, T.Q_Explicit)] ->
            if not (abstr_has_exists body)
            then begin
              T.apply (`gen_elim_exists_unit_body);
              let _ = T.intro () in
              solve_gen_unit_elim ()
            end else begin
              T.apply (`gen_elim_exists);
              let _ = T.intro () in
              solve_gen_elim ()
            end
          | _ -> T.fail "ill-formed exists_"
        else if hd `T.term_eq` (`star) || hd `T.term_eq` (`VStar)
        then
          match body with
          | [(tl, T.Q_Explicit); (tr, T.Q_Explicit)] ->
            if term_has_head tl (`exists_)
            then
              if term_has_head tr (`exists_)
              then begin
                T.apply (`gen_elim_star);
                T.iseq [
                  solve_gen_elim;
                  solve_gen_elim;
                ];
                T.qed ()
              end else begin
                T.apply (`gen_elim_star_l);
                T.iseq [
                  solve_gen_elim;
                  solve_gen_unit_elim;
                ];
                T.qed ()
              end
            else begin (* here, term_has_head tr (`exists_) holds, because otherwise we are in case (not (term_has_head tl (`exists_))) above *)
              T.apply (`gen_elim_star_r);
              T.iseq [
                solve_gen_unit_elim;
                solve_gen_elim;
              ];
              T.qed ()
            end
          | _ -> T.fail "ill-formed star"
        else
          T.apply (`gen_elim_id)
    | _ -> T.fail "ill-formed gen_elim_t"
  )

val gen_elim_prop
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop

let gen_elim_dummy
  (#p: vprop)
  (i: gen_elim_t p)
: Tot prop
= True

let gen_elim_dummy_intro
  (#p: vprop)
  (i: gen_elim_t p)
: Lemma (gen_elim_dummy i)
= ()

val gen_elim_prop_intro
  (p: vprop)
  (i: gen_elim_t p)
  (dummy: squash (gen_elim_dummy i))
  (a: Type0)
  (sq_a: squash (a == GenElim?.a i))
  (post: Ghost.erased a -> Tot prop)
  (sq_post: squash (post == (fun (x: Ghost.erased a) -> GenElim?.post i x)))
  (q: Ghost.erased a -> Tot vprop)
  (sq_q: squash (q == (fun (x: Ghost.erased a) -> GenElim?.q i x)))
: Lemma (gen_elim_prop p a q post)

val gen_elim_prop_elim
  (#opened: _)
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
  (sq: squash (gen_elim_prop p a q post))
  (_: unit)
: STGhostF (Ghost.erased a) opened p q True post

let gen_elim_prop_placeholder
  (p: vprop)
  (a: Type0)
  (q: Ghost.erased a -> Tot vprop)
  (post: Ghost.erased a -> Tot prop)
: Tot prop
= True

let gen_elim_prop_placeholder_intro
  (p: vprop)
  (i: gen_elim_t p)
  (dummy: squash (gen_elim_dummy i))
  (a: Type0)
  (sq_a: squash (a == GenElim?.a i))
  (post: Ghost.erased a -> Tot prop)
  (sq_post: squash (post == (fun (x: Ghost.erased a) -> GenElim?.post i x)))
  (q: Ghost.erased a -> Tot vprop)
  (sq_q: squash (q == (fun (x: Ghost.erased a) -> GenElim?.q i x)))
: Lemma (gen_elim_prop_placeholder p a q post)
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
        | [(i, _)] ->
          if not (T.Tv_Uvar? (T.inspect i))
          then T.fail "gen_elim_dummy is already solved";
          T.unshelve i;
          T.focus solve_gen_elim;
          T.apply_lemma (`gen_elim_dummy_intro)
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
    T.focus solve_gen_elim_dummy;
    let norm () = T.norm [delta_attr [(`%__reduce__)]; delta_only [(`%GenElim?.a); (`%GenElim?.q); (`%GenElim?.post)]; iota] in
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ());
    T.focus (fun _ -> norm (); T.trefl ())
  | _ -> T.fail "ill-formed squash"

val gen_elim
  (#opened: _)
  (#[@@@ framing_implicit] p: vprop)
  (#[@@@ framing_implicit] a: Type0)
  (#[@@@ framing_implicit] q: Ghost.erased a -> Tot vprop)
  (#[@@@ framing_implicit] post: Ghost.erased a -> Tot prop)
  (#[@@@ framing_implicit] sq: squash (gen_elim_prop_placeholder p a q post))
  (_: unit)
: STGhostF (Ghost.erased a) opened p (fun x -> guard_vprop (q x)) ( T.with_tactic solve_gen_elim_prop (squash (gen_elim_prop p a q post))) post

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
    let norm () = T.norm [delta_attr [(`%__reduce__)]; delta_only [(`%GenElim?.a); (`%GenElim?.q); (`%GenElim?.post)]; iota] in
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
