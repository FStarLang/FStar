(*
   Copyright 2021 Microsoft Research

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

module FStar.Classical.Sugar

/// This module provides a few combinators that are targeted
/// by the desugaring phase of the F* front end
///
/// The combinators it provides are fairly standard, except for one
/// subtlety. In F*, the typechecking of terms formed using the
/// logical connectives is biased from left to right. That is:
///
/// * In [p /\ q] and [p ==> q], the well-typedness of [q] is in a
///   context assuming [squash p]
///
/// * In [p \/ q], the well-typedness of [q] is in a context assuming
///   [squash (~p)]
///
/// So, many of these combinators reflect that bias by taking as
/// instantiations for [q] functions that depend on [squash p] or
/// [squash (~p)].
///
/// The other subtlety is that the when using these combinators, we
/// encapsulate any proof terms provided by the caller within a
/// thunk. This is to ensure that if, for instance, the caller simply
/// admits a goal, that they do not inadvertently discard any proof
/// obligations in the remainder of their programs.
///
/// For example, consider the difference between
///
///  1. exists_intro a p v (admit()); rest
///
/// and
///
///  2. exists_intro a p v (fun _ -> admit()); rest
///
/// In (1) the proof of rest is admitted also.


(** Eliminate a universal quantifier by providing an instantiation *)
val forall_elim
       (#a:Type)
       (#p:a -> prop)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))

(** Eliminate an existential quantifier into a proof of a goal [q] *)
val exists_elim
     (#t:Type)
     (#p:t -> prop)
     (#q:prop)
     (s_ex_p: squash (exists (x:t). p x))
     (f: (x:t -> squash (p x) -> Tot (squash q)))
  : Tot (squash q)

(** Eliminate an implication, by providing a proof of the hypothesis
    Note, the proof is thunked *)
let implies_elim
        (p:prop)
        (q:prop)
        (_:squash (p ==> q))
        (f:unit -> Tot (squash p))
  : squash q
  = f()

(** Eliminate a disjunction
    - The type of q can depend on the ~p
    - The right proof can assume both ~p and q
*)
val or_elim
        (p:prop)
        (q:squash (~p) -> prop)
        (r:prop)
        (p_or:squash (p \/ q()))
        (left:squash p -> Tot (squash r))
        (right:squash (~p) -> squash (q()) -> Tot (squash r))
  : Tot (squash r)

(** Eliminate a conjunction
    - The type of q can depend on p
*)
val and_elim
        (p:prop)
        (q:squash p -> prop)
        (r:prop)
        (_:squash (p /\ q()))
        (f:squash p -> squash (q()) -> Tot (squash r))
  : Tot (squash r)

(** Introduce a universal quantifier *)
val forall_intro
      (a:Type)
      (p:a -> prop)
      (f: (x:a -> Tot (squash (p x))))
  : Tot (squash (forall x. p x))

(** Introduce an existential quantifier *)
val exists_intro
        (a:Type)
        (p:a -> prop)
        (v:a)
        (x: unit -> Tot (squash (p v)))
  : Tot (squash (exists x. p x))

(** Introduce an implication
    - The type of q can depend on p
  *)
val implies_intro
        (p:prop)
        (q:squash p -> prop)
        (f:(squash p -> Tot (squash (q()))))
  : Tot (squash (p ==> q()))

(** Introduce an disjunction on the left
    - The type of q can depend on ~p
    - The proof is thunked to avoid polluting the continuation
  *)
val or_intro_left
        (p:prop)
        (q:squash (~p) -> prop)
        (f:unit -> Tot (squash p))
  : Tot (squash (p \/ q()))

(** Introduce an disjunction on the right
    - The type of q can depend on ~p
    - The proof can assume ~p too
  *)
val or_intro_right
        (p:prop)
        (q:squash (~p) -> prop)
        (f:squash (~p) -> Tot (squash (q())))
  : Tot (squash (p \/ q()))

(** Introduce a conjunction
    - The type of q can depend on p
    - The proof in the right case can also assume p
  *)
val and_intro
        (p:prop)
        (q:squash p -> prop)
        (left:unit -> Tot (squash p))
        (right:squash p -> Tot (squash (q())))
  : Tot (squash (p /\ q()))

////////////////////////////////////////////////////////////////////////////////
// Combinators used by the desugaring of `eliminate`
////////////////////////////////////////////////////////////////////////////////

(** Decide which side of a disjunction holds.
    Used to desugar `eliminate p \/ q with e1 and e2` into
    `if or_decide p q then e1 else e2`.

    These combinators are marked `irreducible` so that a `let` binding
    of one of them does not add a defining equation to the VC; see
    `should_return` in FStarC.TypeChecker.Util. *)
irreducible
let or_decide (p q:prop)
  : Ghost bool
    (requires p \/ q)
    (ensures fun b -> if b then p else q)
  = let b = t2b p in
    assert (b <==> p);
    b

(** Pick a witness for an existential.

    `indefinite_descriptionN` picks witnesses for `N` nested existentials in a
    single step, packaged in a right-nested chain of dependent pairs, so that
    `eliminate exists x1 ... xN. p with e` desugars into

      `let (| x1, (| ..., xN |) |) = indefinite_descriptionN (fun x1 ... xN -> p) in e`

    Doing all `N` binders at once matters for performance. If the desugaring
    instead chained several smaller combinators, each intermediate step would
    restate the remaining existential as its own postcondition, and the cost of
    normalizing the resulting verification condition grows exponentially in the
    number of steps. Nesting also gives the outer existentials no usable SMT
    trigger, so Z3 falls back to enumerating tuples of typed terms (see issues
    #4405 and #4444).

    The chain is built from `dtuple2` alone rather than from wider tuple types,
    so no new tuple types are needed to support large arities.

    Only arities up to `max_indefinite_description_arity` are provided; beyond
    that the desugaring peels off one binder at a time. The cap is kept modest
    because checking `indefinite_descriptionN` itself currently costs time
    exponential in `N`; that is a normalizer problem, not a Z3 one (every query
    in this file is discharged well under an rlimit of 1). *)

irreducible
let indefinite_description1
      (#a1:Type)
      (p: a1 -> prop)
  : Ghost a1
    (requires exists x1. p x1)
    (ensures fun x1 -> p x1)
  = indefinite_description p

irreducible
let indefinite_description2
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> prop))
  : Ghost (x1:a1 & a2 x1)
    (requires exists x1 x2. p x1 x2)
    (ensures fun r -> let (| x1, x2 |) = r in p x1 x2)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2. p x1 x2) in
    let rest = indefinite_description1 #(a2 x1) (fun x2 -> p x1 x2) in
    (| x1, rest |)

irreducible
let indefinite_description3
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & a3 x1 x2))
    (requires exists x1 x2 x3. p x1 x2 x3)
    (ensures fun r -> let (| x1, (| x2, x3 |) |) = r in p x1 x2 x3)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3. p x1 x2 x3) in
    let rest = indefinite_description2 #(a2 x1) #(a3 x1) (fun x2 x3 -> p x1 x2 x3) in
    (| x1, rest |)

irreducible
let indefinite_description4
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (#a4:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & (x3:a3 x1 x2 & a4 x1 x2 x3)))
    (requires exists x1 x2 x3 x4. p x1 x2 x3 x4)
    (ensures fun r -> let (| x1, (| x2, (| x3, x4 |) |) |) = r in p x1 x2 x3 x4)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3 x4. p x1 x2 x3 x4) in
    let rest = indefinite_description3 #(a2 x1) #(a3 x1) #(a4 x1) (fun x2 x3 x4 -> p x1 x2 x3 x4) in
    (| x1, rest |)

irreducible
let indefinite_description5
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (#a4:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> GTot Type))
      (#a5:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & (x3:a3 x1 x2 & (x4:a4 x1 x2 x3 & a5 x1 x2 x3 x4))))
    (requires exists x1 x2 x3 x4 x5. p x1 x2 x3 x4 x5)
    (ensures fun r -> let (| x1, (| x2, (| x3, (| x4, x5 |) |) |) |) = r in p x1 x2 x3 x4 x5)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3 x4 x5. p x1 x2 x3 x4 x5) in
    let rest = indefinite_description4 #(a2 x1) #(a3 x1) #(a4 x1) #(a5 x1) (fun x2 x3 x4 x5 -> p x1 x2 x3 x4 x5) in
    (| x1, rest |)

irreducible
let indefinite_description6
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (#a4:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> GTot Type))
      (#a5:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> GTot Type))
      (#a6:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & (x3:a3 x1 x2 & (x4:a4 x1 x2 x3 & (x5:a5 x1 x2 x3 x4 & a6 x1 x2 x3 x4 x5)))))
    (requires exists x1 x2 x3 x4 x5 x6. p x1 x2 x3 x4 x5 x6)
    (ensures fun r -> let (| x1, (| x2, (| x3, (| x4, (| x5, x6 |) |) |) |) |) = r in p x1 x2 x3 x4 x5 x6)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3 x4 x5 x6. p x1 x2 x3 x4 x5 x6) in
    let rest = indefinite_description5 #(a2 x1) #(a3 x1) #(a4 x1) #(a5 x1) #(a6 x1) (fun x2 x3 x4 x5 x6 -> p x1 x2 x3 x4 x5 x6) in
    (| x1, rest |)

irreducible
let indefinite_description7
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (#a4:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> GTot Type))
      (#a5:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> GTot Type))
      (#a6:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> GTot Type))
      (#a7:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> x7:a7 x1 x2 x3 x4 x5 x6 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & (x3:a3 x1 x2 & (x4:a4 x1 x2 x3 & (x5:a5 x1 x2 x3 x4 & (x6:a6 x1 x2 x3 x4 x5 & a7 x1 x2 x3 x4 x5 x6))))))
    (requires exists x1 x2 x3 x4 x5 x6 x7. p x1 x2 x3 x4 x5 x6 x7)
    (ensures fun r -> let (| x1, (| x2, (| x3, (| x4, (| x5, (| x6, x7 |) |) |) |) |) |) = r in p x1 x2 x3 x4 x5 x6 x7)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3 x4 x5 x6 x7. p x1 x2 x3 x4 x5 x6 x7) in
    let rest = indefinite_description6 #(a2 x1) #(a3 x1) #(a4 x1) #(a5 x1) #(a6 x1) #(a7 x1) (fun x2 x3 x4 x5 x6 x7 -> p x1 x2 x3 x4 x5 x6 x7) in
    (| x1, rest |)

irreducible
let indefinite_description8
      (#a1:Type)
      (#a2:(x1:a1 -> GTot Type))
      (#a3:(x1:a1 -> x2:a2 x1 -> GTot Type))
      (#a4:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> GTot Type))
      (#a5:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> GTot Type))
      (#a6:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> GTot Type))
      (#a7:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> GTot Type))
      (#a8:(x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> x7:a7 x1 x2 x3 x4 x5 x6 -> GTot Type))
      (p: (x1:a1 -> x2:a2 x1 -> x3:a3 x1 x2 -> x4:a4 x1 x2 x3 -> x5:a5 x1 x2 x3 x4 -> x6:a6 x1 x2 x3 x4 x5 -> x7:a7 x1 x2 x3 x4 x5 x6 -> x8:a8 x1 x2 x3 x4 x5 x6 x7 -> prop))
  : Ghost (x1:a1 & (x2:a2 x1 & (x3:a3 x1 x2 & (x4:a4 x1 x2 x3 & (x5:a5 x1 x2 x3 x4 & (x6:a6 x1 x2 x3 x4 x5 & (x7:a7 x1 x2 x3 x4 x5 x6 & a8 x1 x2 x3 x4 x5 x6 x7)))))))
    (requires exists x1 x2 x3 x4 x5 x6 x7 x8. p x1 x2 x3 x4 x5 x6 x7 x8)
    (ensures fun r -> let (| x1, (| x2, (| x3, (| x4, (| x5, (| x6, (| x7, x8 |) |) |) |) |) |) |) = r in p x1 x2 x3 x4 x5 x6 x7 x8)
  = let x1 = indefinite_description (fun (x1:a1) -> exists x2 x3 x4 x5 x6 x7 x8. p x1 x2 x3 x4 x5 x6 x7 x8) in
    let rest = indefinite_description7 #(a2 x1) #(a3 x1) #(a4 x1) #(a5 x1) #(a6 x1) #(a7 x1) #(a8 x1) (fun x2 x3 x4 x5 x6 x7 x8 -> p x1 x2 x3 x4 x5 x6 x7 x8) in
    (| x1, rest |)
