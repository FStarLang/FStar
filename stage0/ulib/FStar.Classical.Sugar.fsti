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
       (#p:a -> Type)
       (v:a)
       (f:squash (forall (x:a). p x))
  : Tot (squash (p v))

(** Eliminate an existential quantifier into a proof of a goal [q] *)
val exists_elim
     (#t:Type)
     (#p:t -> Type)
     (#q:Type)
     ($s_ex_p: squash (exists (x:t). p x))
     (f: (x:t -> squash (p x) -> Tot (squash q)))
  : Tot (squash q)

(** Eliminate an implication, by providing a proof of the hypothesis
    Note, the proof is thunked *)
let implies_elim
        (p:Type)
        (q:Type)
        (_:squash (p ==> q))
        (f:unit -> Tot (squash p))
  : squash q
  = f()

(** Eliminate a disjunction
    - The type of q can depend on the ~p
    - The right proof can assume both ~p and q
*)
val or_elim
        (p:Type)
        (q:squash (~p) -> Type)
        (r:Type)
        (p_or:squash (p \/ q()))
        (left:squash p -> Tot (squash r))
        (right:squash (~p) -> squash (q()) -> Tot (squash r))
  : Tot (squash r)

(** Eliminate a conjunction
    - The type of q can depend on p
*)
val and_elim
        (p:Type)
        (q:squash p -> Type)
        (r:Type)
        (_:squash (p /\ q()))
        (f:squash p -> squash (q()) -> Tot (squash r))
  : Tot (squash r)

(** Introduce a universal quantifier *)
val forall_intro
      (a:Type)
      (p:a -> Type)
      (f: (x:a -> Tot (squash (p x))))
  : Tot (squash (forall x. p x))

(** Introduce an existential quantifier *)
val exists_intro
        (a:Type)
        (p:a -> Type)
        (v:a)
        (x: unit -> Tot (squash (p v)))
  : Tot (squash (exists x. p x))

(** Introduce an implication
    - The type of q can depend on p
  *)
val implies_intro
        (p:Type)
        (q:squash p -> Type)
        (f:(squash p -> Tot (squash (q()))))
  : Tot (squash (p ==> q()))

(** Introduce an disjunction on the left
    - The type of q can depend on ~p
    - The proof is thunked to avoid polluting the continuation
  *)
val or_intro_left
        (p:Type)
        (q:squash (~p) -> Type)
        (f:unit -> Tot (squash p))
  : Tot (squash (p \/ q()))

(** Introduce an disjunction on the right
    - The type of q can depend on ~p
    - The proof can assume ~p too
  *)
val or_intro_right
        (p:Type)
        (q:squash (~p) -> Type)
        (f:squash (~p) -> Tot (squash (q())))
  : Tot (squash (p \/ q()))

(** Introduce a conjunction
    - The type of q can depend on p
    - The proof in the right case can also assume p
  *)
val and_intro
        (p:Type)
        (q:squash p -> Type)
        (left:unit -> Tot (squash p))
        (right:squash p -> Tot (squash (q())))
  : Tot (squash (p /\ q()))
