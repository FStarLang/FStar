(*
   Copyright 2008-2018 Microsoft Research

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
module Tutorial

/// This file presents a walkthrough of the tactics engine in its current
/// (July 23rd, 2017) state. It is mostly aimed at users and power users, leaving
/// some details about the implementation out of this.

open FStar.Tactics
open FStar.List

/// **First, what are tactics supposed to be?**
///
/// In other dependently-typed theorem provers, they are a way to construct
/// (or find) proofs automatically, which can be very tedious. Take a
/// goal such as ``a + (b + c) == (c + a) + b``: we can get a proofterm for
/// it by applying and composing associativity and commutativity lemmas.
/// However, this proofterm is very dependent on the exact goal we're
/// trying to prove: any change to the goal will require a change to the
/// proof. This is annoying, since no real insight is required for the
/// proof. Tactics provide an extensible way to automate these kind of
/// proofs, improving robustness of proofs and the user's sanity. In one
/// way or another, tactics reflect on the goal they have been called on,
/// possibly inspecting the local and global environments, and implement
/// a custom behaviour to construct such proof. In the previous example,
/// one possibility for a tactic is shuffling the summands on each side
/// following some well-defined order, a totally automatable process.
///
/// You might be thinking: "doesn't F* already have an SMT solver backend
/// for this reason?". Yes, but this does not at all negate the need for
/// more automation in proofs. One could want to not call the SMT and stay
/// only within F*, or to break down a proof obligation into more manageable
/// chunks for the SMT, or even to simply change some SMT options or its
/// environment for different subgoals. The main goal is to get more robust
/// and faster proofs.
///
/// On the other side of the Curry-Howard isomorphism, tactics can also
/// be used to construct arbitrary terms, and not necessarilly proofs.
/// In this sense, they enable "metaprogramming" such as automatically
/// generating printers for datatypes, recursors, or for whatever crazy
/// boilerplate-like thing you want to do. We can also benefit from that in
/// F*.
///
/// So, enough talk, **what's the hello world of tactics?**
/// The entry point for *proving* in tactics is the `assert _ by _` form,
/// which takes a tactic to be run on the goal to prove.

val ex1 : unit -> Lemma True
let ex1 () =
    assert True
    by idtac()

/// Here, ``idtac`` is the identity tactic, which does nothing. Certainly,
/// ``True`` is a simple enough goal so this example succeeds. In between, the
/// tactic is running with `True` as a goal, in the “logical environment”
/// where we need to do the proof. Running the following example will cause
/// the exact “proofstate” where the tactic runs to be printed in the
/// standard output.

val ex2 : unit -> Lemma True
let ex2 () =
    assert True
    by dump "Example 2"

/// This yields the following::
///
///    Goal 1/1
///      uu___: unit
///      p: pure_post unit
///      ----------------------
///      squash l_True
///      (*?u18*) _ uu___6626 p

/// The output shows that we have only one “active” goal (that we're still working
/// on) and no goals that have been already dispatched to the SMT.
///
/// Concretely, to prove `True`, the engine is asking us to provide a term
/// of type `squash True`. Squashing is the way we do proof-irrelevance in F*,
/// and you can simply think of the type `squash phi` as the type of irrelevant
/// proofs of `phi`. We call goals that are squashed “irrelevant”.

/// .. note::
///
///    For experts: You might notice that ``True`` is already a squash (of
///    ``c_True``), so this seems useless. In this case it is, but we squash
///    nevertheless for consistency since this might be not so.

/// A tactic is not required to completely prove an assertion, and can leave
/// any number of goals unsolved, which will be fed to the SMT. Importantly,
/// this can only be done on irrelevant goals, as the SMT does not produce
/// proof terms!

/// As expected, we can also manipulate logical formulas. There is a derived set of
/// tactics (FStar.Tactics.Logical) simplifying this task, which is somewhat
/// complicated due to squashing. Let's write a tactic to split a conjunction
/// and solve one of its subformulas.

let tau3 () : Tac unit =
  Tactics.split ();
  smt ();
  norm [delta; zeta; primops];
  trivial ()

let ex3 (x : nat) =
  assert (x + x >= 0 /\ List.length [4;5;1] == 3)
      by tau3()

/// First, we defined tau3 as a custom tactic, composed by applying ``split``,
/// ``smt`` and ``trivial`` in that order. The ``tactic 'a`` type is a monad, and
/// this is F*'s version of do notation for it.
///
/// The ``split`` tactic will destruct the original goal into its
/// two conjuncts, creating two new goals.
///
/// Try adding ``dump "After split";`` just after ``split`` above, and run that code again.  Now we see the following::
///
///     After split
///       Goal 1/2
///         x: nat
///         -------------------
///         squash (x + x >= 0)
///         (*?u58*) _ x
///       Goal 2/2
///         x: nat
///         ------------------------------
///         squash (length [4; 5; 1] == 3)
///         (*?u59*) _ x
///
/// Further tactic steps are applied to the first goal. For the first one,
/// we want to just give it to the smt, so we call into the ``smt`` tactic,
/// which always succeeds and marks a goal for SMT discharging. If we were
/// to dump the proofstate here, we'd see the first goal was simply moved
/// into the "SMT goals" set.
///
/// The second conjunct one can be shown true simply by normalization, so we
/// can call into the ``trivial`` tactic to take care of it internally.
///
/// .. note::
///
///    There is currently no support for a "try SMT" tactic, which would
///    return back control if the SMT solver cannot prove the goal. This
///    requires some rework in how guards are discharged in F*.
///
/// For an automation example, let's write a tactic that will split all
/// top-level conjunctions in our goal, trying to discharge them if
/// they're trivial. Importantly, we need to be able to inspect the goal
/// we're trying to prove from *within* the tactic. This is done via the
/// ``cur_goal`` primitive, which returns the goal as ``term``, a reflection of
/// F*'s internal term representation. These ``term``\ s are actually opaque,
/// and can only be meaningfully used through some *views* defined on them.
/// Since we're dealing with a logical formula, the ``formula`` view is the
/// most comfortable one. We can decide if our goal is a conjunction in the
/// following way:

let is_conj () : Tac bool =
  let g = cur_goal () in
  match term_as_formula g with
  | And _ _ -> true
  | _       -> false

/// Now, we want a tactic that will call ``split`` when our goal is a
/// conjunction, and then recurse on the conjuncts! The iseq tactic
/// proves handy here. Given a list of tactics, ``iseq`` will apply them in
/// succession to each of the open goals.

let rec split_all () : Tac unit =
  if is_conj ()
  then
    begin
    Tactics.split ();
    iseq [split_all; split_all]
    end
  else
    let _ = trytac trivial in
    ()

/// We can use it for our previous example, or to break down bigger formulas.

let ex3' (x : nat) =
  assert (x + x >= 0 /\ List.length [4;5;1] == 3)
      by split_all()

let ex4 (x : nat) =
  assert
    ((1 + 1 == 2) /\
     ((-x <= 0 /\ x + x >= 0) /\
      List.length [4;5;1] == 3))
     by split_all()

/// Here, all of the conjuncts that remain are sent off separetely to the SMT solver.
