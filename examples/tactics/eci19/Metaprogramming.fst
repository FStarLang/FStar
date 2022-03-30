module Metaprogramming

open FStar.Tactics

(*
Now, we shall turn to the automated generation of programs. Meta-F*
enables this in much the same way that it allows handling proofs: it
provides the user with a proofstate, a set of hypotheses and goals, and
one uses primitives to solve them. The way to call Meta-F* for metaprogramming
is the `_ by tau` syntax, as in the following:
*)

let my_int : int = _ by (exact (quote 42))

(*
In the fragment above, F* infers that the `_` must have type `int` (from
the annotation of `my_int`), and generates a proof state with a single
`int` goal. If you dump the initial proof state, you'll see something
like this:

    Goal 1/1
      --------------------------------------------------------------------------------
    int
    (*?u35*) _

Then, we solve this goal with the `exact` primitive

  val exact : term -> Tac unit

`exact` takes a term and attempts to solve the current goal with it. In
this case, it succeeds and the original `_` is solved to `42`. If you
print the definition of `my_int` there will be no mention of the tactic,
it will have been run already.

Exercise: try to solve the goal with a type-incorrect solution, for
example `true`.

Here there is a key difference the kind of goals that appeared before.
For proving, we start with an *irrelevant* (i.e. squashed) goal, where a
proof term is not strictly needed. Indeed, we can simply send irrelevant
goals to the SMT solver. On the other hand, in metaprogramming, the goal
is usually relevant and a fully-defined term, in this case an integer,
is needed.

Exercise: instead of using `exact`, try sending this goal to the SMT
solver, or not solving it somehow (it should fail!).

*)

(*
Instead of solving a goal outright with a solution, other primitives
allow to build terms incrementally. For instance, `apply f` solves the
goal to an application of `f` to some arguments (as many as needed), and
presents new goals for each argument. *)

let metasum : int = _ by (apply (quote (+));
                        // dump ""; // You should see two new goals here!
                        exact (`13);
                        exact (`29))
                  
(* Exercise: print the definition of metasum *)

(* We can also construct functions via the `intro` primitive. Calling
`intro` when the current goal is of type `a -> b` will solve it with
`fun x -> ?`, while presenting a new goal for the `?`, of at type `b`.
A `binder` for `x` is returned by intro, so it can be used to construct
the new solution. *)

let fancy_id : x:int -> int = _ by (let x = intro () in
                               exact (binder_to_term x))

(* Exercise: look at the proof states and final solution of `fancy_id` *)

(* Exercise: write a `zero` tactic that solves any goal of type `a -> b
-> ... -> z -> int` with the constant zero function. It should pass the
following tests. *)

//let const () : Tac unit = ???
//
//let f1 : int = _ by (const ())
//let f2 : nat -> int = _ by (const ())
//let f3 : bool -> list int -> unit -> int = _ by (const ())
//let f4 : int -> int -> int -> int -> int = _ by (const ())
//
//let _ = assert (f1 == 0)
//let _ = assert (forall x. f2 x == 0)
//let _ = assert (forall x y z. f3 x y z == 0)
//let _ = assert (forall x y z w . f4 x y z w == 0)

(* We can also perform case analysis on inductive types by the `destruct` primitive`.
Essentially, the `destruct` tactic takes a term `t` that has some inductive type
and performs a `match` on it. Then, it returns goals for each of the possible
cases. In each case, we also get an hypothesis for the fact that
the term we destructed is equal to the given branch. We ignore those
hypotheses here by just `intro`ducing them. *)

type enum = | A | B | C

let matchenum : enum -> int =
  _ by (let x = intro () in
        destruct (binder_to_term x);
        ignore (intro ()); exact (`1);
        ignore (intro ()); exact (`2);
        ignore (intro ()); exact (`3))

(* Exercise: look at the proof states and final solution for matchenum *)

(* Calling `destruct` also allows to get the arguments of each constructor. *)
type either (a b : Type) = | Left of a | Right of b

let matcheither : either int int -> int =
  _ by (let x = intro () in
        destruct (binder_to_term x);
        let x = intro() in ignore (intro ()); exact (binder_to_term x);
        let y = intro() in ignore (intro ()); exact (binder_to_term y))

let _ = assert (matcheither (Left 10) == 10)
let _ = assert (matcheither (Right 20) == 20)

(* For a fancier example of metaprogramming, you can check the
`examples/tactics/Printers.fst` file in the F* repo, which derives
printers for inductive types automatically. Though it is a bit beyond
the scope of this course. *)
