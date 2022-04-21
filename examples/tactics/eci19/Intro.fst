module Intro

(* This file is meant to skim through the features of Meta-F*, and not
really to teach you how to use it. That's what the next files are for! *)

(* We always need this module to use Meta-F* *)
open FStar.Tactics


(*

Meta-F* has many purposes. It can be used to discharge proof obligations
(replacing the SMT solver), to simply preprocess obligations
(complementing the SMT solver), for metaprogramming (i.e. the automatic
generation of terms/programs), solving implicit arguments (which can be
seen as a variant of metaprogramming), and more.

We (somewhat loosely) refer to the setting of using Meta-F* for
proofs as "tactics", and to the generation of terms/programs as
"metaprogramming".

(For experts: If you are familiar with other dependent languages such
as Coq/Agda/Lean, you might think these are the same thing. This is not
exactly so in F*, read ahead for details!)

At its core, Meta-F* is a language for describing correct (i.e. sound)
proof state transformations. A proof state is a set of "goals" that need
to be solved by providing a solution or proof for them. For instance,
a goal can be to prove `forall x. x + 1 == 1 + x`, or to construct a
term of type `int -> int -> Tot int`. The language allows to break down,
tweak, and solve these goals incrementally, while ensuring that the
solutions are correct (valid proofs / well-typed terms).

Meta-F* is in fact a subset of F* itself, and not a separate language
(as Coq and Ltac are). Making good use of F*'s effect system, Meta-F* is
embedded via an effect, named `Tac`, which enjoys all good properties of
F* effects (specifications by WPs, call-by-value, direct-style syntax,
type checking/inference, etc). So, let us present the most simple
metaprogram:

*)

let idtac () : Tac unit = ()

(*
We can also make use of all existing code in the PURE and DIV effects,
since they can be lifted into Tac.
*)

let max_list (l1 l2 : list int) : Tac (list int) =
    if FStar.List.length l1 > FStar.List.length l2 then l1 else l2

let rec recursive_tac (n:nat) : Tac unit =
    if n = 0
    then ()
    else recursive_tac (n - 1)

let rec looping_tac () : Tac unit =
    // Metaprograms need not terminate!
    looping_tac ()

(*

Of course, these programs are not so interesting as they do not have
any effect on the (implicit) proof state that they will manipulate.
Interesting metaprograms can (and must!) be built from *primitives*
(found in FStar.Tactic.Builtins) which can inspect and transform the
proof state. For instance, the `dump` primitive will, when run, output
the proof state in a pretty-printed format to the user, along with a
user-defined string.

*)

(* Exercise: try `C-c` `C-s` `C-d` and query the type of `dump` *)

(*
We can use `run_tactic` to test it. The `run_tactic` "hook" takes a term
of type `unit -> Tac unit` and runs it on a trivial empty proof state.
*)

let _ = run_tactic (fun () -> dump "Hello world!")

(*
You should see a "Hello world!" in the *fstar: goals* buffer of Emacs.
*)

(*
Exercise: Try writing and running a metaprogram that will call `dump` to
count down from 10 to 0. The `string_of_int` function from `Prims` might
be useful. You can navigate the dumps in the *fstar: goals* buffer with
PgUp and PgDown.
*)

// let rec countdown (n:nat) : Tac unit = ???
// 
// let _ = run_tactic (fun () -> countdown 10)

(*
Now that we have seen some trivial metaprograms, we can start writing
more interesting ones that actually manipulate the proof state. We will
begin by writing some tactics, i.e. metaprograms for proving, and using
them to solve assertions within code (as is common in F* ).

For instance, let us prove the following tautology with an explicit
proof:
*)

let constr (a b : prop) : Lemma (a ==> b ==> b /\ a) =
  assert (a ==> b ==> b /\ a)
      by (let ha = implies_intro () in
          let hb = implies_intro () in
          split ();
          hyp hb;
          hyp ha;
          qed ())

(* Exercise: inspect the intermediate proof states to understand the
proof. *)


(*
In the previous example, our proof was completed internally. However, F*
allows for a mixed style of proof where we can leverage the SMT solver
and use it when it works well, without having to fully spell out proofs
or write complex tactics.

For instance, consider the following fragment:
*)
open FStar.Mul

// computes 1 + 2 + .. + n
let rec triang (n : nat) : Tot nat =
  if n = 0 then 0 else n + triang (n - 1)

(* Z3 needs a bit of help to prove this reliably... *)
let triang_aux (n : pos) : Lemma (n + ((n-1) * n) / 2 == (n*(n+1)) / 2) =
  calc (==) {
    n + ((n-1) * n) / 2;
    == { FStar.Math.Lemmas.lemma_div_plus ((n-1)*n) 2 n }
    ((n-1) * n + n * 2) / 2;
    == { FStar.Math.Lemmas.swap_mul n (n-1);
         FStar.Math.Lemmas.distributivity_add_right n (n-1) 2 }
    (n * (n+1)) / 2;
  }

let rec gauss (n : nat) : Lemma (triang n == (n * (n + 1)) / 2) =
  if n <> 0 then (
    gauss (n-1);
    triang_aux n
  )

let prod_even (n : int) : Lemma ((n * (n + 1)) % 2 == 0) =
  (* z3 needs some help *)
  FStar.Math.Lemmas.lemma_mod_mul_distr_l n (n+1) 2

[@expect_failure] // this means the next definition is checked to *fail*!
let test (a : nat) : Lemma (triang a + triang a == a * (a + 1)) =
  //assert (triang a == (a * (a + 1) / 2));
  //assert ((a * (a + 1)) % 2 == 0);
  ()

(*
The test above fails since the SMT cannot find a proof for the         .
assertions We did not call the lemmas, and there are no patterns either.

Exercise: check that both assertions indeed fail by changing them to
`assume`s one at a time. Also make the proof work by using explicit
lemma calls.

Instead of doing either of those things, we can use tactics to guide the
proof in a more local fashion, using each lemma where needed.
*)

let test_good (a : nat) : Lemma (triang a + triang a == a * (a + 1)) =
  assert (triang a == (a * (a + 1) / 2))
      by (apply_lemma (`gauss); qed ());
  assert ((a * (a + 1)) % 2 == 0)
      by (apply_lemma (`prod_even); qed ());
  ()

(*
In this case, the postcondition is being proved by the SMT solver,
while each assertion is completely proven by the tactics.

A couple of things are going here. When using the `assert..by` syntax,
the assertion is turned into a proof state with a single goal, and
the associated tactic is run over it. The backtick marks a "static
quotation"; which we won't explain just yet.

Exercise: print and inspect the proof state before and after applying
the lemmas on each assertion.

These proof states single out the chosen assertion from the full VC of
the term, so one can write tactics for specific subobligations instead
of dealing with an (usually unpleasant) VC. In this case, we use the
`apply_lemma` primitive to solve each one.
*)

(*
Metaprograms can also inspect the goals they are invoked on, which
allows a single metaprogram to be useful in many different scenarios.
We call this ability "reflection", and it is mostly provided by the
FStar.Reflection module and the `inspect` tactic primitive. The
FStar.Reflection.Formula library provides a convenient way to use it for
the case of logical formulae.
*)

let _ =
  assert (True /\ True)
      by (let f = cur_formula () in
          match f with
          | And _ _ -> dump "It's a conjunction!"
          | _ -> fail "Uh-oh!")

let _ =
  assert (False ==> True)
      by (let f = cur_formula () in
          match f with
          | Implies _ _ -> dump "It's an implication!"
          | _ -> fail "Uh-oh!")

(*
By using these inspection capabilities, we can construct more
automated tactics. For instance, the following one that will split all
conjunctions and introduce all implications:
*)

let rec blowup () : Tac unit =
  match cur_formula () with
  | And _ _ -> split (); iseq [blowup; blowup]
  | Implies _ _ -> let _ = implies_intro () in blowup ()
  | _ -> ()

let test_blowup () =
  assert (True /\ (False ==> (True /\ False)))
      by (blowup (); dump "Final state")

(* Note how the final state has 3 separate goals *)

(*
Besides using Meta-F* for proving, we can use it do metaprogramming.
Using Meta-F* to construct terms follows the same principles as for
proving: there is a set of goals that need to be solved, and primitives
can be used to do so. The most simple way to solve a goal is to provide
a term via `exact`. The way to invoke Meta-F* for term generation is `_
by` syntax shown below:
*)

let int42 : int = _ by (exact (`42))

(* Exercise: print the definition of `int42` *)

(*
Besides providing exact solutions, terms can be built algorithmically by
calling the primitives. For instance, the `apply` primitive takes a term
`f` and solves the current goal with an application of `f` to as many
arguments as needed.
*)

let suc (x:int) = x + 1

let rec repeatN (n:nat) (t : unit -> Tac unit) : Tac unit =
  if n = 0
  then ()
  else (t (); repeatN (n-1) t)

let ten : int = _ by (repeatN 10 (fun () -> apply (`suc)); exact (`0))

(* Exercise: print the definition of `ten` (it's not 10!) *)

let rec sums (n:nat) : Tac unit =
  if n = 0
  then exact (`1)
  else begin
    apply (`(+));
    sums (n-1);
    sums (n-1)
  end

let big : int = _ by (sums 4)

(* Exercise: print the definition of `big` *)

(*
We can also use the reflection capabilities of F* to inspect the
goals we need to solve and act accordingly. For instance, here is a
metaprogram that constructs an addition function for any amount of
arguments.
*)

let rec __run (bs:binders) : Tac unit =
  match inspect (cur_goal ()) with
  | Tv_Arrow _ _ ->
    let b = intro () in
    __run (b::bs)
  | _ ->
    iter (fun b -> apply (`(+));
                exact (binder_to_term b)) bs;
    exact (`0)

let make_add () : Tac unit =
  __run []

let add_2 : a:int -> b:int -> Tot int = _ by (make_add ())
let add_3 : a:int -> b:int -> c:int -> Tot int = _ by (make_add ())
let add_4 : a:int -> b:int -> c:int -> d:int -> Tot int = _ by (make_add ())

let _ = assert (add_2 3 4 == 7)
let _ = assert (add_3 3 4 5 == 12)
let _ = assert (add_4 3 4 5 6 == 18)

(*
Another usage of metaprogramming is resolving implicit arguments.
Usually, in dependently typed languages, they are solved via
unification, which works fine when there is a single correct solution
implied by the well-typing of the term.
*)

let id (#a:Type) (x:a) = x

let call_id () = id 5

#push-options "--print_implicits"

(*
Run C-c C-s C-p call_id here, the implicit argument was resolved to
`int` since `5` has type `int`.
*)

#pop-options

(*
In other cases, there is perhaps no single correct solution via
unification, but there might however be some strategy to solve them.
Meta-F* provides a way to solve implicits via tactics, which allows
programmers to write their own strategies. As a simple example, let's
write a "diagonal" function whose second arguments is inferred to be the
same as the first one, unless explicitly provided.
*)

let diag (x : int) (#[exact (quote x)] y : int) : tuple2 int int = (x, y)

(* When the implicit is not given, this is simply a pair of an element
with itself. Note how in this case, there is no information that fully
defines the implicit from the types, and any integer is a correct
solution. *)
let _ = assert (diag 5 == (5, 5))

(* But one can override it *)
let _ = assert (diag 5 #23 == (5, 23))

(* As a more interesting example, this is exactly how typeclasses are
implemented in F*. See the type of add3 below , it contains an implicit
argument of type `add a`, which is to be resolved by the `tcresolve`
tactic. *)
open FStar.Tactics.Typeclasses

class add 'a = {
  sum : 'a -> 'a -> 'a
}

(* {|add a|} is just sugar for `(#[tcresolve ()] _ : add a)` *)
let add3 (#a:Type) {|add a|} (x y z : a) : a = sum x (sum y z)

(* Instances are just values with a `tcinstance` attribute, which is
what `tcresolve` looks for. *)
instance add_int : add int = { sum = (+) }

(* Same as
[@tcinstance] let add_int : add int = ...
*)

(* When called over a concrete type with an instance, such as `int`, the
`tcresolve` tactic solves the implicit to the instance. *)

let test_add = assert (add3 1 2 3 == 6)

#push-options "--print_implicits"

(* Exercise: print the definition of `test_add` here and look at the
solved implicits. *)

#pop-options

(* Having seen a bit of everything, we can now move into more advanced
topics on each area. *)

// Constructive.fst: doing proofs via tactics instead of SMT solver
// Automation.fst: inspecting goals and automating proofs
// Hybrid.fst: mixed style of proofs, using SMT + tactics
// Term.fst: The term representation and view
// Metaprogramming.fst: generating terms automatically and from type definitions
