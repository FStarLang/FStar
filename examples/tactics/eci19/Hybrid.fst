module Hybrid

open FStar.Tactics
open FStar.Mul

(*
Meta-F* supports a "hybrid" style of proof, where we can just
simplify/tweak goals before sending them to the SMT solver instead of
completely solving them via tactics. This is useful, since sometimes
writing an automated proof procedure can be a lot of work. Hence,
reusing the SMT solver's logic saves us some work.

Previously, providing "hints" to the SMT solver involved modifying the
program/proof by introducing lemma calls, as so:
*)

let modulo_add (p:pos) (a b c : int)
  : Lemma (requires (b % p == c % p)) (ensures ((a + b) % p == (a + c) % p))
  = FStar.Math.Lemmas.modulo_distributivity a b p; (* a hint *)
    FStar.Math.Lemmas.modulo_distributivity a c p; (* a hint *)
    assert ((a + b) % p == (a + c) % p)

(* Now, instead of doing that, we can tackle the assertion via a tactic. In
this case we simply "pose" the lemmas to get their hypotheses in the context,
so not much work is saved, but we're not making use of automation (yet!). *)
            
let modulo_add_tactic (p:pos) (a b c : int)
  : Lemma (requires (b % p == c % p)) (ensures ((a + b) % p == (a + c) % p))
  = assert ((a + b) % p == (a + c) % p)
        by (ignore (pose_lemma (quote (FStar.Math.Lemmas.modulo_distributivity a b p)));
            ignore (pose_lemma (quote (FStar.Math.Lemmas.modulo_distributivity a c p))))

(*

Exercise: print and look at the proofstates before and after the
`pose_lemma` calls. There are some SMT goals introduced by the calls,
what do they represent?

Notice that, for this assertion, F* generates a proofstate with the
assertion as a goal, and with a context including all variables in scope
*plus* the logical facts (such as the requires clause).
*)

(*
The inner workings:

As we have seen, assertions essentially introduce a cut
in the verification condition that F* computes: the assertion needs to
be proven at that program point, and is assumed in the continuation.

What's happening here is that F* is computing a verification condition
with the assertion, which basically introduces a "cut". When the assertion
has a tactic `t`, the proposition is actually wrapped with a marker `with_tactic`.

  val with_tactic : (unit -> Tac unit) -> Type -> Type

Semantically, this marker just returns its second argument, ignoring
the tactic. However, when F* finds it before discharging a VC, it gets
special treatment. If a part of a VC is wrapped with this marker, it is
split out of the VC and turned into a proofstate. This is done only when
it appears in a "positive" position (i.e. a proof obligation) and not
for "negative" ones (i.e. hypotheses).

So, for instance, if we have `assert phy by tau ()` in a term, our VC
will look something like:

   .... ==> with_tactic tau phi /\ (with_tactic tau phi ==> ....

Here F* will turn this into

   .... ==> True /\ (phi ==> ....

trivializing the assertion within the VC, and creating a goal for
`squash phi` in a proper context (including all hypotheses in the left
"....").

The modified VC, called the "skeleton", is discharged as usual by the
SMT solver. The created proofstate will be fed to the `tau` tactic,
which can either solve it or finish with some open goals, which will be
fed to SMT.

*)

(*
Posing lemmas is a sort of "forward style" of proof: we conclude new
facts from previous facts in order to prove our goal. We can also do
proofs in backwards style, where we reduce our goal to simpler, usually
smaller, goals (note: implies_intro, split, left, and etc, are all
backwards-style).

To use a lemma in backwards style, there is `apply_lemma`. This
primitive unifies a Lemma's postcondition with the current goal and,
if that succeeds, creates goals for the missing arguments of the lemma
and (possibly) for the precondition of it.

Let's use them to prove a simple lemma (triang2), after some auxiliary
definitions.
*)

let rec triang (n : nat) : Tot nat =
  if n = 0 then 0 else n + triang (n - 1)

(* Z3 is actually not so great at doing this proof when the context
includes many facts, so we delete everything but the most primitive
module and the current one. Plus, we add a --retry flag so it attempts
again (up to 10 times) if the proof fails. *)
#push-options "--using_facts_from '-* +Prims +Hybrid' --retry 10"
let rec gauss (n : int) : Lemma (requires (n >= 0))
                              (ensures (triang n == (n * (n + 1)) / 2))
                        =
  if n <> 0 then gauss (n - 1)
#pop-options

let prod_even (n : int) : Lemma ((n * (n + 1)) % 2 == 0) =
  (* z3 needs some help *)
  FStar.Math.Lemmas.lemma_mod_mul_distr_l n (n+1) 2

let triang2 (a : nat) : Lemma (triang a + triang a == a * (a + 1)) =
  assert ((a * (a + 1)) % 2 == 0)
      by (apply_lemma (`prod_even); qed ());
  assert (triang a == (a * (a + 1) / 2))
      by (apply_lemma (`gauss); smt (); qed ());
  ()

(* Exercise: step through the proof and look at the proof state
evolution on both assertions, what goals does `apply_lemma` create in
each case? *)

(*
In the calls above, there was only one valid choice for the arguments
to `gauss` and `prod_even` (namely `a` in both cases), but this is not
always the case. When this happens, apply_lemma will create a new goal
for the missing term/proof. For terms, we can use `exact` to provide the
solution manually.
*)

let silly_lemma (a b : nat) : Lemma (requires (a > b))
                                  (ensures (a * a > 0)) = ()

let test_need_arg (a : nat{a > 2}) =
  assert (a * a > 0)
      by (apply_lemma (`silly_lemma);
          exact (`2))

(* Exercise: dump the intermediate proof states and identify what each
goal represents. *)

(* Exercise: make this work without SMT by using the canonicalizer from
FStar.Tactics.Canon, and print the resulting simplified goal. Equalities
between syntactically equal terms can be solved by the `trefl` tactic.
*)

open FStar.Tactics.Canon

(* let arith_test (a b c d e : int) = *)
(*     assert *)
(*         ((a+b+c+d + e%2)*(b+c+d+a) == *)
(*                 a * a + b * b *)
(*               + c * c + d * d *)
(*               + e%2 * a + e%2 * b *)
(*               + e%2 * c + e%2 * d *)
(*               + a * b + a * b *)
(*               + a * c + a * c *)
(*               + a * d + a * d *)
(*               + b * c + b * c *)
(*               + b * d + b * d *)
(*               + c * d + c * d) *)
