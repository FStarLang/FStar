module Pulse.Lib.Protocol.Temporal

(**
  A small, generic path-based temporal-logic reasoning layer.

  This module is deliberately independent of the calculator protocol: it is
  parameterised over an abstract state type `a` and a step relation
  `step : binrel a`. It provides

    - executions ("paths") over a transition system,
    - the core LTL operators `G` (globally), `F` (eventually), `X` (next) and
      `U` (until), given as predicates on paths,
    - the CTL path quantifier `ag` (`A G`, "on all runs, always"), together with
      `ef`/`af`,
    - a *soundness bridge* connecting `ag` to a reachable-state invariant:
      an inductive invariant that holds on every reachable state entails `ag`,
      and (for serial systems) the converse.

  The intended use is: prove that a property is an inductive invariant of the
  concrete system (cheap, via `FStar.ReflexiveTransitiveClosure.stable_on_closure`)
  and then *conclude* the genuine path-based `AG` property via `lemma_ag_of_invariant`.
**)

module R = FStar.ReflexiveTransitiveClosure

(** A step relation on states. **)
let binrel (a:Type) = a -> a -> prop

(** A state predicate. **)
let sprop (a:Type) = a -> prop

(** An execution: an infinite sequence of states. **)
let path (a:Type) = nat -> a

(** `p` is a run of `step`: consecutive states are related by `step`. **)
let is_run (#a:Type) (step:binrel a) (p:path a) : prop =
  forall (i:nat). step (p i) (p (i + 1))

(** The suffix of `p` starting at position `n`. **)
let shift (#a:Type) (p:path a) (n:nat) : path a =
  fun i -> p (i + n)

(** ─────────────────────────────────────────────────────────────────────────
    LTL operators as predicates on paths.
    ───────────────────────────────────────────────────────────────────────── **)

(** `G sp` — `sp` holds at every position. **)
let holds_G (#a:Type) (sp:sprop a) (p:path a) : prop =
  forall (i:nat). sp (p i)

(** `F sp` — `sp` holds at some position. **)
let holds_F (#a:Type) (sp:sprop a) (p:path a) : prop =
  exists (i:nat). sp (p i)

(** `X sp` — `sp` holds at the next position. **)
let holds_X (#a:Type) (sp:sprop a) (p:path a) : prop =
  sp (p 1)

(** `spa U spb` — `spb` eventually holds, and `spa` holds until then. **)
let holds_U (#a:Type) (spa:sprop a) (spb:sprop a) (p:path a) : prop =
  exists (j:nat). spb (p j) /\ (forall (k:nat). k < j ==> spa (p k))

(** ─────────────────────────────────────────────────────────────────────────
    Path quantifiers (CTL-flavoured), evaluated at a starting state.
    ───────────────────────────────────────────────────────────────────────── **)

(** `A G sp` at `s`: on every run starting at `s`, `sp` holds always. **)
let ag (#a:Type) (step:binrel a) (sp:sprop a) (s:a) : prop =
  forall (p:path a). (is_run step p /\ p 0 == s) ==> holds_G sp p

(** `E F sp` at `s`: some run starting at `s` eventually satisfies `sp`. **)
let ef (#a:Type) (step:binrel a) (sp:sprop a) (s:a) : prop =
  exists (p:path a). is_run step p /\ p 0 == s /\ holds_F sp p

(** `A F sp` at `s`: every run starting at `s` eventually satisfies `sp`. **)
let af (#a:Type) (step:binrel a) (sp:sprop a) (s:a) : prop =
  forall (p:path a). (is_run step p /\ p 0 == s) ==> holds_F sp p

(** ─────────────────────────────────────────────────────────────────────────
    Reachability and the soundness bridge.
    ───────────────────────────────────────────────────────────────────────── **)

(** `s'` is reachable from `s`: the reflexive-transitive closure of `step`. **)
let reachable (#a:Type) (step:binrel a) (s s':a) : prop =
  R.closure step s s'

(** Along any run, every visited state is reachable from the start. **)
let rec lemma_run_reaches (#a:Type) (step:binrel a) (p:path a) (i:nat)
  : Lemma (requires is_run step p)
          (ensures reachable step (p 0) (p i))
          (decreases i)
=
  if i = 0 then ()
  else begin
    lemma_run_reaches step p (i - 1);
    // step (p (i-1)) (p i) is in the closure, then compose with reachable (p 0) (p (i-1)).
    R.closure_step step (p (i - 1)) (p i)
  end

(**
  Soundness bridge (the direction we use): if `sp` holds on *every* state
  reachable from `s`, then the genuine path-based `A G sp` holds at `s`.

  This lets a cheap inductive-invariant proof discharge a real temporal `AG`.
**)
let lemma_ag_of_invariant
  (#a:Type)
  (step:binrel a)
  (sp:sprop a)
  (s:a)
  : Lemma
      (requires (forall s'. reachable step s s' ==> sp s'))
      (ensures ag step sp s)
=
  introduce forall (p:path a). (is_run step p /\ p 0 == s) ==> holds_G sp p
  with begin
    introduce (is_run step p /\ p 0 == s) ==> holds_G sp p
    with begin
      introduce forall (i:nat). sp (p i)
      with begin
        lemma_run_reaches step p i
      end
    end
  end

(**
  An inductive invariant `inv` that (a) holds initially and (b) is preserved by
  every step, holds on all reachable states — and hence yields `AG inv`.
  This packages `stable_on_closure` with `lemma_ag_of_invariant`.
**)
let lemma_ag_of_inductive
  (#a:Type)
  (step:binrel a)
  (inv:sprop a)
  (s:a)
  : Lemma
      (requires
        inv s /\
        (forall x y. inv x /\ step x y ==> inv y))
      (ensures
        (forall s'. reachable step s s' ==> inv s') /\
        ag step inv s)
=
  R.stable_on_closure step inv ();
  lemma_ag_of_invariant step inv s
