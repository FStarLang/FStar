module FStar.InteractiveHelpers.Propositions

open FStar.Tactics.Effect
open FStar.Stubs.Reflection.Types

/// Propositions and assertions.
/// Assertions are propositions to be inserted in the F* code: we differentiate
/// between pre and post assertions, which are to be inserted before a point in
/// the code. For instance, if we analyze an effectful term in F*:
/// [> assert(y <> 0); // pre assertion
/// [> let z = x / y in // term of interest
/// [> assert(...); // post assertion

/// Analyze a term to retrieve its effectful information

type proposition = term

[@@plugin]
val proposition_to_string : proposition -> Tac string

/// Propositions split between pre and post assertions
[@@plugin]
noeq type assertions = {
  pres : list proposition;
  posts : list proposition;
}

let mk_assertions pres posts : assertions =
  Mkassertions pres posts

(*** Simplification *)
/// Whenever we generate assertions, we simplify them to make them cleaner,
/// prettier and remove the trivial ones. The normalization steps we apply
/// are listed below.
let simpl_norm_steps = [primops; simplify; iota]

/// Simplify the propositions and filter the trivial ones.
/// Check if a proposition is trivial (i.e.: is True)
[@@plugin]
val is_trivial_proposition : proposition -> Tac bool

[@@plugin]
val simp_filter_proposition (e:env) (steps:list norm_step) (p:proposition) :
  Tac (list proposition)

[@@plugin]
val simp_filter_propositions (e:env) (steps:list norm_step) (pl:list proposition) :
  Tac (list proposition)

[@@plugin]
val simp_filter_assertions (e:env) (steps:list norm_step) (a:assertions) :
  Tac assertions
