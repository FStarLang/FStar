module FStar.InteractiveHelpers.Propositions

open FStar.List.Tot
open FStar.Tactics
open FStar.Mul
open FStar.InteractiveHelpers.Base
open FStar.InteractiveHelpers.ExploreTerm

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

/// Propositions and assertions.
/// Assertions are propositions to be inserted in the F* code: we differentiate
/// between pre and post assertions, which are to be inserted before a point in
/// the code. For instance, if we analyze an effectful term in F*:
/// [> assert(y <> 0); // pre assertion
/// [> let z = x / y in // term of interest
/// [> assert(...); // post assertion

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

/// Analyze a term to retrieve its effectful information

let proposition_to_string p = term_to_string p

let is_trivial_proposition p =
  term_eq (`Prims.l_True) p

let simp_filter_proposition (e:env) (steps:list norm_step) (p:proposition) :
  Tac (list proposition) =
  let prop1 = norm_term_env e steps p in
  (* If trivial, filter *)
  if term_eq (`Prims.l_True) prop1 then []
  else [prop1]

let simp_filter_propositions (e:env) (steps:list norm_step) (pl:list proposition) :
  Tac (list proposition) =
  List.Tot.flatten (map (simp_filter_proposition e steps) pl)

let simp_filter_assertions (e:env) (steps:list norm_step) (a:assertions) :
  Tac assertions =
  let pres = simp_filter_propositions e steps a.pres in
  let posts = simp_filter_propositions e steps a.posts in
  mk_assertions pres posts
