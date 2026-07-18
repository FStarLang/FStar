module PluginReturned

open FStar.Tactics.V2

(* This used to trip the normalizer due to an extra Meta_monadic
node on the returned and_elim or inspect (which are plugins). *)

assume val p : prop
assume val q : prop

let foo (b:bool) : Tac (term -> Tac unit) =
  if b
  then and_elim
  else fail "no"

let test (x : squash (p /\ q)) =
  assert True by (
    let f = foo true in
    f (quote x);
    dump ""
  )

let bar () : Tac (term -> Tac term_view) =
  inspect

let test2 () =
  assert True by (
    let f = bar () in
    let tv = f (`1) in
    dump ""
  )
