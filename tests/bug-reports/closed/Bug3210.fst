module Bug3210
friend FStar.Tactics.NamedView
// ^ We need this (at the start of the file for fly_deps)
// to bring the definitions into scope,
// since NamedView has an interface.

module Tac = FStar.Tactics.V2

let lift_ty: Tac.term -> Tac.Tac Tac.term =
  let rec go (t: Tac.term): Tac.Tac Tac.term =
    t
  in Tac.visit_tm go

[@@Tac.preprocess_with lift_ty]
let rec count (x: int): int =
  if x > 0 then count (x - 1) else 0

(* Inspecting and packing back this term fails for the same reason. *)
let test2 () : Tac.Tac unit =
  let tm = `(match 0 with nm -> nm) in
  let tv = Tac.inspect_ln tm in
  let tm = Tac.pack_ln tv in
  Tac.print (Tac.term_to_string tm)
let _ = assert True by test2 ()

(* This would surprisingly work in the NamedView, since it is a plugin
and works behind the `sealed` abstraction. But, using --no_plugins
did make it fail. *)

let test3 () : Tac.Tac unit =
  let open FStar.Tactics.V2 in
  let open FStar.Tactics.NamedView in
  let tm = `(match 0 with nm -> nm) in
  let tv = inspect tm in
  let tm = pack tv in
  print (term_to_string tm)

#push-options "--no_plugins"
let _ = assert True by test3 ()
#pop-options
