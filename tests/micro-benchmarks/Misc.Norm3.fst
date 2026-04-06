module Misc.Norm3

(* This is inspired by a regression in Pulse during the development
of https://github.com/FStarLang/FStar/pull/3385. If the pass to erase
universes during SMT encoding operates under the quoted universes, this
will fail to typecheck. *)

open FStar.Ghost
open FStar.Tactics
open FStar.Reflection.Typing
module R = FStar.Reflection

[@@erasable]
noeq
type my_erased (a:Type) = | E of a

let test (r_env goal : _) : Tac unit =
  let u0 = pack_universe Uv_Zero in
  let goal_typing :
    my_erased (typing_token r_env goal (E_Total, pack_ln (R.Tv_Type u0)))
    = magic()
  in
  let goal_typing_tok : squash (typing_token r_env goal (E_Total, pack_ln (R.Tv_Type u0))) =
    match goal_typing with E x -> ()
  in
  ()

(* This should always work regardless of the comment above. *)
let test2 (r_env goal u0 : _) : Tac unit =
  let goal_typing :
    my_erased (typing_token r_env goal (E_Total, pack_ln (R.Tv_Type u0)))
    = magic()
  in
  let goal_typing_tok : squash (typing_token r_env goal (E_Total, pack_ln (R.Tv_Type u0))) =
    match goal_typing with E x -> ()
  in
  ()
