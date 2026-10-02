module CoreCacheCatch

(* Pushing a guard as an SMT goal commits the core checker's cache, which is
   the undertaking to prove that guard: [Core.guard] drops a later occurrence
   of it whose context includes this one, on the grounds that someone is
   already obliged to prove it.

   [catch] discards the goals its branch pushed, so it has to drop that
   undertaking too, or a guard emitted inside a failing branch would silence an
   identical one emitted afterwards -- and the second one would never be
   proved.

   Here the guard is [0 == 1]. It is emitted once inside a [catch] that then
   fails, and once outside. The second must still be reported. *)

open FStar.Tactics.V2

let emit_false_guard () : Tac unit =
  let g = top_env () in
  match core_check_term g (`(0 <: int)) (`(x:int{x == 1})) E_Total with
  | (Some _, _) -> ()
  | (None, _) -> fail "core_check_term rejected the term outright"

[@@expect_failure [19]]
let discarded_guard_is_not_an_undertaking =
  assert True by (
    let _ : either exn unit =
      catch (fun () -> emit_false_guard (); fail "discard the goal") in
    emit_false_guard ())
