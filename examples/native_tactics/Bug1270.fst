module Bug1270

open FStar.Tactics

[@plugin]
let mytac =
    (fun () ->
        (fun () ->
          let _ = forall_intros () in
          let env = cur_env () in
          let hyps = binders_of_env env in
          match hyps with
          | [] -> ()
          | h :: _ -> ()) `or_else` trivial)

let test =
  assert_by_tactic (True ==> True) mytac

