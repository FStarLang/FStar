module Bug1392

open FStar.Tactics

let unsquash #a : a -> squash a =
  fun _ -> ()

let broken (a: Type0) =
  assert_by_tactic a (fun () ->
                        apply (`unsquash); //(unsquash #a));
                        let g = cur_goal () in
                        let aa = unquote #Type0 g in
                        let xx : aa = admit #aa () in
                        exact (quote xx))
