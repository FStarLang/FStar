module Pose

open FStar.Tactics

let lem (x y : int) : squash False =
    admit ()

let _ = assert_by_tactic False
            (fun () -> let _ = pose (`(lem 3 9)) in ())
                       
