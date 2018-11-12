module Nest

(* This is simply testing that #1065.2 doesn't pop back up again *)

open FStar.Tactics

let _ = assert_by_tactic (3 == 3)
                         (fun () -> pointwise (fun () -> pointwise trefl; trefl ()))
