module Nest

(* This is simply testing that #1065.2 doesn't pop back up again *)

open FStar.Tactics

[@plugin]
let tau = fun () -> pointwise (fun () -> pointwise trefl; trefl ())

let _ = assert_by_tactic (3 == 3) tau
