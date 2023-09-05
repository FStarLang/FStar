module Pulse.Typing.Util

module L = FStar.List.Tot
module T = FStar.Tactics.V2

(* Call check_equiv under a SMTSync guard policy *)
let check_equiv_now tcenv t0 t1 =
  T.with_policy SMTSync (fun () ->
    T.check_equiv tcenv t0 t1)

let universe_of_now g e =
  T.with_policy SMTSync (fun () ->
    T.universe_of g e)
