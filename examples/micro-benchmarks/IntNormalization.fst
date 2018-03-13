module IntNormalization

open FStar.UInt32
open FStar.Tactics

(* Testing that the normalizer reduces these equalities *)

let by_red () : Tac unit =
    norm [primops; delta];
    trivial ()

let _ = assert_by_tactic (0ul = 0ul)
                         by_red
let _ = assert_by_tactic (0ul == 0ul)
                         by_red
let _ = assert_by_tactic (0ul === 0ul)
                         by_red

let _ = assert_by_tactic (0ul <> 1ul)
                         by_red
let _ = assert_by_tactic (~(0ul == 1ul))
                         by_red
let _ = assert_by_tactic (0ul =!= 1ul)
                         by_red
