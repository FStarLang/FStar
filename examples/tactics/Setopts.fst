module Setopts

open FStar.Tactics
open FStar.Mul

let mult_ass (x y z : int) =
    assert_by_tactic ((x + x) * (y * z) = (x * y) * z + (z * x * y))
                     (fun () -> set_options "--smtencoding.elim_box true --z3rlimit 1")
