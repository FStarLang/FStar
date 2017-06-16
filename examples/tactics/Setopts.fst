module Setopts

open FStar.Tactics
open FStar.Mul

let mult_ass (x y z : int) =
    assert_by_tactic (set_options "--smtencoding.elim_box true --z3rlimit 1")
                      ((x + x) * (y * z) = (x * y) * z + (z * x * y))
