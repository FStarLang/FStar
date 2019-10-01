module Bug1812

let op_any_word o = 1 // any identifier fitting the pattern `op_*_*` works
let t = op_any_word

open FStar.Tactics

let _ =
    assert True
        by (let s = term_to_string (`(op_any_word ())) in
            if s = "Bug1812.op_any_word ()" then ()
            else fail "wrong")
