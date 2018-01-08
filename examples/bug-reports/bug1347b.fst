module Bug1347B

open FStar.Tactics

let test (x : int) =
    assert_by_tactic True
        (e <-- quote (match x with | 0 -> 1 | _ -> 0);
         r <-- unify e e;
         if r
         then print ("u = " ^ term_to_string e)
         else fail "Did not unify")
