module Bug1347B

open FStar.Tactics

let test (x : int) =
    assert_by_tactic True
        (fun () ->
            let e = quote (match x with | 0 -> 1 | _ -> 0) in
            if unify e e
            then print ("u = " ^ term_to_string e)
            else fail "Did not unify")
