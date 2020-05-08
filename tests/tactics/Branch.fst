module Branch

open FStar.Tactics

type abc = | A of int | B | C

assume val p : prop
assume val q : prop
assume val r : prop

assume val ep : squash p
assume val eq : squash q
assume val er : squash r

let test0 (x:abc) =
    assert (match x with | A x -> q | _ -> r)
        by (branch_on_match ();
            guard (List.length (goals ()) = 3);
            exact (`eq);
            exact (`er);
            exact (`er))

(*
let test (x:abc) =
    assert (p /\ (match x with | A x -> q | _ -> r))
        by (explode ();
            guard (List.length (goals ()) = 4);
            exact (`ep);
            exact (`eq);
            exact (`er);
            exact (`er))
            *)
