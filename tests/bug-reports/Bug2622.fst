module Bug2622

open FStar.Tactics

type ind : Type u#1 = | A

assume val p : prop

assume val ep : squash p

let test0 (x:ind) =
    assert (match x with | A -> p)
        by (branch_on_match ();
            guard (List.length (goals ()) = 1);
            exact (`ep))
