module Arith

//

open FStar.Tactics
open FStar.Tactics.Arith
open FStar.List
open FStar.Mul

let lem0 (x:int) =
    assert (op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
        by (prune ""; addns "Prims")

// Can't locally define tactics
let tau1 () : Tac unit =
    prune "";
    FStar.Tactics.split ();
    (* rev part *)
      addns "FStar.List";
      addns "Prims";
      smt ();
    (* arithmetic part *)
      addns "Prims";
      smt ()

let lem1 (x:int) =
    assert (List.rev [1;2;3;4] == [4;3;2;1] /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
        by tau1 ()

let lem2 (x:int) =
    assert_by_tactic (List.rev [1;2;3;4] == [4;3;2;1] /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
                     split_arith

let lem3 (x y z : int) (f : int -> int) =
    assume (x + f y > 2);
    assert_by_tactic (x + f y > 1 /\ f == f /\ List.length (List.Tot.tail [1;2;3]) == 2)
                     split_arith

let lem4 (x y z : int) (f : int -> int) =
    assume (forall y. f y > y);
    assert_by_tactic (f 5 > 1 /\ f == f /\ List.length (List.Tot.tail [1;2;3]) == 2
                     /\ 1 + 2 == 3 /\ (forall x. f (f x) > x)
                     /\ (forall (x y : int). x > 2 /\ y > 2 ==> op_Multiply x y > x + y))
                     split_arith
