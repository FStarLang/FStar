module ArithExample

open FStar.Tactics
open NativeArith

let lem1 (x:int) =
    assert_by_tactic tau1 (List.rev [1;2;3;4] == [4;3;2;1]
                             /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
