module Arith

// Testing out an arithmetic tactic.

open FStar.Tactics
open FStar.Reflection.Arith
open FStar.List

// decide if the current goal is arith
let is_arith_goal : tactic bool =
    eg <-- cur_goal;
    let _, g = eg in
    match is_arith_prop g 0 with
    | Inr _ -> return true
    | Inl s -> (print ("arith: not an arith prop: " ^ term_to_string g);;
                print ("message: " ^ s);;
                return false)

val split_arith : unit -> Tac unit
let rec split_arith = fun () -> (
    b <-- is_arith_goal;
    if b then (
        prune "";;
        addns "Prims";;
        smt
    ) else (
        eg <-- cur_goal;
        let _, g = eg in
        match term_as_formula g with
        | True_ -> trivial
        | And l r -> seq FStar.Tactics.split split_arith
        | _ -> return ()
    )) ()
    

// TODO: even if encoding this module to SMT, x is not given a HasType
//assume val x : int

let lem0 (x:int) =
    assert_by_tactic (prune "";;
                      addns "Prims"
                     ) (op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)

// Can't locally define tactics
let tau1 : tactic unit =
    prune "";;
    FStar.Tactics.split;;
    (* rev part *)
      addns "FStar.List";;
      addns "Prims";;
      smt;;
    (* arithmetic part *)
      addns "Prims";;
      g <-- cur_goal;
      let _, t = g in
      print ("goal = " ^ term_to_string t);;
      smt;;
    return ()

let lem1 (x:int) =
    assert_by_tactic tau1 (FStar.List.Tot.rev [1;2;3;4] == [4;3;2;1]
                             /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)

let lem2 (x:int) =
    assert_by_tactic split_arith (FStar.List.Tot.rev [1;4] == [4;1]
                                    /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
