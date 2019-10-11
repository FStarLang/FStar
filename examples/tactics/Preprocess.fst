module Preprocess

open FStar.Tactics

let incr_lits_by_1 (t:term) : Tac term =
    match t with
    | Tv_Const (C_Int x) -> Tv_Const (C_Int (x+1))
    | _ -> t

let test_add_1 (x:int) : int =
    _ by (exact (visit_tm incr_lits_by_1 (quote (x + 1))))

[@(preprocess_with (visit_tm incr_lits_by_1))]
let test_add_1' (x:int) : int =
    x + 1

let test () =
  assert (test_add_1' 5 == 7)
