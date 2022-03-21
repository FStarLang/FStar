module NormMachineInteger
open FStar.Tactics
open FStar.UInt32

let check_norm ()
  : Tac unit
  = norm [delta; iota; primops];
    let g = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) t0 t1 ->
      if term_eq t0 t1
      then trefl ()
      else fail "Not syntactically equal"
    | _ -> fail "Unexpected goal"

let test = assert (1ul +^ 2ul == 3ul)
               by (check_norm())
