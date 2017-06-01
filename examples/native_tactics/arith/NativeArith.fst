module NativeArith

open FStar.Tactics
open FStar.Tactics.Arith
open FStar.List

let tau1 : tactic unit =
    prune "";;
    FStar.Tactics.split;;
    (* rev part *)
      addns "FStar.List";;
      addns "Prims";;
      smt ();;
    (* arithmetic part *)
      addns "Prims";;
      g <-- cur_goal;
      let _, t = g in
      smt ();;
    return ()