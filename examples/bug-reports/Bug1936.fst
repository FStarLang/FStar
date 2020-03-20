module Bug1936

(* more tests in examples/calc/CalcImpl.fst *)

open FStar.Calc

assume val p : prop
assume val q : prop

assume val lem : unit -> Lemma (requires p) (ensures q)

let test () =
  calc (==>) {
    p;
    ==> { lem () }
    q;
  }
