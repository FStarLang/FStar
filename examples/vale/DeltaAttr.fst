module DeltaAttr

open FStar.Tactics

irreducible let myattr = ()
irreducible let otherattr = ()

let normalize (#t:Type) (steps : list norm_step) (x:t) : Tac unit =
  dup ();
  exact (quote x);
  norm steps;
  trefl ()

[@myattr]
let add_1 (x:int) : int = x + 1

[@myattr]
let sub_1 (x:int) : int = x - 1

[@otherattr]
let add (x:int) : int = x + x

let test_1 (x:int) : int = synth_by_tactic
  (fun () -> normalize [delta_attr myattr] (add (sub_1 (add_1 x))))

let test_2 (x:int) : int = synth_by_tactic
  (fun () -> normalize [delta_attr otherattr] (add (sub_1 (add_1 x))))

let test_3 (x:int) : int = synth_by_tactic
  (fun () -> normalize [delta_attr myattr; delta_attr otherattr] (add (sub_1 (add_1 x))))

let test_4 (x:int) : int = synth_by_tactic
  (fun () -> normalize [delta_attr myattr; delta_only [`%(add)]] (add (sub_1 (add_1 x))))

// more than one delta_only specified
let test_5 (x:int) : int = synth_by_tactic
  (fun () -> normalize [delta_only [`%(add)];delta_only[`%(add_1)];delta_only [`%(sub_1)]] (add (sub_1 (add_1 x))))
