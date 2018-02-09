module Bug1347

open FStar.Tactics

let t1 : tactic unit =
  dump "Before";;
  u <-- forall_intro;
  smt

let fyz (yz:(int * int)) : Type = let (y, z) = yz in True

assume val g0 (x:int) : Ghost (int * int)
  (requires True)
//  (ensures fyz) // SUCCEEDS
//  (ensures (fun (yz:(int * int)) -> let xx = yz in True)) // SUCCEEDS
  (ensures (fun (yz:(int * int)) -> let (y, z) = yz in True)) // FAILS

let foo (x:nat) =
(
  let yz:(int * int) = g0 x in
  ()
) <: (Lemma True) by t1
