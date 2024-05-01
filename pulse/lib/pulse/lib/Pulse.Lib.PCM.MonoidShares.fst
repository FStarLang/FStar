module Pulse.Lib.PCM.MonoidShares
open FStar.PCM
module M = FStar.Algebra.CommMonoid

let pcm_of (#a:Type) (m:M.cm a) (v:a)
: pcm a
= let p : pcm' a  = {
      composable = (fun _ _ -> True);
      op = m.mult;
      one = m.unit
  } in
  {
    p;
    comm = (fun x y -> m.commutativity x y);
    assoc = (fun x y z -> m.associativity x y z);
    assoc_r = (fun x y z -> m.associativity x y z);
    is_unit = (fun x -> m.commutativity x m.unit; m.identity x); 
    refine = (fun x -> x == v);
  }

let nat_plus_cm : M.cm nat =
  M.CM #nat 0 (fun x y -> x + y) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let pcm_of_nat (v:nat) = pcm_of nat_plus_cm v
let test (x:nat) (u v w:nat) = 
  let p = pcm_of_nat x in
  assume (p.refine u); //test
  assert (u == x);
  assume (compatible p (v + w) x); //test
  assert (v + w <= x)