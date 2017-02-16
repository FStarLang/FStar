module Loops
open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

reifiable 
let rec sum_up (r:ref int) (from:int) (to:int{from <= to})
    : ST unit (requires (fun h -> h `contains_a_well_typed` r))
	      (ensures (fun _ _ _ -> True))
	      (decreases (to - from))
    = r := !r + from;
      if to <> from
      then sum_up r (from + 1) to

reifiable 
let rec sum_dn (r:ref int) (from:int) (to:int{from <= to})
    : ST unit (requires (fun h -> h `contains_a_well_typed` r))
	      (ensures (fun _ _ _ -> True))
	      (decreases (to - from))
    = r := !r + to;
      if to <> from
      then sum_dn r from (to - 1)

val equiv_sum_up_dn (h0:heap) (h1:heap)
		    (r0:ref int) (r1:ref int)
		    (from:int) (to:int{from <= to})
   : Lemma (h0 `contains_a_well_typed` r0 /\
            h1 `contains_a_well_typed` r1 /\
	    sel h0 r0 == sel h1 r1 ==> (
	    let (_, h0') = reify (sum_up r0 from to) h0 in
	    let (_, h1') = reify (sum_dn r1 from to) h1 in
	    (h0' `contains_a_well_typed` r0 /\
 	     h1' `contains_a_well_typed` r1 /\
	     sel h0' r0 == sel h1' r1)))
let equiv_sum_up_dn h0 h1 r0 r1 from to =
    if from = to
    then ()
    else admit()
	    
   
