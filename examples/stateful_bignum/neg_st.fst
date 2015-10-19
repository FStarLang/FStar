module Neg

open Heap
open ST
open IntLib
open Bigint

val neg_aux :
  b:bigint -> ghost_b:Seq.seq (tint ocaml63) -> ctr:nat ->
  ST unit
    (requires (fun h -> 
      (inHeap h b)
      /\ (ctr <= getLength h b)
      /\ (Seq.length ghost_b = getLength h b)
      /\ (forall (i:nat). i < ctr 
	  ==> (getSize h b i = dfst (Seq.index ghost_b i)
	      /\ getValue h b i = - (dsnd (Seq.index ghost_b i))))
      /\ (forall (i:nat). (i >= ctr /\ i < getLength h b)
	  ==> (getSize h b i = dfst (Seq.index ghost_b i)
	      /\ getValue h b i = dsnd (Seq.index ghost_b i)))
     ))
    (ensures (fun h0 u h1 ->
      (inHeap h1 b)
      /\ (inHeap h0 b)
      /\ (modifies !{Bigint63.data b} h0 h1)
      /\ (Seq.length ghost_b = getLength h0 b)
      /\ (ctr <= getLength h0 b)
      /\ (getLength h0 b = getLength h1 b)
      /\ (forall (i:nat). i < getLength h1 b
	  ==> (getSize h1 b i = dfst (Seq.index ghost_b i)
	      /\ getValue h1 b i = - (dsnd (Seq.index ghost_b i) )))
     ))
let rec neg_aux b ghost_b ctr =
  match get_length b - ctr with
  | 0 -> ()
  | _ -> 
     let bi = - (get b ctr) in
     let h0 = (ST.get()) in
     let size_bi = 
       (getSize h0 b ctr) in
     let bi = mk_tint b size_bi bi in
     Bigint.updateBigint b ctr bi;
     neg_aux b ghost_b (ctr+1)	    
	   

val neg:
  b:bigint -> 
  ST bigint
    (requires (fun h -> 
      (inHeap h b)
      /\ (getLength h b > 0)
     ))
    (ensures (fun h0 c h1 ->
      (inHeap h0 b)
      /\ (getLength h0 b > 0)
      /\ (inHeap h1 c)
      /\ (modifies !{} h0 h1)
      /\ (getLength h1 c = getLength h0 b)
      /\ (forall (i:nat). i < getLength h1 c
	  ==> (getSize h0 b i = getSize h1 c i
	      /\ getValue h0 b i = - (getValue h1 c i)))
     ))
let neg b =
  let h0 = (ST.get()) in
  let c = Bigint.copy b in
  let h0' = (ST.get()) in
  //cut (modifies !{} h0 h0');
  neg_aux c ((Array.to_seq (Bigint63.data c))) 0;
  let h1 = (ST.get()) in
  (cut (True /\ inHeap h1 c));
  //cut (True /\ getLength h0 b = getLength h1 c);
  //cut (modifies !{Bigint63.data c} h0' h1);
  //cut (modifies!{} h0 h1);
  c
