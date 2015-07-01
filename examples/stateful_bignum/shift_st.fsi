module Shift


open Heap
open ST
open IntLib
open Bigint
open Eval

type norm_bigint = a:bigint{ forall (i:nat). Bigint63.t a i = Bigint63.t a 0 }

val shift:
  a:bigint -> offset:nat ->
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (modifies !{} h0 h1)
	       /\ (getLength h1 b = getLength h0 a + offset)
	       /\ (forall (i:nat).
		   (i < getLength h0 a ==> (getValue h1 b (i+offset) = getValue h0 a i
                                         /\ getSize h1 b (i+offset) = getSize h0 a i))
		   /\ (i < offset ==> (getValue h1 b i = 0 /\ getSize h1 b i = 0)))
	       /\ (eval h1 b (getLength h1 b) = pow2 (offset * (Bigint63.t a 0)) * eval h0 a (getLength h0 a))
     ))
     
		   
