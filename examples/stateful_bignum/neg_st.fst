module Neg

open Heap
open ST
open IntLib
open Bigint

assume val neg:
    b:bigint -> 
    ST bigint
      (requires (fun h -> 
	(inHeap h b)
       ))
      (ensures (fun h0 c h1 ->
	(inHeap h0 b)
	/\ (inHeap h1 c)
	/\ (getLength h1 c = getLength h0 b)
	/\ (forall (i:nat). i < getLength h1 c
	    ==> (getSize h0 b i = getSize h1 c i
		/\ getValue h0 b i = getValue h1 c i))
       ))
