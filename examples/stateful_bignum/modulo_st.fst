module Modulo

open Heap
open ST
open Bigint
open Eval

assume val modulo:
  a:bigint -> b:bigint -> 
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h b)
		/\ (Bigint63.t a = Bigint63.t b)
     ))
     (ensures (fun h0 r h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (getLength h1 a = getLength h0 b)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a) % eval h0 b (getLength h0 b))
     ))
