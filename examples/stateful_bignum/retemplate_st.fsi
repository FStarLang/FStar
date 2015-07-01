module Retemplate 

open Heap
open ST
open Eval
open Bigint

val retemplate:
  a:bigint -> t:template ->
  ST bigint
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (modifies !{} h0 h1)
	       /\ not(contains h0 (Bigint63.data b))
	       /\ (Bigint63.t b = t)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
