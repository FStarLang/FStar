(* STATUS : lax type checks but not verified, work in progress *)

module Carry

open Heap 
open ST
open Limb
open Bigint
open IntLib
open Seq
open Axiomatic
open Eval
open Array

val blit : #a:Type -> i:array a -> i_idx:nat -> o:array a -> o_idx:nat -> len:nat -> 
		  ST unit
		     (requires (fun h -> 
				(contains h i)
				/\ (contains h o)
				/\ (len + i_idx <= Seq.length (sel h i))
				/\ (len + o_idx <= Seq.length (sel h o))
		     ))
				   (* Need of a separation clause ? *)
		     (ensures (fun h0 u h1 -> 
			       (contains h1 i)
			       /\ (contains h1 o)
			       /\ (modifies !{o} h0 h1)
			       /\ (len + i_idx <= Seq.length (sel h0 i))
			       /\ (len + o_idx <= Seq.length (sel h0 o))
			       /\ (forall (n:nat). n < len 
				   ==> Seq.index (sel h1 o) (n+o_idx) = Seq.index (sel h0 i) (n+i_idx))
		     ))

val carry : 
  a:bigint -> 
  ST unit
     (requires (fun h -> 
		(inHeap h a)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h1 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (Normalized h1 a)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
     ))
	       
val carry_mod:
  a:bigint -> m:bigint -> 
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h m)
		/\ (eval h m (getLength h m) > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (inHeap h0 m)
	       /\ (eval h0 m (getLength h0 m) > 0)
	       /\ (Bigint63.t b = Bigint63.t a)
	       /\ (getLength h1 b > 0)
	       /\ (bitweight (Bigint63.t b) (getLength h1 b) > eval h0 m (getLength h0 m))
	       /\ (bitweight (Bigint63.t b) (getLength h1 b - 1) <= eval h0 m (getLength h0 m))
	       /\ (forall (i:nat). i < getLength h1 b 
		   ==> getValue h1 b i >= 0)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a) % eval h0 m (getLength h0 m))
     ))
