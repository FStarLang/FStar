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

val blit : #a:Type -> i:array a -> i_dix:nat -> o:array a -> o_idx:nat -> len:nat -> 
		  ST unit
		     (requires (fun h -> 
				(contains h i)
				/\ (contains h o)
				/\ (len + i_idx <= Seq.length (sel h i))
				/\ (len + o_idx <= Seq.length (sel h o))
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
		(contains h a)
     ))
     (ensures (fun h0 u h1 ->
	       (contains h0 a)
	       /\ (contains h1 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (Normalized h1 a)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
     ))
	       
