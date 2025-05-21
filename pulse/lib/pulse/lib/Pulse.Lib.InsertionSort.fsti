module Pulse.Lib.InsertionSort
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.TotalOrder

let rec count (#t:Type) {| total_order t |} (x:t) (s:Seq.seq t)
: Tot nat (decreases Seq.length s)
= if Seq.length s = 0 then 0
  else if Seq.head s ==? x
  then 1 + count x (Seq.tail s)
  else count x (Seq.tail s)

let permutation 
      (#t:Type)
      {| total_order t |}
      (s0 s1:Seq.seq t)
= forall (x:t). count x s0 == count x s1
    
let sorted 
      (#t:Type)
      {| total_order t |}
      (s:Seq.seq t)
= forall (i j:nat).{:pattern (Seq.index s i); (Seq.index s j)}
  i <= j /\ j < Seq.length s ==> Seq.index s i <=? Seq.index s j

fn insertion_sort
      (#t:Type)
      {| total_order t |}
      (a:A.array t)
      (len:SZ.t)
      (#s:erased (Seq.seq t){ Seq.length s == SZ.v len })
requires a |-> s
requires pure (SZ.v len > 0)
ensures exists* s'. 
  (a |-> s') **
  pure (sorted #t s' /\ permutation s s')
