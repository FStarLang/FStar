module PulseExample.BinarySearch
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.TotalOrder
open Pulse.Lib.BoundedIntegers

fn binary_search
      (#t:Type)
      {| total_order t |}
      (a:A.array t)
      (key:t)
      (len:SZ.t)
      (#s:erased (Seq.seq t) { Seq.length s == SZ.v len })
      (#p:perm)
requires
  pts_to a #p s **
  pure ((forall (i j: SZ.t).
          i <= j /\
          j < len ==>
          Seq.index s (SZ.v i) <=? Seq.index s (SZ.v j)) /\
        (exists (k:SZ.t).
          k < len /\
          Seq.index s (SZ.v k) == key))
returns k:SZ.t
ensures
  pts_to a #p s **
  pure (k < len /\ Seq.index s (SZ.v k) == key)
{
  let mut i1 : SZ.t = 0sz;
  let mut i2 : SZ.t = len - 1sz;
  while (
    let v1 = !i1;
    let v2 = !i2;
    (v1 <> v2)
  )
  invariant b . (
    exists* v1 v2.
      pts_to i1 v1 **
      pts_to i2 v2 **
      pts_to a #p s **
      pure (
        (b == (v1 <> v2)) /\
        v2 < len /\
        (exists (i:SZ.t). v1 <= i /\ i <= v2 /\ Seq.index s (SZ.v i) == key) /\
        (forall (i j: SZ.t). {:pattern Seq.index s (SZ.v i); Seq.index s (SZ.v j)}
          i <= j /\
          j < len ==>
          Seq.index s (SZ.v i) <=? Seq.index s (SZ.v j)))
  )
  { 
    let v1 = !i1;
    let v2 = !i2;
    let ix = v1 + (v2 - v1) / 2sz;
    let a_ix = a.(ix);
    if (a_ix <? key)
    {
      i1 := ix + 1sz;
    }
    else
    {
      i2 := ix;
    }
  };
  !i1
}

instance total_order_int : total_order int = {
  compare = FStar.Order.compare_int;
  properties = ()
}

fn binary_search_int
      (a:A.array int)
      (key:int)
      (len:SZ.t)
      (#s:erased (Seq.seq int) { Seq.length s == SZ.v len })
      (#p:perm)
requires
  pts_to a #p s **
  pure ((forall (i j: SZ.t).
          i <= j /\
          j < len ==>
          Seq.index s (SZ.v i) <= Seq.index s (SZ.v j)) /\
        (exists (k:SZ.t).
          k < len /\
          Seq.index s (SZ.v k) == key))
returns k:SZ.t
ensures
  pts_to a #p s **
  pure (k < len /\ Seq.index s (SZ.v k) == key)
{ 
  binary_search a key len
}
