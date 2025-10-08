module Pulse.Lib.InsertionSort
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.TotalOrder

let rec upd_count (#t:Type) {| total_order t |} (s:Seq.seq t) (i:nat) (x:t) (z:t)
: Lemma
  (requires i < Seq.length s)
  (ensures (
    if Seq.index s i ==? x
    then Seq.upd s i x == s
    else (
      if z ==? x
      then count x (Seq.upd s i x) == count x s + 1
      else if z ==? Seq.index s i
      then count z (Seq.upd s i x) == count z s - 1
      else count z (Seq.upd s i x) == count z s)
  ))
  (decreases Seq.length s)
  [SMTPat (count z  (Seq.upd s i x))]
= if Seq.index s i ==? x
  then assert (Seq.equal (Seq.upd s i x) s)
  else (
    if i = 0 then ()
    else upd_count (Seq.tail s) (i - 1) x z
  )

let ordered 
      (#t:Type)
      {| total_order t |}
      (s0 s1:Seq.seq t)
= forall i j. 
  0 <= i /\ i < Seq.length s0 /\
  0 <= j /\ j < Seq.length s1  ==>
  Seq.index s0 i <=? Seq.index s1 j 

let slice_index (#t:Type) (s:Seq.seq t) (i j k:nat) 
: Lemma 
  (ensures (i <= j /\ j < k /\ k <= Seq.length s ==>
            Seq.index s j == Seq.index (Seq.slice s i k) (j - i <: nat)))
  [SMTPat (Seq.slice s i k);
   SMTPat (Seq.index s j)]
= ()

let sorted_concat
      (#t:Type)
      {| total_order t |}
      (s0 s1:Seq.seq t)
: Lemma 
  (requires
    sorted s0 /\
    sorted s1 /\
    ordered s0 s1)
  (ensures sorted (Seq.append s0 s1))
= () 

fn op_Array_Assignment u#a
        (#t: Type u#a)
        (a: array t)
        (i: SZ.t)
        (v: t)
        (#s: erased (Seq.seq t) {SZ.v i < Seq.length s})
requires pts_to a s
ensures  exists* s'. 
  pts_to a s' **
  pure (s' == Seq.upd s (SZ.v i) v)
{
  a.(i) <- v;
}

let inner_invariant 
      (#t:Type)
      {| total_order t |}
      (s0 s':Seq.seq t)
      (key:t)
      (vi vj:SZ.t)
      (done:bool)
= 0 <= SZ.v vi /\
  SZ.v vi < SZ.v vj /\
  SZ.v vj < Seq.length s' /\ (
  let ai = Seq.index s' (SZ.v vi) in
  let lhs = Seq.slice s' 0 (SZ.v vi + 1 <: nat) in
  let rhs = Seq.slice s' (SZ.v vi + 1) (SZ.v vj + 1 <: nat) in
  let slot = Seq.index s' (SZ.v vi + 1 <: nat) in
  sorted lhs /\
  sorted rhs /\
  ordered lhs (Seq.upd rhs 0 ai) /\
  (if done
   then vi == 0sz /\ slot == ai /\ permutation s0 (Seq.upd s' 0 key)
   else if SZ.v vi + 1 = SZ.v vj then slot == key /\ permutation s0 s'
   else slot == Seq.index s' (SZ.v vi + 2) /\ permutation s0 (Seq.upd s' (SZ.v vi + 1) key)) /\
  (forall (k:nat). 0 <= k /\ k < Seq.length rhs ==> Seq.index rhs k >=? key))

#push-options "--fuel 0 --ifuel 1 --split_queries no --z3rlimit_factor 5"
#restart-solver
let step_inner_invariant
      (#t:Type)
      {| total_order t |}
      (s s0 s1:Seq.seq t) (key:t)
      (vi vj : SZ.t)
: Lemma
  (requires 
    inner_invariant s s0 key vi vj false /\
    Seq.index s0 (SZ.v vi) >? key /\
    s1 == Seq.upd s0 (SZ.v vi + 1 <: nat) (Seq.index s0 (SZ.v vi)))
  (ensures (
    let vi' = if vi = 0sz then 0sz else SZ.(vi -^ 1sz) in
    let done = (vi = 0sz) in
    inner_invariant s s1 key vi' vj done))
= () 
#pop-options

#push-options "--fuel 0 --ifuel 1 --split_queries no --z3rlimit_factor 2"
#restart-solver
let step_outer_invariant
      (#t:Type)
      {| total_order t |}
      (s s0:Seq.seq t) (key:t)
      (vi vj : SZ.t)
      (done:bool)
: Lemma
  (requires 
    inner_invariant s s0 key vi vj done /\
    (done \/ Seq.index s0 (SZ.v vi) <=? key))
  (ensures (
    let ix = if done then 0 else SZ.v vi + 1 <: nat in
    let s' = Seq.upd s0 ix key in
    sorted (Seq.slice s' 0 (SZ.v vj + 1 <: nat)) /\
    permutation s s'))
= () 
#pop-options


fn insertion_sort u#a
      (#t:Type u#a)
      {| total_order t |}
      (a:A.array t)
      (len:SZ.t)
      (#s:erased (Seq.seq t){ Seq.length s == SZ.v len })
requires a |-> s
requires pure (SZ.v len > 0)
ensures exists* s'. (a |-> s') **
  pure (sorted #t s' /\ permutation s s')
{
  let mut j = 1sz;
  while (
    SZ.(!j <^ len)
  )
  invariant (
    exists* vj (s':Seq.seq t).
      (j |-> vj) **
      (a |-> s') **
      pure (
        1 <= SZ.v vj /\ 
        SZ.v vj <= SZ.v len /\
        Seq.length s' == Seq.length s /\
        sorted (Seq.slice s' 0 (SZ.v vj)) /\
        permutation s s'
      )
  )
  {
    pts_to_len a;
    let vj = !j;
    j := SZ.(vj +^ 1sz);
    let key = a.(vj);
    let mut i : SZ.t = SZ.(vj -^ 1sz);
    let mut done = false;
    with ss. assert (a |-> ss);
    while (
      (not !done && a.(!i) >? key)
    )
    invariant (
      exists* (vi:SZ.t) (d:bool) (s':Seq.seq t { inner_invariant ss s' key vi vj d}).
        (i |-> vi) ** (a |-> s') ** (done |-> d) 
    )
    {
      let vi = !i;
      with s0. assert (a |-> s0);
      a.(SZ.(vi +^ 1sz)) <- a.(vi);
      with s1. assert (a |-> s1);
      step_inner_invariant ss s0 s1 key vi vj;
      if (vi = 0sz) { done := true }
      else { i := SZ.(vi -^ 1sz); }
    };
    with s0. assert (a |-> s0);
    let vi = !i;
    let done = !done;
    pts_to_len a;
    step_outer_invariant ss s0 key vi vj done;
    if (done)
    {
      a.(vi) <- key;
    }
    else 
    {
      a.(SZ.(vi +^ 1sz)) <- key;
    }
  };
  with s'. assert (a |-> s');
  assert pure (Seq.slice s' 0 (Seq.length s') `Seq.equal` s');
}

instance total_order_int : total_order int = {
  compare = FStar.Order.compare_int;
  properties = ()
}

fn insertion_sort_int
      (a:A.array int)
      (len:SZ.t)
      (#s:erased (Seq.seq int) { Seq.length s == SZ.v len })
requires
  a |-> s
requires pure (SZ.v len > 0)
ensures
  exists* s'. (a |-> s') **
  pure (sorted s' /\ permutation s s')
{
  insertion_sort a len
}
