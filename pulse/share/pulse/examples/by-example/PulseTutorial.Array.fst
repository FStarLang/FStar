(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseTutorial.Array
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array

module SZ = FStar.SizeT

//readi$
fn read_i
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type)
  (arr:array t)
  (#p:perm)
  (#s:erased (Seq.seq t))
  (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr #p s
  returns x:t
  ensures pts_to arr #p s ** pure (x == Seq.index s (SZ.v i))
{
  arr.(i)
}
//end readi$

//writei$
fn write_i (#t:Type) (arr:array t) (#s:erased (Seq.seq t)) (x:t) (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr s
  ensures pts_to arr (Seq.upd s (SZ.v i) x)
{
  arr.(i) <- x
}
//end writei$


//writeipbegin$
[@@ expect_failure]

fn write_ip #t (arr:array t) (#p:perm) (#s:erased _) (x:t) (i:SZ.t { SZ.v i < Seq.length s })
  requires pts_to arr #p s
  ensures pts_to arr #p (Seq.upd s (SZ.v i) x)
{
  arr.(i) <- x
}

//writeipend$

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
open FStar.SizeT


//comparesigbegin$
fn compare
  (#[@@@ Rust_generics_bounds ["PartialEq"; "Copy"]] t:eqtype)
  #p1 #p2
  (a1 a2:A.array t)
  (l:SZ.t) 
  requires (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (res <==> Seq.equal 's1 's2)
  )
//comparesigend$
//compareimplbegin$
{
  let mut i = 0sz;
  while (
    let vi = !i;
    if (vi <^ l) {
      let v1 = a1.(vi);
      let v2 = a2.(vi);
      (v1 = v2)
    } else {
      false
    }
  )
  invariant b.
  exists* vi. ( 
    R.pts_to i vi **
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l && Seq.index 's1 (SZ.v vi) = Seq.index 's2 (SZ.v vi))) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index 's1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i; 
    i := vi +^ 1sz
  };
  let vi = !i;
  let res = vi = l;
  res
}
//compareimplend$


 //copy$
fn copy
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type0)
  (a1 a2:A.array t)
  (l:SZ.t)
  (#p2:perm)
  requires (
    A.pts_to a1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  ensures (
    (exists* s1. A.pts_to a1 s1 ** pure (Seq.equal s1 's2)) **
    A.pts_to a2 #p2 's2
  )
{
  let mut i = 0sz;
  while (
    let vi = !i;
    (vi <^ l)
  )
  invariant b.
  exists* vi s1. ( 
    R.pts_to i vi **
    A.pts_to a1 s1 **
    A.pts_to a2 #p2 's2 **
    pure (
      Seq.length s1 == Seq.length 's2 /\
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l)) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index s1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    let v = a2.(vi);
    a1.(vi) <- v;
    i := vi +^ 1sz
  }
}
//end copy$


//copy2sigbegin$
fn copy2
  (#[@@@ Rust_generics_bounds ["Copy"]] t:Type0)
  (a1 a2:A.array t)
  (l:SZ.t)
  (#p2:perm)
  requires (
    A.pts_to a1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == SZ.v l)
  )
  ensures (
    A.pts_to a1 's2 **
    A.pts_to a2 #p2 's2
  )
//copy2sigend$
{
  let mut i = 0sz;
  while (
    let vi = !i;
    (vi <^ l)
  )
  invariant b.
  exists* vi s1. ( 
    R.pts_to i vi **
    A.pts_to a1 s1 **
    A.pts_to a2 #p2 's2 **
    pure (
      Seq.length s1 == Seq.length 's2 /\
      SZ.v vi <= SZ.v l /\
      (b == (SZ.v vi < SZ.v l)) /\
      (forall (i:nat). i < SZ.v vi ==> Seq.index s1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i;
    let v = a2.(vi);
    a1.(vi) <- v;
    i := vi +^ 1sz
  };
  //copy2rewriting$
  // after the loop
  with v1 s1. _; //bind existentially bound witnesses from the invariant
  Seq.lemma_eq_elim s1 's2; //call an F* lemma to prove that s1 == 's2
  ()
  //copy2rewritingend$
}


 //compare_stack_arrays$
fn compare_stack_arrays ()
  requires emp
  ensures emp
{
  // |- emp
  let mut a1 = [| 0; 2sz |];
  // a1:array int |- pts_to a1 (Seq.create 0 (SZ.v 2))
  let mut a2 = [| 0; 2sz |];
  // a1 a2:array int |- pts_to a1 (Seq.create 0 (SZ.v 2)) ** pts_to a2 (Seq.create 0 (SZ.v 2))
  let b = compare a1 a2 2sz;
  assert (pure b)
}
//end compare_stack_arrays$

//ret_stack_array$
[@@ expect_failure]

fn ret_stack_array ()
  requires emp
  returns a:array int
  ensures pts_to a (Seq.create 2 0)
{
  let mut a1 = [| 0; 2sz |];
  a1  // cannot prove pts_to a (Seq.create 0 2) in the context emp
}

//ret_stack_array_end$

//heaparray$
module V = Pulse.Lib.Vec

 
fn heap_arrays ()
  requires emp
  returns a:V.vec int
  ensures V.pts_to a (Seq.create 2 0)
{
  let a1 = V.alloc 0 2sz;
  let a2 = V.alloc 0 2sz;
  V.free a1;
  a2  // returning vec is ok
}

//heaparrayend$

 //copyuse$
fn copy_app ([@@@ Rust_mut_binder] v:V.vec int)
  requires exists* s. V.pts_to v s ** pure (Seq.length s == 2)
  ensures V.pts_to v (Seq.create 2 0)
{
  let mut a = [| 0; 2sz |];
  // v, s |- V.pts_to v s ** ...
  V.to_array_pts_to v;
  // v, s |- pts_to (vec_to_array v) s ** ...
  copy2 (V.vec_to_array v) a 2sz;
  // v, s |- pts_to (vec_to_array v) (Seq.create 2 0) ** ...
  V.to_vec_pts_to v
  // v, s |- V.pts_to v (Seq.create 2 0) ** ...
}
//end copyuse$