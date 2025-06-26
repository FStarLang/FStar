module PulseTutorialExercises.SumArray
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
module SZ = FStar.SizeT
open FStar.SizeT
module R = Pulse.Lib.Reference
open FStar.Seq


fn read (arr:array int) (s:erased (seq int) { Seq.length s > 0 })
  requires pts_to arr s
  returns x:int
  ensures pts_to arr s ** pure (x == Seq.index s 0)
{
    arr.(0sz) // indices have type FStar.SizeT 
}




[@@expect_failure]

fn read_spec_fails (arr:array int) (s:erased (seq int))
  requires pts_to arr s ** pure (Seq.length s > 0)
  returns x:int
  ensures pts_to arr s ** pure (x == Seq.index s 0)
{
    arr.(0sz) // indices have type FStar.SizeT 
}




fn write (s:erased (seq int)) (arr:array int) (x:int) (i:SizeT.t { v i < length s })
  requires pts_to arr s
  ensures pts_to arr (upd s (v i) x)
{
    arr.(i) <- x
}



fn mk_even (r:ref int)
  requires exists* v. R.pts_to r v
  ensures exists* w. R.pts_to r w ** pure (w % 2 == 0)
{
    let n = !r;
    r := n + n
}


// Elim and intro exists may be done explicitly as well


fn mk_even_explicit (r:R.ref int)
  requires exists* v. R.pts_to r v
  ensures exists* w. R.pts_to r w ** pure (w % 2 == 0)
{
    with v. assert (R.pts_to r v); // when there is only one exists* in the context, can write with v. _
    let n = !r;
    r := n + n;
    introduce exists* w. R.pts_to r w ** pure (w % 2 == 0) with (v + v)
}


module A = Pulse.Lib.Array
module BoundedInts = Pulse.Lib.BoundedIntegers


fn compare (#t:eqtype) #p1 #p2 (a1 a2:A.array t) (l:SZ.t) 
  requires (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (Seq.length 's1 == Seq.length 's2 /\ Seq.length 's2 == v l)
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (res <==> Seq.equal 's1 's2)
  )
{
  open BoundedInts;
  let mut i = 0sz;
  while (
    let vi = !i;
    if (vi < l) {
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
      vi <= l /\
      (b == (vi < l && Seq.index 's1 (v vi) = Seq.index 's2 (v vi))) /\
      (forall (i:nat). i < v vi ==> Seq.index 's1 i == Seq.index 's2 i)
    )
  )
  {
    let vi = !i; 
    i := vi + 1sz
  };
  let vi = !i;
  (vi = l)
}
//compareimplend$


module Vec = Pulse.Lib.Vec

fn test_compare ()
  requires emp
  ensures emp
{
    let mut a1 = [| 0; 2sz |];  // stack array, allocated using the repeat constructor

    let a2 = Vec.alloc 0 2sz;  // heap allocated array
    
    Vec.to_array_pts_to a2;  // explicit coercions from vec to array and back
    compare a1 (Vec.vec_to_array a2) 2sz;
    Vec.to_vec_pts_to a2;

    Vec.free a2  // need to free a2, a1 is automatically reclaimed when the function returns
}


// Exercise:
// Here's an F* specification of a function that sums up the elements of a sequence

let rec sum_spec (s:Seq.seq int) : Tot int (decreases Seq.length s) =
  if Seq.length s = 0
  then 0
  else let prefix = Seq.slice s 0 (Seq.length s - 1) in
       let last = Seq.index s (Seq.length s - 1) in
       sum_spec prefix + last

// Write a Pulse implementation of this function on arrays, proven to be equivalent
// to the sequence spec above

fn sum #p (#s:erased _) (arr:array int) (len:SZ.t { v len == Seq.length s })
  requires pts_to arr #p s
  returns res:int
  ensures pts_to arr #p s ** pure (res == sum_spec s)
{
  open BoundedInts;
  admit()
}

