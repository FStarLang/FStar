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

module ArrayTests
#lang-pulse
open Pulse
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module US = FStar.SizeT
module R = Pulse.Lib.Reference

let some_f (x:'a) : GTot _ = ()


fn compare (#t:eqtype) (#p1 #p2:perm) (l:US.t) (#s1 #s2:elseq t l) (a1 a2:A.larray t (US.v l))
  requires (
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2
  )
  returns res:bool
  ensures (
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2 **
    (pure (res <==> Seq.equal s1 s2))
  )
{
  let mut i = 0sz;
  while (let vi = !i; if US.(vi <^ l) { let v1 = a1.(vi); let v2 = a2.(vi); (v1 = v2) } else { false } )
  invariant b. exists* (vi:US.t). ( 
    R.pts_to i vi **
    A.pts_to a1 #p1 s1 **
    A.pts_to a2 #p2 s2 **
    pure (b == (US.(vi <^ l) && Seq.index s1 (US.v vi) = Seq.index s2 (US.v vi))) **
    pure (
      US.v vi <= US.v l /\
      (forall (i:nat). i < US.v vi ==> Seq.index s1 i == Seq.index s2 i)
    )
  )
  {
    let vi = !i; 
    i := US.(vi +^ 1sz);
    ()
  };
  let vi = !i;
  let res = vi = l;
  res
}



fn fill_array (#t:Type0) (l:US.t) (a:(a:A.array t{ US.v l == A.length a })) (v:t)
              (#s:(s:Ghost.erased (Seq.seq t) { Seq.length s == US.v l }))
   requires (A.pts_to a s)
   ensures 
      exists* (s:Seq.seq t). (
         A.pts_to a s **
         pure (s `Seq.equal` Seq.create (US.v l) v)
      )
{
   let mut i = 0sz;
   while (let vi = !i; US.(vi <^ l))
   invariant exists* (s:Seq.seq t) (vi:US.t). (
      A.pts_to a s **
      R.pts_to i vi **
      pure (US.v vi <= US.v l /\
            Seq.length s == A.length a /\
            (forall (i:nat). i < US.v vi ==> Seq.index s i == v))
   )
   {
      let vi = !i; 
      a.(vi) <- v;
      i := US.(vi +^ 1sz);
      ()
   };
   ()
}



fn array_of_zeroes (n:US.t)
   returns a: V.vec U32.t
   ensures (
    V.pts_to a (Seq.create (US.v n) 0ul) **
    pure (V.length a == US.v n)
  )
{
   let a = V.alloc 0ul n;
   a
}


//this is not a recommended way to do this, since s is not erased, but it works

fn read_at_offset_0 (#t:Type0) (#p:perm) (#s:Seq.seq t) (a:array t) (i:US.t)
   requires (A.pts_to a #p s **
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a #p s **
      pure (//Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 



fn read_at_offset_poly (#t:Type0) (#p:perm) (#s:Ghost.erased (Seq.seq t)) (a:array t) (i:US.t)
   requires (A.pts_to a #p s **
             pure (US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a #p s **
      pure (US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 



fn read_at_offset (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a #p s **
             pure (US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a #p s **
      pure (US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{
   let x = a.(i);
   x
} 


assume
val test_array_access
  (#t: Type)
  (#p: perm)
  (a: A.array t)
  (i: US.t)
  (#s: Ghost.erased (Seq.seq t) {US.v i < A.length a \/ US.v i < Seq.length s})
: stt t
    (requires
      A.pts_to a #p s)
    (ensures fun res ->
      A.pts_to a #p s **
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            res == Seq.index s (US.v i)))


fn read_at_offset_refine (#p:perm) (#s:Ghost.erased (Seq.seq U32.t)) (a:array U32.t) (i:US.t) 
   requires (A.pts_to a #p s **
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:U32.t
   ensures (
      A.pts_to a #p s
     **
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 




fn read_at_offset_refine_poly (#t:Type0) (#p:perm) (#s:Ghost.erased (Seq.seq t)) (a:array t) (i:US.t) 
   requires (A.pts_to a #p s **
             pure (US.v i < A.length a \/ US.v i < Seq.length s))
   returns x:t
   ensures (
      A.pts_to a #p s
     **
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            x == Seq.index s (US.v i))
   )
{ 
   let x = test_array_access a i;
   x
} 

//Error message is correctly localizded to Seq.index in the return type
//This type is genuinely incorrect, since the return type does not assume
//the validity of the pure conjuncts in the requires
//so the sequence indexing there cannot be proven to be safe
//Maybe we should find a way to allow the pure conjuncts to be assumed in the returns
//Megan correctly remarks that this is unintuitive ... let's see if we can fix it
[@@expect_failure]

fn read_at_offset_refine_fail (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires A.pts_to a #p s
   requires pure (US.v i < A.length a)
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a #p s
   )
{ 
   let x = test_array_access a i;
   (x <: (x:U32.t { Seq.length s == A.length a /\
                    US.v i < A.length a /\
                    x == Seq.index s (US.v i)}))
} 


//But if we hoist the pure payload into a refinement, then it can be used for typing throughout the spec & body

fn read_at_offset_refine_post (a:array U32.t) (i:(i:US.t { US.v i < A.length a})) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires (A.pts_to a #p s)
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a #p s
   )
{ 
   let x = test_array_access a i;
   x
}



fn read_at_offset_refine_post2 (a:array U32.t) (i:US.t) (#p:perm) (#s:Ghost.erased (Seq.seq U32.t))
   requires A.pts_to a #p s
   requires pure (US.v i < A.length a)
   returns x: (x:U32.t { Seq.length s == A.length a /\
                         US.v i < A.length a /\
                         x == Seq.index s (US.v i)})
   ensures (
      A.pts_to a #p s
   )
{ 
   let x = test_array_access a i;
   x
} 



fn write_at_offset (#t:Type0) (a:array t) (i:US.t) (v:t)
                   (#s:(s:Ghost.erased (Seq.seq t) {US.v i < Seq.length s}))
   requires (A.pts_to a s)
   ensures (
      A.pts_to a (Seq.upd s (US.v i) v)
   )
{
   a.(i) <- v
}


noextract
let sorted (s0 s:Seq.seq U32.t) : GTot _ =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j)))

let permutation (s:Seq.seq U32.t) (l:list U32.t) =
   (forall (i:nat). i < Seq.length s ==> 
      (exists (j:nat). j < List.Tot.length l /\ U32.v (Seq.index s i) == U32.v (List.Tot.index l j)))

open FStar.UInt32
// #push-options "--query_stats"


fn sort3 (a:array U32.t)
         (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let x = a.(0sz);
   let y = a.(1sz);
   let z = a.(2sz);
   if (x >^ y) 
   {
      if (y >^ z)
      {
         a.(0sz) <- z;
         a.(1sz) <- y;
         a.(2sz) <- x;
      }
      else {
         if (x >^ z)
         {
            a.(0sz) <- y;
            a.(1sz) <- z;
            a.(2sz) <- x;
         }
         else
         {
            a.(0sz) <- y;
            a.(1sz) <- x;
            a.(2sz) <- z;
         }     
      }
   }
   else {
      if (y >^ z) {
         if (x >^ z) {
            a.(0sz) <- z;
            a.(1sz) <- x;
            a.(2sz) <- y;
         }
         else {
            a.(0sz) <- x;
            a.(1sz) <- z;
            a.(2sz) <- y;
         }
      }
      else {
         a.(0sz) <- x;
         a.(1sz) <- y;
         a.(2sz) <- z;
      }
   }
}


//Pulse does not yet implement join point inference
fn sort3_alt (a:array U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   let vz = !z;
   if (vy <^ vx) 
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   {
      y := vz;
      z := vy;
   };
   a.(0sz) <- !x;
   a.(1sz) <- !y;
   a.(2sz) <- !z;
}



fn test_local_array0 ()
  returns  b:bool
  ensures  pure (b)
{
  let mut a1 = [| 0; 2sz |];
  let v2 = V.alloc 0 2sz;
  let a2 = V.vec_to_array v2;
  V.to_array_pts_to v2;
  rewrite each V.vec_to_array v2 as a2; // BAD
  let b = compare 2sz a1 a2;
  rewrite each a2 as V.vec_to_array v2; // BAD
  V.to_vec_pts_to v2;
  V.free v2;
  b
}



fn test_local_array1 ()
  returns  i:int
  ensures  pure (i == 3)
{
  let mut a = [| 1; 2sz |];
  fill_array 2sz a 2;
  fill_array 2sz a 3;
  read_at_offset_refine_poly a 1sz
}


[@@ expect_failure]  // cannot call free on a local array

fn test_local_array2 ()
{
  let mut a = [| 1; 2sz |];
  A.free a
}


[@@ expect_failure]  // cannot return a local array

fn test_local_array3 ()
  returns  a:array int
  ensures  (
    A.pts_to a (Seq.create (US.v 2sz) 0)
  )
{
  let mut a = [| 0; 2sz |];
  a
}


[@@ expect_failure]  // immutable local arrays are not yet supported

fn test_local_array4 ()
{
  let a = [| 0; 2sz |];
  ()
}



fn test_array_swap
  (a: A.array U32.t)
  (#s: Ghost.erased (Seq.seq U32.t))
requires
  A.pts_to a s ** pure (A.length a == 2)
ensures exists* s' .
  A.pts_to a s'
{
  A.pts_to_len a;
  A.pts_to_range_intro a 1.0R s;
  A.pts_to_range_upd a 1sz 42ul;
  A.pts_to_range_upd a 1sz 42ul;
  A.pts_to_range_elim a _ _;
  ()
}

