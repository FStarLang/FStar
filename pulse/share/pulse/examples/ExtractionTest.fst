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

module ExtractionTest
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.UInt32
module U32 = FStar.UInt32
inline_for_extraction
let zero () = 0ul



fn test_read_write (x:ref U32.t)
  requires pts_to x 'n
  ensures pts_to x 'n
{
  let n = !x;
  x := n +^ (zero());
}



[@@"inline"]

fn test_write_10 (x:ref U32.t)
   requires pts_to x 'n
   ensures  pts_to x 0ul
{
    x := 2ul;
    test_read_write x;
    x := 0ul;
}

assume val p : int -> slprop
assume val q : int -> slprop

fn test_inner_ghost_fun ()
  requires p 1
  ensures  q 1
{
  ghost
  fn aux (i:int)
    requires p i
    ensures  q i
  {
    admit()
  };
  aux 1
}

#push-options "--ext 'pulse:rvalues'"

fn write10 (x:ref U32.t)
  requires pts_to x 'n
  ensures pts_to x 0ul
{
  let mut ctr = 10ul;
  while ((ctr >^ 0ul))
  invariant b.
    exists* n i.
      pts_to x n **
      pts_to ctr i **
      pure (i <=^ 10ul /\ 
           (i <^ 10ul ==> n == 0ul) /\
           (b == (i >^ 0ul)))
  {
    test_write_10 x;
    ctr := ctr -^ 1ul;
  }
}


module SZ = FStar.SizeT
module A = Pulse.Lib.Array


fn fill_array (x:array U32.t) (n:SZ.t) (v:U32.t)
  requires pts_to x 's ** pure (A.length x == SZ.v n)
  ensures exists* s. pts_to x s ** pure (Seq.equal s (Seq.create (SZ.v n) v))
{
  A.pts_to_len x;
  let mut i : SZ.t = 0sz;
  while (SZ.(i `SZ.lt` n))
  invariant b.
    exists* (vi:SZ.t) (s:Seq.seq U32.t).
      pts_to i vi **
      pts_to x s **
      pure (SZ.(vi <=^ n) /\
            Seq.length s == Seq.length 's /\
            (forall (j:nat). j < SZ.v vi ==> Seq.index s j == v) /\
            b == SZ.(vi <^ n))
  {
    x.(i) <- v;
    i := i `SZ.add` 1sz;
  }
}


module SZ = FStar.SizeT
let test0 (x:SZ.t) (y:(y:SZ.t { SZ.v y <> 0 })) = let open SZ in x %^ y
type opt a =
  | None
  | Some : v:a -> opt a

let my_safe_add (x y : SZ.t)
  : o:opt SZ.t { Some? o ==> SZ.v (Some?.v o) == SZ.v x + SZ.v y } 
  = let open SZ in
    if x <=^ 0xffffsz
    then (
      if (y <=^ 0xffffsz -^ x)
      then Some (x +^ y)
      else None
    )
    else None
     

fn testbi (x:SZ.t) (y:(y:SZ.t { SZ.v y <> 0 }))
  requires emp
  returns z:SZ.t
  ensures emp
{
  open SZ;
  (x %^ y)
}



fn testbi2 (x:SZ.t) (y:SZ.t)
  requires emp
  returns o:opt SZ.t
  ensures emp
{
  (my_safe_add x y)
}



fn extract_match (x:opt bool)
  requires emp
  returns b:bool
  ensures emp
{
  match x {
    None ->
    {
      false
    }
    Some b ->
    {
      not b
    }
  }
}



fn rec fib (x:nat)
  requires emp
  returns y:nat
  ensures emp
{
  if (x <= 1)
  {
    1
  }
  else
  {
    let x1 = fib (x - 1);
    let x2 = fib (x - 2);
    (x1 + x2)
  }
}



fn fib2 (x:nat)
requires emp
returns y:nat
ensures emp
{
  let n = fib x;
  let m = fib (x + 1);
  (m + n)
}


type data (a b: Type0) =
  | One: a -> b -> data a b
  | Two: a -> data a b
  | Three: b -> a -> data a b
fn test_that_we_access_the_right_field_in_matches (x: data nat bool)
  requires emp
  returns y: nat
  ensures emp
{
  match x {
    One y z -> { y }
    Two y -> { y }
    Three z y -> { y }
  }
}
