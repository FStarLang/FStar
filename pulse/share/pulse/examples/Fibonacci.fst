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

module Fibonacci
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

open FStar.UInt32
open Pulse.Lib.BoundedIntegers


fn fibonacci (k:pos)
  returns r:int
  ensures pure (r == fib k)
{
  let mut i = 1;
  let mut j = 1;
  let mut ctr = 1;
  while (!ctr < k)
  invariant
    exists* (vi vj vctr : int).
    pts_to i vi **
    pts_to j vj **
    pts_to ctr vctr **
    pure (1 <= vctr /\
          vctr <= k /\
          vi == fib (vctr - 1) /\
          vj == fib vctr)
  {
      let vi = !i;
      ctr := !ctr + 1;
      i := !j;
      j := vi + !j;
  };
  !j
}


fn fibonacci32 (k:U32.t)
  requires pure (0ul < k /\ fib (v k) < pow2 32)
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (!ctr < k)
  invariant
    exists* (vi vj vctr : U32.t).
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1ul <=  vctr /\
           vctr <= k /\
           fib (v (vctr - 1ul)) == v vi/\
           fib (v vctr) == v vj)
  {
     let vi = !i;
     ctr := !ctr + 1ul;
     with vc. assert (pts_to ctr vc);
     fib_mono (v k) (v vc);
     i := !j;
     j := vi + !j;
  };
  !j
}



fn fibo (n:pos)
  returns r:int
  ensures pure (r == fib n)
{
  let mut i = 1;
  let mut j = 1;
  let mut ctr = 1;
  while (!ctr < n)
  invariant
    exists* (vi vj vctr : int). (
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr)
  )
  {
     let vi = !i;
     i := !j;
     j := vi + !j;
     ctr := !ctr + 1;
  };
  !j
}


fn fibo2 (n:pos)
  returns r:nat
  ensures pure (r == fib n)
{
  let mut i : nat = 1;
  let mut j : nat = 1;
  let mut ctr : nat = 1;
  while (!ctr < n)
  invariant exists* (vi vj vctr : nat). (
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **     
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr)
  )
  {
     let vi = !i;
     i := !j;
     j := vi + !j;
     ctr := !ctr + 1;
  };
  !j
}

fn fibo3 (n:pos)
  returns r: (r:nat { r == fib n })
{
  let mut i : nat = 1;
  let mut j : nat = 1;
  let mut ctr : nat = 1;
  while (!ctr < n)
  invariant exists* (vi vj vctr : nat). (
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **     
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr)
  )
  {
     let vi = !i;
     i := !j;
     j := vi + !j;
     ctr := !ctr + 1;
  };
  let res = !j;
  res
}