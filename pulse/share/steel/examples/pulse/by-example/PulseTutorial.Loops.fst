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

module PulseTutorial.Loops
open Pulse.Lib.Pervasives

```pulse //count_down$
fn count_down (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    let mut keep_going = true;
    while (
        !keep_going
    )
    invariant b. 
      exists* v.
        pts_to keep_going b **
        pts_to x v **
        pure (b == false ==> v == 0)
    {
        let n = !x;
        if (n = 0) 
        {
            keep_going := false;
        } 
        else
        {
            x := n - 1;
        }
    }
}
```

```pulse //count_down2$
fn count_down2 (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        } 
        else
        {
            x := n - 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```

```pulse //count_down_loopy$
fn count_down_loopy (x:ref nat)
requires pts_to x 'v
ensures pts_to x 0
{
    while (
        let n = !x;
        if (n = 0)
        {
            false
        }
        else
        {
            x := n + 1;
            true
        }
    )
    invariant b. 
      exists* v.
        pts_to x v **
        pure (b == false ==> v == 0)
    { () }
}
```
open FStar.Mul

```pulse //multiply_by_repeated_addition$
fn multiply_by_repeated_addition (x y:nat)
    requires emp
    returns z:nat
    ensures pure (z == x * y)
{
    let mut ctr : nat = 0;
    let mut acc : nat = 0;
    while (
        let c = !ctr;
        (c < x)
    )
    invariant b.
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= x /\
              a == (c * y) /\
              b == (c < x))
    {
        let a = !acc;
        acc := a + y;
        let c = !ctr;
        ctr := c + 1;
    };
    !acc
}
```

//SNIPPET_START: sum$
let rec sum (n:nat)
: nat
= if n = 0 then 0 else n + sum (n - 1)

let rec sum_lemma (n:nat)
: Lemma (sum n == n * (n + 1) / 2)
= if n = 0 then ()
  else sum_lemma (n - 1)
//SNIPPET_END: sum$

//SNIPPET_START: isum$
#push-options "--z3cliopt 'smt.arith.nl=false'"
```pulse
fn isum (n:nat)
requires emp
returns z:nat
ensures pure ((n * (n + 1) / 2) == z)
{
    let mut acc : nat = 0;
    let mut ctr : nat = 0;
    while (
        let c = !ctr;
        (c < n)
    )
    invariant b.
    exists* c a.
        pts_to ctr c **
        pts_to acc a **
        pure (c <= n /\
              a == sum c /\
              b == (c < n))
    {
        let a = !acc;
        let c = !ctr;
        ctr := c + 1;
        acc := a + c + 1;
    };
    sum_lemma n; //call an F* lemma inside Pulse
    !acc;
}
```
#pop-options
//SNIPPET_END: isum$

//fib$
let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)
//fib$

```pulse //fib_rec$
fn rec fib_rec (n:pos) (out:ref (nat & nat))
requires
    pts_to out 'v
ensures
    exists* v.
        pts_to out v **
        pure (
          fst v == fib (n - 1) /\
          snd v == fib n 
        )
{
  if ((n = 1))
  {
    //type inference in Pulse doesn't work well here:
    //it picks (1, 1) to have type (int & int)
    //so we have to annotate
    out := ((1 <: nat), (1 <: nat)); 
  }
  else
  {
    fib_rec (n - 1) out;
    let v = !out;
    out := (snd v, fst v + snd v);
  }
}
```

```pulse //fib_loop$
fn fib_loop (k:pos)
  requires emp
  returns r:nat
  ensures pure (r == fib k)
{
  let mut i : nat = 1;
  let mut j : nat = 1;
  let mut ctr : nat = 1;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b . 
    exists* vi vj vctr. 
        pts_to i vi **
        pts_to j vj **
        pts_to ctr vctr **
        pure (
            1 <= vctr /\
            vctr <= k /\
            vi == fib (vctr - 1) /\
            vj == fib vctr /\
            b == (vctr < k)
        )
  {
      let vi = !i;
      let vj = !j;
      let c = !ctr;
      ctr := c + 1;
      i := vj;
      j := vi + vj;
  };
  !j
}
```



let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

open FStar.UInt32
open Pulse.Lib.BoundedIntegers
module U32 = FStar.UInt32


```pulse
fn fibonacci32 (k:U32.t)
  requires pure (0ul < k /\ fib (v k) < pow2 32)
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (
    let c = !ctr;
    (c < k)
  )
  invariant b . 
    exists* vi vj vctr. 
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1ul <= vctr /\
           vctr <= k /\
           fib (v (vctr - 1ul)) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  {
     let vi = !i;
     let vj = !j;
     let c = !ctr;
     fib_mono (v k) (v c + 1);
     ctr := c + 1ul;
     i := vj;
     j := vi + vj;
  };
  !j
}
```
