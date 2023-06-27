module Fibonacci
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper

let rec fib (n:nat) : nat =
  if n <= 1 then 1
  else fib (n - 1) + fib (n - 2)

let rec fib_mono (n:nat) (m:nat { m <= n})
  : Lemma
    (ensures fib m <= fib n)
  = if n = m then ()
    else fib_mono (n - 1) m

#push-options "--using_facts_from 'Prims FStar.Pervasives FStar.Ghost FStar.UInt FStar.UInt32 Fibonacci'"

```pulse
fn fibo32 (k:(n:U32.t { 0 < U32.v n  /\ fib (U32.v n) < pow2 32 }))
  requires emp
  returns r:U32.t
  ensures pure (U32.v r == fib (U32.v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (let vctr = !ctr; U32.(vctr <^ k))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1 <= U32.v vctr /\
           U32.v vctr <= U32.v k /\
           fib (U32.v vctr - 1) == U32.v vi/\
           fib (U32.v vctr) == U32.v vj /\
           b == U32.(vctr <^ k))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     ctr := U32.(vc +^ 1ul);
     i := vj;
     fib_mono (U32.v k) (U32.v vc + 1);
     j := U32.(vi +^ vj);
     ()
  };
  let r = !j;
  r
}
```


```pulse
fn fibo (n:pos)
  requires emp
  returns r:int
  ensures pure (r == fib n)
{
  let mut i = 1;
  let mut j = 1;
  let mut ctr = 1;
  while (let vctr = !ctr; (vctr < n))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr /\
           b == (vctr < n))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     i := vj;
     j := vi + vj;
     ctr := vc + 1;
     ()
  };
  let r = !j;
  r
}
```

```pulse
fn fibo2 (n:pos)
  requires emp
  returns r:nat
  ensures pure (r == fib n)
{
  let mut i = ( 1 <: nat );
  let mut j = ( 1 <: nat );
  let mut ctr = ( 1 <: pos );
  while (let vctr = !ctr; (vctr < n))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr /\
           b == (vctr < n))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     i := vj;
     j := vi + vj;
     ctr := vc + 1;
     ()
  };
  let r = !j;
  r
}
```

```pulse
fn fibo3 (n:pos)
  requires emp
  returns r: (r:nat { r == fib n })
  ensures emp
{
  let mut i = ( 1 <: nat );
  let mut j = ( 1 <: nat );
  let mut ctr = ( 1 <: pos );
  while (let vctr = !ctr; (vctr < n))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1 <= vctr /\
           vctr <= n /\
           vi == fib (vctr - 1) /\
           vj == fib vctr /\
           b == (vctr < n))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     i := vj;
     j := vi + vj;
     ctr := vc + 1;
     ()
  };
  let r = !j;
  r
}
```
