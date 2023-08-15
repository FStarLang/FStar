module Fibonacci
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
open Pulse.Class.BoundedIntegers
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

```pulse
fn fibo32 (k:U32.t)
  requires pure (0ul < k /\ fib (v k) < pow2 32)
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while ((ctr < k))
  invariant b . 
    exists vi vj vctr. 
     pts_to i vi **
     pts_to j vj **
     pts_to ctr vctr **
     pure (1ul <=  vctr /\
           vctr <= k /\
           fib (v vctr - 1) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  {
     let vi = i;
     ctr := ctr + 1ul;
     fib_mono (v k) (v ctr);
     i := j;
     j := vi + j;
  };
  j
}
```


// ```pulse
// fn fibo (n:pos)
//   requires emp
//   returns r:int
//   ensures pure (r == fib n)
// {
//   let mut i = 1;
//   let mut j = 1;
//   let mut ctr = 1;
//   while (let vctr = !ctr; (vctr < n))
//   invariant b . exists vi vj vctr. (
//      pts_to i vi `star`
//      pts_to j vj `star`
//      pts_to ctr vctr `star`     
//      pure (1 <= vctr /\
//            vctr <= n /\
//            vi == fib (vctr - 1) /\
//            vj == fib vctr /\
//            b == (vctr < n))
//   )
//   {
//      let vc = !ctr;
//      let vi = !i;
//      let vj = !j;
//      i := vj;
//      j := vi + vj;
//      ctr := vc + 1;
//      ()
//   };
//   let r = !j;
//   r
// }
// ```

// ```pulse
// fn fibo2 (n:pos)
//   requires emp
//   returns r:nat
//   ensures pure (r == fib n)
// {
//   let mut i = ( 1 <: nat );
//   let mut j = ( 1 <: nat );
//   let mut ctr = ( 1 <: pos );
//   while (let vctr = !ctr; (vctr < n))
//   invariant b . exists vi vj vctr. (
//      pts_to i vi `star`
//      pts_to j vj `star`
//      pts_to ctr vctr `star`     
//      pure (1 <= vctr /\
//            vctr <= n /\
//            vi == fib (vctr - 1) /\
//            vj == fib vctr /\
//            b == (vctr < n))
//   )
//   {
//      let vc = !ctr;
//      let vi = !i;
//      let vj = !j;
//      i := vj;
//      j := vi + vj;
//      ctr := vc + 1;
//      ()
//   };
//   let r = !j;
//   r
// }
// ```

// ```pulse
// fn fibo3 (n:pos)
//   requires emp
//   returns r: (r:nat { r == fib n })
//   ensures emp
// {
//   let mut i = ( 1 <: nat );
//   let mut j = ( 1 <: nat );
//   let mut ctr = ( 1 <: pos );
//   while (let vctr = !ctr; (vctr < n))
//   invariant b . exists vi vj vctr. (
//      pts_to i vi `star`
//      pts_to j vj `star`
//      pts_to ctr vctr `star`     
//      pure (1 <= vctr /\
//            vctr <= n /\
//            vi == fib (vctr - 1) /\
//            vj == fib vctr /\
//            b == (vctr < n))
//   )
//   {
//      let vc = !ctr;
//      let vi = !i;
//      let vj = !j;
//      i := vj;
//      j := vi + vj;
//      ctr := vc + 1;
//      ()
//   };
//   let r = !j;
//   r
// }
// ```
 
