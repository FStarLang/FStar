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

#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection -Pulse +Pulse.Steel.Wrapper -Pulse.Steel.Wrapper.Typing'"

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
     introduce exists b vi vj vctr. (
       pts_to i full_perm vi `star`
       pts_to j full_perm vj `star`
       pts_to ctr full_perm vctr `star`     
       pure (1 <= vctr /\
             vctr <= n /\
             vi == fib (vctr - 1) /\
             vj == fib vctr /\
             b == (vctr < n))
     )
     with (vc + 1 < n)
  };
  let r = !j;
  r
}
```
