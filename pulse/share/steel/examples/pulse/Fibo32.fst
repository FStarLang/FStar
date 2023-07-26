module Fibo32
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

open Pulse.Class.BoundedIntegers

#push-options "--using_facts_from 'Prims FStar.Pervasives FStar.Ghost FStar.UInt FStar.UInt32 Pulse.Class.BoundedIntegers Fibo32'"
#push-options "--ide_id_info_off"
```pulse
fn fibo32 (k:U32.t) (_:squash(0ul < k /\ fits #U32.t (fib (v k))))
  requires emp
  returns r:U32.t
  ensures pure (v r == fib (v k))
{
  let mut i = 1ul;
  let mut j = 1ul;
  let mut ctr = 1ul;
  while (let vctr = !ctr; (vctr < k))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1ul <= vctr /\
           vctr <= k /\
           fib (v vctr - 1) == v vi/\
           fib (v vctr) == v vj /\
           b == (vctr < k))
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     ctr := vc + 1ul;
     i := vj;
     fib_mono (v k) (v vc + 1);
     j := vi + vj;
     ()
  };
  let r = !j;
  r
}
```
