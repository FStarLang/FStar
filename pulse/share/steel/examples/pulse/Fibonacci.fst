module Fibonacci
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper

let rec fib' (n:nat) =
  if n <= 1 then 1
  else fib' (n - 1) + fib' (n - 2)

assume
val fib (n:nat) :  nat

assume
val fib_eq (n:nat)
  : Lemma
    (ensures fib n == fib' n)
    [SMTPat (fib n)]


//#push-options "--admit_smt_queries true"

[@@expect_failure]
```pulse
fn fibo (n:nat)
  requires emp
  returns r: nat
  ensures emp
{
  let mut i = 1;
  let mut j = 1;
  let mut ctr = 1;
  while (let vctr = !ctr; (vctr < n))
  invariant b . exists vi vj vctr. (
     pts_to i full_perm vi `star`
     pts_to j full_perm vj `star`
     pts_to ctr full_perm vctr `star`     
     pure (1 <= vctr /\ vctr <= n /\ (not b ==> vctr == n) /\
           vi == fib (vctr - 1) /\
           vj == fib vctr)
  )
  {
     let vc = !ctr;
     let vi = !i;
     let vj = !j;
     i := vj;
     j := vi + vj;
     ctr := vc + 1;
  };
  ()
}
```

//   while (let vctr = !ctr; (vctr < n))
//   invariant b . exists vi vj vctr. (
//      pts_to i full_perm vi `star`
//      pts_to j full_perm vj `star`
//      pts_to ctr full_perm vctr `star`     
//      pure (1 <= vctr /\ vctr <= n /\ (not b ==> vctr == n) /\
//            vi == fib (vctr - 1) /\
//            vj == fib vctr)
//   )
//   {
//      let tmp = !vi;
//      vi := !vj;
//      vj = !vj + tmp;
//   };
//   let res = !vj;
//   res
// }
// ```


