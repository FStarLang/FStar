module CustomSyntax
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper


```pulse
fn test_write_10 (x:(ref FStar.UInt32.t))
                 (n:(erased FStar.UInt32.t))
   requires (pts_to x full_perm n)
   returns _ : unit
   ensures  (pts_to x full_perm 0ul)
{
    x := 1ul;
    x := 0ul
}
```

// fn fibonacci(n:nat)
//   requires emp
//   returns  _ : nat
//   ensures emp
//  {
//    let mut i0 = 1;
//    let mut i1 = 1;
//    let mut ctr = 1;   
//    while (ctr < n) 
//    invariant b . exists (n:pos). (pts_to ctr n * pts_to i1 (fib_spec n) * pts_to i0 (fib_spec (n - 1)))
//    {
//       let tmp = i0;
//       i0 := i1;
//       i1 := (tmp + i0);
//       ctr := (ctr + 1)
//    };
//    i1
// }
// ```

// ```pulse
// fn add (x y: int)
//   requires (pts_to x a * pts_to y b)
//   returns r:int
//   ensures (pts_to x a * pts_to y b * pure (r == a + b))
// {
//   (x + y)
// }
// ```
