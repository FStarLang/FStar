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
fn test_write_10 (x:ref U32.t)
                 (#n:erased U32.t)
   requires pts_to x full_perm n
   returns _ : unit
   ensures  pts_to x full_perm 0ul
{
    x := 1ul;
    x := 0ul;
}
```

```pulse
fn test_read (r:ref U32.t)
             (#n:erased U32.t)
             (#p:perm)
   requires pts_to r p n
   returns x : U32.t
   ensures pts_to r p x
{
  let x = !r;
  x
}
```

```pulse
fn swap (r1 r2:ref U32.t)
        (#n1 #n2:erased U32.t)
  requires 
     (pts_to r1 full_perm n1 `star`
      pts_to r2 full_perm n2)
  returns _ : unit
  ensures
     (pts_to r1 full_perm n2 `star`
      pts_to r2 full_perm n1)
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```


```pulse
fn call_swap2 (r1 r2:ref U32.t)
              (#n1 #n2:erased U32.t)
   requires
      (pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2)
   returns _ : unit
   ensures
      (pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2)
{
   swap r1 r2;
   swap r1 r2
}
```


```pulse
fn swap_with_elim_pure (r1 r2:ref U32.t) 
                       (#n1 #n2:erased U32.t)
   requires
     (pts_to r1 full_perm n1 `star`
      pts_to r2 full_perm n2)
   returns _ : unit
   ensures
     (pts_to r1 full_perm n2 `star`
      pts_to r2 full_perm n1)
{
   let x = !r1;
   let y = !r2;
   r1 := y;
   r2 := x
}
```

```pulse
fn intro_pure_example (r:ref U32.t)
                      (#n1 #n2:erased U32.t)
   requires 
     (pts_to r full_perm n1 `star`
      pure (eq2_prop (reveal n1) (reveal n2)))
   returns _ : unit
   ensures 
     (pts_to r full_perm n2 `star`
      pure (eq2_prop (reveal n2) (reveal n1)))
{
  ()
}
```


```pulse
fn if_example2 (r:ref U32.t)
              (n:(n:erased U32.t{eq2_prop (U32.v (reveal n)) 1}))
              (b:bool)
   requires 
     pts_to r full_perm n
   returns _ :unit
   ensures
     pts_to r full_perm (U32.add (reveal n) 2ul)
{
   let x = read_atomic r;
   if b
   {
     r := U32.add x 2ul
   }
   else
   {
     write_atomic r 3ul
   }
}
```

// open Tests.Common

// %splice_t[elim_intro_exists] (PM.check (`(
//   fun (r:ref U32.t) ->
//     (expects (exists n. pts_to r full_perm n))
//     (provides (fun _ -> exists n. pts_to r full_perm n))
//     (
//       intro (exists n. pts_to r full_perm n) _
//     )
// )))

// ```pulse
// fn elim_intro_exists2 (r:ref U32.t)
//    requires 
//      exists (n:_). pts_to r full_perm n
//    returns _ : unit
//    ensures 
//      exists (n:_). pts_to r full_perm n
// {
//   introduce exists (n:_). pts_to r full_perm n with _
// }
// ```


// // assume
// // val pred (b:bool) : vprop
// // assume
// // val read_pred (_:unit) (#b:erased bool)
// //     : stt bool (pred b) (fun r -> pred r)

// // //while syntax does not allow an st_term in the guard
// // [@@expect_failure [228]]
// // ```pulse
// // fn while_test_alt (r:ref U32.t)
// //   requires 
// //     exists (b:bool) (n:_). 
// //       (pts_to r full_perm n `star`
// //        pred b)
// //   returns _ : unit
// //   ensures 
// //     exists (n:_). (pts_to r full_perm n `star`
// //               pred false)
// // {
// //   while (let x = read_pred(); x)
// //   invariant b. exists n. (pts_to r full_perm n `star` pred b)
// //   {
// //     ()
// //   }
// // }
// // ```

// // ```pulse
// // fn infer_read_ex (r:ref U32.t)
// //   requires
// //     exists n. pts_to r full_perm n
// //   returns _ : unit
// //   ensures exists n. pts_to r full_perm n
// // {
// //   let x = !r;
// //   ()
// // }
// // ```

// // // %splice_t[intro_pure_example] (check (`(
// // //   fun (r:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
// // //     (expects (pts_to r full_perm n1 * pure (eq2_prop (reveal n1) (reveal n2))))
// // //     (provides (fun x -> pts_to r full_perm n2 * pure (eq2_prop (reveal n2) (reveal n1))))
// // //     (
// // //        ()
// // //     )
// // // )))


// // // fn fibonacci(n:nat)
// // //   requires emp
// // //   returns  _ : nat
// // //   ensures emp
// // //  {
// // //    let mut i0 = 1;
// // //    let mut i1 = 1;
// // //    let mut ctr = 1;   
// // //    while (ctr < n) 
// // //    invariant b . exists (n:pos). (pts_to ctr n * pts_to i1 (fib_spec n) * pts_to i0 (fib_spec (n - 1)))
// // //    {
// // //       let tmp = i0;
// // //       i0 := i1;
// // //       i1 := (tmp + i0);
// // //       ctr := (ctr + 1)
// // //    };
// // //    i1
// // // }
// // // ```

// // // ```pulse
// // // fn add (x y: int)
// // //   requires (pts_to x a * pts_to y b)
// // //   returns r:int
// // //   ensures (pts_to x a * pts_to y b * pure (r == a + b))
// // // {
// // //   (x + y)
// // // }
// // // ```
