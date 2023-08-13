module CustomSyntax
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"
#push-options "--ide_id_info_off"

assume val p : vprop
assume val g : unit -> stt unit emp (fun _ -> p)

let folded_pts_to (r:ref U32.t) (n:erased U32.t) : vprop = pts_to r n

```pulse
fn unfold_test (r:ref U32.t) (n:erased U32.t)
  requires folded_pts_to r n
  ensures folded_pts_to r n
{
  with n. unfold (folded_pts_to r n);
  with n. fold (folded_pts_to r n)
}
```

```pulse
fn test_write_10 (x:ref U32.t)
                 (#n:erased U32.t)
   requires pts_to x n
   ensures  pts_to x 0ul
{
    x := 1ul;
    x := 0ul;
}
```

```pulse
fn test_read (r:ref U32.t)
             (#n:erased U32.t)
             (#p:perm)
   requires pts_to r #p n
   returns x : U32.t
   ensures pts_to r #p x
{
  !r
}
```

```pulse
fn swap (r1 r2:ref U32.t)
        (#n1 #n2:erased U32.t)
  requires 
      pts_to r1 n1 **
      pts_to r2 n2
  ensures
      pts_to r1 n2 **
      pts_to r2 n1
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
       pts_to r1 n1 **
       pts_to r2 n2
   ensures
       pts_to r1 n1 **
       pts_to r2 n2
{
   swap r1 r2;
   swap r1 r2
}
```


```pulse
fn swap_with_elim_pure (r1 r2:ref U32.t) 
                       (#n1 #n2:erased U32.t)
   requires
      pts_to r1 n1 **
      pts_to r2 n2
   ensures
      pts_to r1 n2 **
      pts_to r2 n1
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
     (pts_to r  n1  **
      pure (reveal n1 == reveal n2))
   ensures 
     (pts_to r n2  **
      pure (reveal n2 == reveal n1))
{
  ()
}
```


```pulse
fn if_example (r:ref U32.t)
              (n:(n:erased U32.t{U32.v (reveal n) == 1}))
              (b:bool)
   requires 
     pts_to r n
   ensures
     pts_to r (U32.add (reveal n) 2ul)
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

```pulse
ghost
fn elim_intro_exists2 (r:ref U32.t)
   requires 
     exists n. pts_to r n
   ensures 
     exists n. pts_to r n
{
  introduce exists n. pts_to r n with _
}
```

assume
val pred (b:bool) : vprop
assume
val read_pred (_:unit) (#b:erased bool)
    : stt bool (pred b) (fun r -> pred r)

```pulse
fn while_test_alt (r:ref U32.t)
  requires 
    exists b n.
      (pts_to r n  **
       pred b)
  ensures 
    exists n. (pts_to r n  **
              pred false)
{
  while (read_pred ())
  invariant b . exists n. (pts_to r n  ** pred b)
  {
    ()
  }
}
```

```pulse
fn infer_read_ex (r:ref U32.t)
  requires
    exists n. pts_to r n
  ensures exists n. pts_to r n
{
  let x = !r;
  ()
}
```


```pulse
fn while_count2 (r:ref U32.t)
  requires exists (n:U32.t). (pts_to r n)
  ensures (pts_to r 10ul)
{
  open FStar.UInt32;
  while (let x = !r; (x <> 10ul))
  invariant b. 
    exists n. (pts_to r n  **
          pure (b == (n <> 10ul)))
  {
    let x = !r;
    if (x <^ 10ul)
    {
      r := x +^ 1ul
    }
    else
    {
      r := x -^ 1ul
    }
  }
}
```


```pulse
fn test_par (r1 r2:ref U32.t)
            (#n1 #n2:erased U32.t)
  requires 
    (pts_to r1 n1  **
     pts_to r2 n2)
  ensures
    (pts_to r1 1ul  **
     pts_to r2 1ul)
{
  parallel
  requires (pts_to r1 n1)
       and (pts_to r2 n2)
  ensures  (pts_to r1 1ul)    
       and (pts_to r2 1ul)
  {
     r1 := 1ul
  }
  {
     r2 := 1ul
  };
  ()
}
```

// A test for rewrite
let mpts_to (r:ref U32.t) (n:erased U32.t) : vprop = pts_to r n

```pulse
fn rewrite_test (r:ref U32.t)
                (#n:erased U32.t)
   requires (mpts_to r n)
   ensures  (mpts_to r 1ul)
{
  rewrite (mpts_to r n) 
       as (pts_to r n);
  r := 1ul;
  rewrite (pts_to r 1ul)
       as (mpts_to r 1ul)
}
```

```pulse
fn test_local (r:ref U32.t)
              (#n:erased U32.t)
   requires (pts_to r n)
   ensures  (pts_to r 0ul)
{
  let mut x = 0ul;
  let y = Pulse.Lib.Reference.op_Bang x;
  r := y
}
```

```pulse
fn count_local (r:ref int) (n:int)
   requires (pts_to r (hide 0))
   ensures (pts_to r n)
{
  let mut i = 0;
  while
    (let m = !i; (m <> n))
  invariant b. exists m. 
    (pts_to i m  **
     pure (b == (m <> n)))
  {
    let m = !i;
    i := m + 1
  };
  let x = !i;
  r := x
}
```


let rec sum_spec (n:nat) : nat =
  if n = 0 then 0 else n + sum_spec (n - 1)

 
let zero : nat = 0

```pulse
fn sum (r:ref nat) (n:nat)
   requires exists i. (pts_to r i)
   ensures (pts_to r (sum_spec n))
{
   let mut i = zero;
   let mut sum = zero;
   introduce exists b m s. (
     pts_to i m  **
     pts_to sum s  **
     pure (s == sum_spec m /\
           b == (m <> n)))
   with (zero <> n);
        
   while (let m = !i; (m <> n))
   invariant b . exists m s. (
     pts_to i m  **
     pts_to sum s  **
     pure (s == sum_spec m /\
           b == (m <> n)))
   {
     let m = !i;
     let s = !sum;
     i := (m + 1);
     sum := s + m + 1;
     introduce exists b m s. (
       pts_to i m  **
       pts_to sum s  **
       pure (s == sum_spec m /\
             b == (m <> n)))
     with (m + 1 <> n)
   };
   let s = !sum;
   r := s;
   introduce exists m. (pts_to i m) 
   with _;
   introduce exists s. (pts_to sum s)
   with _
}
```

```pulse
fn sum2 (r:ref nat) (n:nat)
   requires exists i. pts_to r i
   ensures pts_to r (sum_spec n)
{
   let mut i = zero;
   let mut sum = zero;
   while (let m = !i; (m <> n))
   invariant b . exists m s.
     pts_to i m  **
     pts_to sum s **
     pure (s == sum_spec m /\ b == (m <> n))
   {
     let m = !i;
     let s = !sum;
     i := (m + 1);
     sum := s + m + 1;
     ()
   };
   let s = !sum;
   r := s;
   ()
}
```

```pulse
fn if_then_else_in_specs (r:ref U32.t)
  requires `@(if true
              then pts_to r 0ul
              else pts_to r 1ul)
  ensures  `@(if true
              then pts_to r 1ul
              else pts_to r 0ul)
{
  // need this for typechecking !r on the next line,
  //   with inference of implicits
  rewrite `@(if true then pts_to r 0ul else pts_to r 1ul)
       as (pts_to r 0ul);
  let x = !r;
  r := U32.add x 1ul
}
```

```pulse
fn test_tot_let (r:ref U32.t)
  requires (pts_to r 0ul)
  ensures  (pts_to r 2ul)
{
  let x = 1ul;
  let y = 1ul;
  r := U32.add x y
}
```

// Ascriptions coming in the way
// ```pulse
// fn if_then_else_in_specs2 (r:ref U32.t) (b:bool)
//   requires (pts_to r (if b then 0ul else 1ul))
//   ensures (pts_to r (if b then 1ul else 2ul))
// {
//   let x = !r;
//   r := U32.add x 1ul
// }
// ```


```pulse
fn incr (x:nat)
  requires emp
  returns r : (r:nat { r > x })
  ensures emp
{
  let y = x + 1;
  ( y <: r:nat { r > x } )
}
```
