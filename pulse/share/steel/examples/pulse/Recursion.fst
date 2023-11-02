module Recursion

open Pulse.Lib.Pervasives

```pulse
fn rec test1
  (x:unit)
  requires emp
  ensures pure False
{
  let x = perform (fun () -> test1 ());
  ()
}
```

let _ = test1

```pulse
fn rec test2
  (y:nat)
  requires emp
  ensures emp
{
  if (y > 0) {
    perform (fun () -> test2 (y-1));
    ()
  }
}
```

```pulse
fn rec test3
  (z:nat)
  (y:nat)
  requires emp
  returns _:int
  ensures emp
{
  if (y > 0) {
    perform (fun () -> test3 (z+1) (y-1));
  } else {
    z
  }
}
```

```pulse
ghost
fn rec test_ghost_nop
  (x:unit)
  requires emp
  ensures emp
  decreases ()
{
  ()
}
```

(* Should not succeed. *)
[@@expect_failure]
```pulse
ghost
fn rec test_ghost_loop
  (x:unit)
  requires emp
  ensures emp
  decreases ()
{
  perform_ghost (fun () -> test_ghost_loop ())
}
```

```pulse
fn rec test4
  (r : ref int)
  (v : erased int)
  (y : nat)
  requires pts_to r v
  ensures pts_to r (v+y)
  decreases 1
{
  if (y > 0) {
    let w = !r;
    r := w+1;
    perform (fun () -> test4 r (v+1) (y-1));
  }
}
```

```pulse
ghost
fn rec test5
  (z:nat)
  (y:nat)
  requires emp
  ensures emp
  decreases z
{
  if (z <> 0 && y <> 0) {
    perform_ghost (fun () -> test5 (z-1) (y-1))
  }
}
```

// This should print 'Could not prove termination'
[@@expect_failure]
```pulse
ghost
fn rec test5
  (z:int)
  (y:nat)
  requires emp
  ensures emp
  decreases z
{
  if (z <> 0 && y <> 0) {
    perform_ghost (fun () -> test5 (z-1) (y-1))
  }
}
```

```pulse
fn rec test6
  (x:unit) (y:int)
  requires emp
  ensures pure False
{
  let x = perform (fun () -> test6 () (y+1));
  ()
}
```
