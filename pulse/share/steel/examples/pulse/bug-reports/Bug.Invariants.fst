module Bug.Invariants
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

```pulse
atomic
fn return_atomic
      (x:ref U32.t)
requires emp ** pts_to x 1ul
returns n:U32.t
ensures emp ** pts_to x 1ul
{
    read_atomic x;
}
```

```pulse
atomic
fn return_atomic2 ()
requires emp ** pts_to x 1ul
returns n:U32.t
ensures emp ** pts_to x 1ul
{
    0ul;
}
```


```pulse
ghost
fn ghost_step ()
requires emp
ensures emp
{
    ()
}
```

assume
val atomic_step (_:unit) : stt_atomic unit emp_inames emp (fun _ -> emp)

```pulse
fn ghost_then_atomic ()
requires emp
ensures emp
{
    ghost_step();
    atomic_step();
}
```

assume
val atomic_step_res (_:unit) : stt_atomic bool emp_inames emp (fun _ -> emp)

```pulse
fn ghost_then_atomic_bool ()
requires emp
returns b:bool
ensures emp
{
    ghost_step();
    atomic_step_res();
}
```

```pulse
fn ghost_then_atomic_bool2 ()
requires emp
returns b:bool
ensures emp
{
    ghost_step();
    let b = atomic_step_res();
    ghost_step();
    b
}
```

```pulse
fn return_with_invariant
      (p:vprop)
      (i:inv p)
requires emp
returns x:bool
ensures emp
{
    with_invariants i { 
      atomic_step_res();
    }
}
```

```pulse
fn return_with_invariant2
      (x:ref U32.t)
      (i:inv (pts_to x 1ul))
requires emp
returns x:U32.t
ensures emp
{
    with_invariants i {
        read_atomic x;
    }
}
```

```pulse
fn test_invariant_annot (x:ref U32.t) (i:inv (pts_to x 0ul)) (y:ref U32.t)
requires pts_to y 'w
ensures pts_to y 0ul
{
    let n = 
        with_invariants i
        returns x:U32.t
        ensures pure (x == 0ul) ** pts_to y 'w {
            read_atomic x
        };
    y := n;
}
```
