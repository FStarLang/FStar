module PulseTutorial.Box
open Pulse.Lib.Pervasives
open Pulse.Lib.Box

open Pulse.Lib.Box

```pulse //new_heap_ref
fn new_heap_ref (#a:Type) (v:a)
requires emp
returns r:box a
ensures pts_to r v
{
    alloc v
}
```

```pulse //swap
fn swap (#a:Type) (r0 r1:box a)
requires pts_to r0 'v0 ** pts_to r1 'v1
ensures pts_to r0 'v1 ** pts_to r1 'v0
{
    let v0 = !r0;
    let v1 = !r1;
    r0 := v1;
    r1 := v0;
}
```

```pulse //last_value_of
fn last_value_of (#a:Type) (r:box a)
requires pts_to r 'v
returns v:a
ensures emp ** pure (v == 'v)
{
    let v = !r;
    free r;
    v
}
```

```pulse //last_value_of_alt
fn last_value_of_alt (#a:Type) (r:box a)
requires pts_to r 'v
returns v:(x:a { x == 'v} )
ensures emp 
{
    let v = !r;
    free r;
    v
}
```


```pulse //copy_free_box
fn copy_free_box (#a:Type) (r:box a)
requires pts_to r 'v
returns r':box a
ensures pts_to r' 'v
{
    let v = !r;
    free r;
    alloc v
}
```


```pulse //new_heap_box_explicit_perm
fn new_heap_box_explicit_perm (#a:Type) (v:a)
requires emp
returns r:box a
ensures pts_to r #full_perm v
{
    alloc v
}
```

```pulse //share_box
fn share_box (#a:Type) (r:box a)
requires pts_to r #p 'v
ensures pts_to r #(half_perm p) 'v ** pts_to r #(half_perm p) 'v
{
    share r;
}
```

```pulse //alias_box
fn alias_box (#a:Type) (r:box a)
requires pts_to r #p 'v
returns s:box a
ensures
    pts_to r #(half_perm p) 'v **
    pts_to s #(half_perm p) 'v **
    pure (r == s)
{
    share r;
    r
}
```


```pulse //copy_box
fn copy_box (#a:Type) (r:box a)
requires pts_to r #p 'v
returns s:box a
ensures pts_to s 'v ** pts_to r #p 'v
{
    let v = !r;
    alloc v
}
```
