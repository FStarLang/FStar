module Pulse.Lib.CancellableInvariant
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

[@@erasable]
let token = GR.ref bool

let maybe b v = if b then v else emp

let cancellable (t:token) (v:vprop) =
    exists* b.
        maybe b v **
        GR.pts_to t #(half_perm full_perm) b

let active (p:perm) (c:token)
  : vprop
  = GR.pts_to c #(half_perm p) true

```pulse
ghost
fn take (#p #t:_) (v:vprop)
requires
    cancellable t v **
    active p t
ensures
    v ** active p t ** active full_perm t
{
    unfold cancellable t v;
    with b. _;
    unfold active p t;
    GR.pts_to_injective_eq t;
    rewrite each b as true;
    unfold (maybe true v);
    fold (active p t);
    fold (active full_perm t);
}
```

```pulse
ghost
fn restore (#t:_) (v:vprop)
requires
    v **
    active full_perm t
ensures
    cancellable t v
{
    unfold (active full_perm t);
    fold (maybe true v);
    fold (cancellable t v);
}
```

```pulse
ghost
fn cancel (#t:_) (v:vprop)
requires
    cancellable t v **
    active full_perm t
ensures 
    cancellable t v ** v
{
    unfold cancellable t v;
    with b. _;
    unfold active full_perm t;
    GR.pts_to_injective_eq t;
    rewrite each b as true;
    unfold (maybe true v);
    GR.gather t;
    with _p _q. rewrite (GR.pts_to t #_p _q) as (GR.pts_to t _q);
    GR.( t := false );
    with  _q. rewrite (GR.pts_to t _q) as (GR.pts_to t false);
    GR.share t;
    drop_ (GR.pts_to t #(half_perm full_perm) _);
    fold (maybe false v);
    fold (cancellable t v);
}
```

```pulse
ghost
fn create (v:vprop)
requires v
returns t:token
ensures cancellable t v ** active full_perm t
{
    let t = GR.alloc true;
    fold (maybe true v);
    GR.share t;
    fold (cancellable t v);
    fold (active full_perm t);
    t
}
```

```pulse
ghost
fn create2 (v:vprop)
requires v
returns t:erased token
ensures cancellable t v ** active full_perm t
{
    let t = create v;
    rewrite each t as (reveal (hide t));
    hide t
}
```

```pulse
ghost
fn share (#p:_) (t:_)
requires
    active p t
ensures 
    active (half_perm p) t ** active (half_perm p) t
{
    unfold active p t;
    GR.share t;
    fold (active (half_perm p) t);
    fold (active (half_perm p) t);
}
```


```pulse
ghost
fn gather (#p:_) (t:_)
requires
    active (half_perm p) t **
    active (half_perm p) t
ensures active p t
{
    unfold (active (half_perm p) t);
    unfold (active (half_perm p) t);
    GR.gather t;
    with _p _v. rewrite (GR.pts_to t #_p _v) as (GR.pts_to t #(half_perm p) _v);
    fold (active p t);
}
```

 
```pulse
ghost
fn cancel_inv (#t #v:_) (i:inv (cancellable t v))
requires
    active full_perm t
ensures v
opens (add_inv emp_inames i)
{
    with_invariants i {
        cancel v;
    }
}
```
