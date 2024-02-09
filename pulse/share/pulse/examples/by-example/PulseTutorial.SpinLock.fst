module PulseTutorial.SpinLock
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
module U32 = FStar.UInt32

//lock$
let maybe (b:bool) (p:vprop) =
    if b then p else emp

let lock_inv (r:ref U32.t) (p:vprop) =
  exists* v. pts_to r v ** maybe (v = 0ul) p

noeq
type lock (p:vprop) = {
  r:ref U32.t;
  i:inv (lock_inv r p);
}
//lock$

```pulse //new_lock$
fn new_lock (p:vprop)
requires p
returns l:lock p
ensures emp
{
   let r = Box.alloc 0ul;
   Box.to_ref_pts_to r;
   fold (maybe (0ul = 0ul) p);
   fold (lock_inv (Box.box_to_ref r) p);
   let i = new_invariant (lock_inv (Box.box_to_ref r) p);
   let l = { r = Box.box_to_ref r; i };
   l
}
```



```pulse
//acquire_sig$
fn rec acquire #p (l:lock p)
requires emp
ensures p
//acquire_sig$
//acquire_body$
{
  let b = 
    with_invariants l.i
    returns b:bool
    ensures maybe b p 
    {
      unfold lock_inv;
      let b = cas l.r 0ul 1ul;
      if b
      { 
        elim_cond_true _ _ _;
        with _b. rewrite (maybe _b p) as p;
        fold (maybe false p);
        rewrite (maybe false p) as (maybe (1ul = 0ul) p);
        fold (lock_inv l.r p);
        fold (maybe true p);
        true
      }
      else
      {
        elim_cond_false _ _ _;
        fold (lock_inv l.r p);
        fold (maybe false p);
        false
      }
    };
  if b { rewrite (maybe b p) as p; }
  else { rewrite (maybe b p) as emp; acquire l }
}
```

```pulse //release$
fn release #p (l:lock p)
requires p
ensures emp
{
  with_invariants l.i {
    unfold lock_inv;
    write_atomic l.r 0ul;
    drop_ (maybe _ _); //double release
    fold (maybe (0ul = 0ul) p);
    fold (lock_inv l.r p);
  }
}
```

