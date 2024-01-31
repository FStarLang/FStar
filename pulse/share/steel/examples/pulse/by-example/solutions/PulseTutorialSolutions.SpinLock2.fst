module PulseTutorialSolutions.SpinLock2
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference

//lock$
let maybe (b:bool) (p:vprop) =
    if b then p else emp

let lock_inv (r:ref U32.t) (gr:GR.ref U32.t) (p:vprop) =
  exists* v perm. 
    pts_to r v **
    GR.pts_to gr #perm v **
    maybe (v = 0ul) p **
    pure (if v=0ul then perm == full_perm else perm == one_half)

noeq
type lock (p:vprop) = {
  r:ref U32.t;
  gr:GR.ref U32.t;
  i:inv (lock_inv r gr p);
}
//lock$

let locked #p (l:lock p) = GR.pts_to l.gr #one_half 1ul

```pulse
fn new_lock (p:vprop)
requires p
returns l:lock p
ensures emp
{
   let r = Box.alloc 0ul;
   let gr = GR.alloc 0ul;
   Box.to_ref_pts_to r;
   fold (maybe (0ul = 0ul) p);
   fold (lock_inv (Box.box_to_ref r) gr p);
   let i = new_invariant (lock_inv (Box.box_to_ref r) gr p);
   let l = { r = Box.box_to_ref r; gr; i };
   l
}
```


```pulse
fn rec acquire #p (l:lock p)
requires emp
ensures p ** locked l
{
  let b = 
    with_invariants l.i
    returns b:bool
    ensures maybe b (p ** locked l) 
    { 
      unfold lock_inv;
      let b = cas l.r 0ul 1ul;
      if b
      { 
        elim_cond_true _ _ _;
        with _b. rewrite (maybe _b p) as p;
        fold (maybe false p);
        rewrite (maybe false p) as (maybe (1ul = 0ul) p);
        open GR;
        l.gr := 1ul;
        GR.share l.gr;
        fold (lock_inv l.r l.gr p);
        fold (locked l);
        fold (maybe true (p ** locked l));
        true
      }
      else
      {
        elim_cond_false _ _ _;
        fold (lock_inv l.r l.gr p);
        fold (maybe false p);
        false
      }
    };
  if b { with q. rewrite (maybe b q) as q; }
  else { with q. rewrite (maybe b q) as emp; acquire l }
}
```

```pulse
fn release #p (l:lock p)
requires p ** locked l
ensures emp
{
  with_invariants l.i {
    unfold lock_inv;
    unfold locked;
    GR.gather l.gr;
    with _b _q. rewrite (maybe _b _q) as emp;
    write_atomic l.r 0ul;
    open GR;
    l.gr := 0ul;
    fold (maybe (0ul = 0ul) p);
    fold (lock_inv l.r l.gr p);
  }

}
```

```pulse
fn acquire_loop #p (l:lock p)
requires emp
ensures p ** locked l
{
  let mut acquired = false;
  fold (maybe false (p ** locked l));
  while (
    let v = !acquired;
    not v
  )
  invariant b.
    exists* v.
        pts_to acquired v **
        maybe v (p ** locked l) **
        pure (b == not v)
  {
    with _b _p. rewrite (maybe _b _p) as emp;
    let b = 
      with_invariants l.i
      returns b:bool
      ensures maybe b (p ** locked l) ** pts_to acquired false
      { 
        unfold lock_inv;
        let b = cas l.r 0ul 1ul;
        if b
        { 
            elim_cond_true _ _ _;
            with _b. rewrite (maybe _b p) as p;
            fold (maybe false p);
            rewrite (maybe false p) as (maybe (1ul = 0ul) p);
            open GR;
            l.gr := 1ul;
            GR.share l.gr;
            fold (lock_inv l.r l.gr p);
            fold (locked l);
            fold (maybe true (p ** locked l));
            true
        }
        else
        {
            elim_cond_false _ _ _;
            fold (lock_inv l.r l.gr p);
            fold (maybe false p);
            false
        }
      };
    acquired := b;
  };
  with _b _q. rewrite (maybe _b _q) as _q;
}
```
