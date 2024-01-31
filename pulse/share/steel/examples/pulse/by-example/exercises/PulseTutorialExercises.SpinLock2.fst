(* This exercise revises PulseTutorial.SpinLock
   with an additional permission to track when a lock is taken,
   ensuring that a lock cannot be double-released *)
module PulseTutorialExercises.SpinLock2
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
  admit()
}
```


```pulse
fn rec acquire #p (l:lock p)
requires emp
ensures p ** locked l
{
  admit()
}
```

```pulse
fn release #p (l:lock p)
requires p ** locked l
ensures emp
{
  admit()
}
```
