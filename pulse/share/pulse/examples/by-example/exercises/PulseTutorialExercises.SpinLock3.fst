(* This exercise revises PulseTutorial.SpinLock
   with an additional permission to track when a lock is live,
   so that it can eventually be freed. *)
module PulseTutorialExercises.SpinLock3
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference

//lock$
let maybe (b:bool) (p:vprop) =
    if b then p else emp

let lock_inv (r:ref U32.t) (live:GR.ref bool) (p:vprop) =
  exists* b. 
    GR.pts_to live #one_half b **
    maybe b (
        exists* v.
            pts_to r v **
            maybe (v = 0ul) p
    )

noeq
type lock (p:vprop) = {
  r:ref U32.t;
  live:GR.ref bool;
  i:inv (lock_inv r live p);
}

let lock_live #p (l:lock p) (#[default_arg (`full_perm)] perm:perm) =
    GR.pts_to l.live #(half_perm perm) true
//lock$

```pulse
fn new_lock ()
requires p
returns l:lock p
ensures lock_live l
{
    admit()
}
```


```pulse
fn free_lock #p (l:lock p)
requires lock_live l 
ensures emp
{
    admit()
}
```

```pulse
ghost
fn share #p #q (l:lock p)
requires lock_live l #q
ensures lock_live l #(half_perm q) ** lock_live l #(half_perm q)
{
    admit()
}
```

let sum_halves (x y:perm)
 : Lemma (ensures sum_perm (half_perm x) (half_perm y) == half_perm (sum_perm x y))
         [SMTPat (sum_perm (half_perm x) (half_perm y))]
 = let open FStar.Real in
   assert (forall (x y:FStar.Real.real). ( x /. 2.0R ) +. (y /. 2.0R) == ((x +. y) /. 2.0R))

```pulse
ghost
fn gather #p #q1 #q2 (l:lock p)
requires lock_live l #q1 ** lock_live l #q2
ensures lock_live l #(sum_perm q1 q2)
{
    admit()
}
```

```pulse
fn acquire #p #q (l:lock p)
requires lock_live l #q 
ensures p ** lock_live l #q
{
    admit()
}
```

```pulse
fn release #p #q (l:lock p)
requires p ** lock_live l #q 
ensures lock_live l #q
{
    admit()
}
```

