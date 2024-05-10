module PulseTutorial.PCMParallelIncrement
open Pulse.Lib.Pervasives
module M = FStar.Algebra.CommMonoid
module MS = Pulse.Lib.PCM.MonoidShares
module U = FStar.Universe
module GPR = Pulse.Lib.GhostPCMReference
module CI = Pulse.Lib.CancellableInvariant

let pcm_of (n:nat) = MS.pcm_of MS.nat_plus_cm n

let elim_compatible (n:nat) (i:nat)
: Lemma
  (requires FStar.PCM.compatible (pcm_of n) i n)
  (ensures i <= n)
= ()

let gref (n:nat) = GPR.gref (pcm_of n)

let gref_pts_to #n (g:gref n) (i:nat)
: boxable
= GPR.pts_to #_ #(pcm_of n) g i


```pulse
ghost
fn extract_gref_bound (#n:nat) (g:gref n) (#i:erased nat)
requires
  gref_pts_to g i
ensures
  gref_pts_to g i ** pure (i <= n)
{
  unfold gref_pts_to;
  let v = GPR.read_simple g; 
  fold gref_pts_to;
}
```


```pulse
ghost
fn gather_gref_pts_to (#n:nat) (g:gref n) (#i #j:erased nat)
requires
  gref_pts_to g i **
  gref_pts_to g j
ensures
  gref_pts_to g (i + j) **
  pure (i <= n /\ j <= n /\ i + j <= n)
{
  extract_gref_bound g #i;
  extract_gref_bound g #j;
  unfold gref_pts_to;
  unfold gref_pts_to;
  GPR.gather g _ _;
  fold gref_pts_to;
  extract_gref_bound g;
}
```

```pulse
ghost
fn share_gref_pts_to (#n:nat) (g:gref n) (#v:nat { v > 0 })
requires
  gref_pts_to g v
ensures
  gref_pts_to g (v - 1) **
  gref_pts_to g 1
{
  open FStar.PCM;
  unfold gref_pts_to;
  rewrite (GPR.pts_to g v)
       as (GPR.pts_to g (op (pcm_of n) (v - 1) 1));
  GPR.share g (v - 1) 1; //leaving the arguments (v - 1) and 1 as _ _ causes a crash
  fold (gref_pts_to g (v - 1));
  fold gref_pts_to
}
```

[@@erasable]
noeq
type ghost_state (n:nat) = {
  given:gref n;
  to_give:gref n
} 

open Pulse.Lib
instance non_informative_gs (n:nat)
: Pulse.Lib.NonInformative.non_informative (ghost_state n)
= { reveal = (fun r -> FStar.Ghost.reveal r) <: NonInformative.revealer (ghost_state n) }

let contributions
    (n:nat)
    (initial:nat)
    (gs:ghost_state n)
    (r:ref nat)
: boxable
= exists* (v g t:nat).
    pts_to r v **
    gref_pts_to gs.given g **
    gref_pts_to gs.to_give t **
    pure (v == initial + g /\ g + t == n)

let can_give #n (gs:ghost_state n) = gref_pts_to gs.given 1
let has_given #n (gs:ghost_state n) = gref_pts_to gs.to_give 1

```pulse
atomic
fn atomic_incr (r:ref nat)
requires pts_to r 'i
ensures pts_to r ('i + 1)
{
  admit()
}
```

```pulse
// atomic
fn increment 
    (#initial:erased nat)
    (#n:erased nat)
    (#gs:ghost_state n)
    (#p:perm)
    (r:ref nat)
    (i:CI.cinv)
requires
    can_give gs **
    CI.active p i **
    inv (CI.iref_of i) 
        (CI.cinv_vp i (contributions n initial gs r))
ensures
    has_given gs **
    CI.active p i **
    inv (CI.iref_of i) 
        (CI.cinv_vp i (contributions n initial gs r))
// opens (add_inv emp_inames (CI.iref_of i))
{ 
  with_invariants (CI.iref_of i)
  {
    CI.unpack_cinv_vp i;
    unfold contributions;
    unfold can_give;
    gather_gref_pts_to gs.given;
    share_gref_pts_to gs.to_give;
    atomic_incr r;
    fold (contributions n initial gs r);
    fold (has_given gs);
    CI.pack_cinv_vp #(contributions n initial gs r) i;
  }
}
```

```pulse
ghost
fn init_ghost_state (initial:nat) (r:ref nat)
requires pts_to r initial
returns gs:ghost_state 2
ensures contributions 2 initial gs r **
        can_give #2 gs **
        can_give #2 gs
{
  let given = GPR.alloc #_ #(pcm_of 2) 2;
  fold (gref_pts_to #2 given 2);
  share_gref_pts_to given;
  share_gref_pts_to given;

  let to_give = GPR.alloc #_ #(pcm_of 2) 2;
  fold (gref_pts_to #2 to_give 2);
  
  let gs : ghost_state 2 = { given; to_give };
  rewrite each given as gs.given;
  rewrite each to_give as gs.to_give;
  fold (can_give #2 gs);
  fold (can_give #2 gs);
  fold (contributions 2 initial gs r);
  gs
}
```

```pulse
ghost
fn elim_ghost_state (initial:nat) (r:ref nat) (gs:ghost_state 2)
requires
  contributions 2 initial gs r **
  gref_pts_to gs.to_give 2
ensures
  pts_to r (initial + 2)
{
  unfold contributions;
  gather_gref_pts_to gs.to_give;
  drop_ (gref_pts_to gs.to_give _);
  drop_ (gref_pts_to gs.given _);
}
```

```pulse
fn par (#pf #pg #qf #qg:_)
       (f: unit -> stt unit pf (fun _ -> qf))
       (g: unit -> stt unit pg (fun _ -> qg))
requires pf ** pg
ensures qf ** qg
{
  parallel 
  requires pf and pg
  ensures qf and qg
  { f () }
  { g () };
  ()
}
```

```pulse
fn incr2 (r:ref nat)
requires pts_to r 'i
ensures pts_to r ('i + 2)
{
  let gs = init_ghost_state 'i r;
  let ci = CI.new_cancellable_invariant (contributions 2 'i gs r);
  rewrite (can_give #2 gs) as (can_give #(reveal (hide 2)) gs);
  rewrite (can_give #2 gs) as (can_give #(reveal (hide 2)) gs);
  CI.share2 ci;
  dup_inv _ _;
  par (fun _ -> increment #'i #2 #gs r ci)
      (fun _ -> increment #'i #2 #gs r ci);
  CI.gather2 ci;
  CI.cancel ci;
  drop_ (inv _ _);
  rewrite each (reveal #nat (hide #nat 2)) as 2;
  unfold has_given;
  unfold has_given;
  gather_gref_pts_to gs.to_give;
  elim_ghost_state 'i r gs;
}
```