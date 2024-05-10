module PulseTutorial.PCMParallelIncrement
open Pulse.Lib.Pervasives
module M = FStar.Algebra.CommMonoid
module MS = Pulse.Lib.PCM.MonoidShares
module U = FStar.Universe
module GPR = Pulse.Lib.GhostPCMReference
module CI = Pulse.Lib.CancellableInvariant

(* This example illustrates the use of a custom PCM
   to reason about the "contributions" of multiple threads to
   a shared memory location. It is an adaptation of the classic
   Owicki-Gries parallel increment construction with ghost state,
   however, rather than using separate ghost variables for each thread,
   we use a ghost state construction that generalizes easily to
   an arbitrary number of threads.

   The main example at the end of the file in `incr_n r n` which
   increments the contents of r in n parallel threads.

   Intuitively, the main idea of the construction is depicted by this
   diagram:


     Concrete                 Ghost state
     memory                 ___      ___
     location:             |___|    |___|
                           |___|    |_1_|
     r -> [ v ]            |___|    |_1_|
                           |_1_|    |_1_|
                           given    to_give   

   We have two pieces of ghost state, think of each of them as a
   "tank" with a capacity of `n` units. An invariant states that
   at all times, 
   
    - the combined volume of resources in both tanks is
      "n". In the diagram, n=4

    - the value of location r is v, where v = initial + given, 
      i.e., the current value of r is the initial value plus
      the number of units of resource in the "given" tank.

   Initially, the "given" tank is empty and the to_give tank is full.

   Each thread has knowledge that the "given" tank has at least one unit of
   space remaining, a predicate called `can_give gs 1`, where `gs` is the
   ghost state. From the invariant, this implies that the "to_give" tank
   has at least one unit left. So, with this permission, a thread can "push"
   one unit of resource from the "to_give" tank into the "given" tank, while
   incrementing the reference r, and maintaining the invariant. Having done so,
   each thread gains knowledge that the "to_give" tank is at least one unit
   short of being full, a predicate called `has_given gs 1`

   At the end, we gather up the individual `has_given gs 1` permissions
   from all the threads to construct `has_given hs n`, from which, we learn that
   the "to_give" tank is empty, and so the "given" tank must be full,
   and that the value of `r` is `initial + n`.
*)

// We build the ghost state from a PCM corresponding to the 
// monoid { nat, +, 0 }
// `pcm_of n` represents a "tank" whose capacity is `n`
let pcm_of (n:nat) = MS.pcm_of MS.nat_plus_cm n

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

```pulse
ghost
fn share_gref_pts_to_unit (#n:nat) (g:gref n) (#v:nat)
requires
  gref_pts_to g v
ensures
  gref_pts_to g v **
  gref_pts_to g 0
{
  open FStar.PCM;
  unfold gref_pts_to;
  rewrite (GPR.pts_to g v)
       as (GPR.pts_to g (op (pcm_of n) v 0));
  GPR.share g v 0; //leaving the arguments (v - 1) and 1 as _ _ causes a crash
  fold (gref_pts_to g v);
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

let can_give #n (gs:ghost_state n) (k:nat) = gref_pts_to gs.given k
let has_given #n (gs:ghost_state n) (k:nat) = gref_pts_to gs.to_give k

```pulse
ghost
fn share_can_give (#n:nat) (gs:ghost_state n) (#i:nat { i > 0 })
requires can_give gs i
ensures can_give gs (i - 1) ** can_give gs 1
{
  unfold can_give;
  share_gref_pts_to gs.given;
  fold (can_give gs (i - 1));
  fold can_give;
}
```

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
    can_give gs 1 **
    CI.active p i **
    inv (CI.iref_of i) 
        (CI.cinv_vp i (contributions n initial gs r))
ensures
    has_given gs 1 **
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
    fold (has_given gs 1);
    CI.pack_cinv_vp #(contributions n initial gs r) i;
  }
}
```

```pulse
ghost
fn init_ghost_state (initial:nat) (capacity:nat) (r:ref nat)
requires pts_to r initial
returns gs:ghost_state capacity
ensures contributions capacity initial gs r **
        can_give gs capacity
{
  let given = GPR.alloc #_ #(pcm_of capacity) capacity;
  fold (gref_pts_to given capacity);
  share_gref_pts_to_unit given;

  let to_give = GPR.alloc #_ #(pcm_of capacity) capacity;
  fold (gref_pts_to to_give capacity);
  
  let gs : ghost_state capacity = { given; to_give };
  rewrite each given as gs.given;
  rewrite each to_give as gs.to_give;
  fold (can_give gs capacity);
  fold (contributions capacity initial gs r);
  gs
}
```

```pulse
ghost
fn elim_ghost_state (initial:nat) (capacity:nat) (r:ref nat) (gs:ghost_state capacity)
requires
  contributions capacity initial gs r **
  has_given gs capacity
ensures
  pts_to r (initial + capacity)
{
  unfold contributions;
  unfold has_given;
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
ghost
fn gather_has_given (#n:nat) (gs:ghost_state n) (#i #j:nat)
requires has_given gs i ** has_given gs j
ensures has_given gs (i + j)
{
  unfold has_given;
  unfold has_given;
  gather_gref_pts_to gs.to_give;
  fold (has_given gs (i + j));
}
```

#push-options "--print_implicits"
```pulse
fn incr2 (r:ref nat)
requires pts_to r 'i
ensures pts_to r ('i + 2)
{
  let gs = init_ghost_state 'i 2 r;
  let ci = CI.new_cancellable_invariant (contributions 2 'i gs r);
  share_can_give gs;
  rewrite (can_give #2 gs (2 - 1)) as (can_give #(reveal (hide 2)) gs 1);
  rewrite (can_give #2 gs 1) as (can_give #(reveal (hide 2)) gs 1);
  CI.share2 ci;
  dup_inv _ _;
  par (fun _ -> increment #'i #2 #gs r ci)
      (fun _ -> increment #'i #2 #gs r ci);
  CI.gather2 ci;
  CI.cancel ci;
  drop_ (inv _ _);
  rewrite each (reveal #nat (hide #nat 2)) as 2;
  gather_has_given gs;
  elim_ghost_state 'i _ r gs;
}
```

```pulse
ghost
fn has_given_zero 
        (#initial:erased nat)
        (#capacity:nat)
        (#gs:ghost_state capacity)
        (#p:perm)
        (r:ref nat)
        (ci:CI.cinv)
requires
    CI.active p ci **
    inv (CI.iref_of ci) 
        (CI.cinv_vp ci (contributions capacity initial gs r))
ensures
   has_given gs 0 **
   CI.active p ci **
   inv (CI.iref_of ci) 
       (CI.cinv_vp ci (contributions capacity initial gs r))
opens (add_inv emp_inames (CI.iref_of ci))
{
  with_invariants (CI.iref_of ci)
  {
    CI.unpack_cinv_vp ci;
    unfold contributions;
    share_gref_pts_to_unit gs.to_give;
    fold (has_given gs 0);
    fold (contributions capacity initial gs r);
    CI.pack_cinv_vp #(contributions capacity initial gs r) ci;
  }
}
```

```pulse
fn rec incr_n_aux
        (#initial:erased nat)
        (#capacity:erased nat)
        (#gs:ghost_state capacity)
        (#p:perm)
        (r:ref nat)
        (remaining:nat)
        (ci:CI.cinv)
requires
    can_give gs remaining **
    CI.active p ci **
    inv (CI.iref_of ci) 
        (CI.cinv_vp ci (contributions capacity initial gs r))
ensures
   has_given gs remaining **
   CI.active p ci **
   inv (CI.iref_of ci) 
       (CI.cinv_vp ci (contributions capacity initial gs r))
decreases remaining
{
  if (remaining = 0)
  {
    drop_ (can_give gs remaining);
    has_given_zero #_ #capacity r ci;
  }
  else
  {
    share_can_give gs;
    CI.share ci;
    dup_inv _ _;
    par (fun _ -> increment #_ #capacity r ci)
        (fun _ -> incr_n_aux #_ #capacity r (remaining - 1) ci);
    drop_ (inv _ _);
    CI.gather ci;
    gather_has_given gs;
    with q. rewrite (CI.active q ci) as CI.active p ci;
  }
}
```


```pulse
fn incr_n (r:ref nat) (n:nat)
requires pts_to r 'i
ensures pts_to r ('i + n)
{
  let gs = init_ghost_state 'i n r;
  let ci = CI.new_cancellable_invariant (contributions n 'i gs r);
  rewrite (can_give #n gs n) as (can_give #(reveal (hide n)) gs n);
  incr_n_aux #_ #n r n ci;
  CI.cancel ci;
  rewrite (contributions (reveal (hide n)) 'i gs r) as
          (contributions n 'i gs r);
  rewrite (has_given #(reveal (hide n)) gs n) as
          (has_given #n gs n);
  elim_ghost_state 'i _ r gs;
}
```