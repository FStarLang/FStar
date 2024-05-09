module PulseTutorial.PCMParallelIncrement
open Pulse.Lib.Pervasives
module M = FStar.Algebra.CommMonoid
module MS = Pulse.Lib.PCM.MonoidShares
module U = FStar.Universe
module CI = Pulse.Lib.CancellableInvariant

let raise_monoid (#a:Type u#a) (m:M.cm a)
: M.cm (U.raise_t u#a u#b a)
= let M.CM u op id assoc comm = m in
  M.CM (U.raise_val u) 
       (fun x y -> U.raise_val <| (U.downgrade_val x) `op` (U.downgrade_val y))
       (fun x -> id (U.downgrade_val x))
       (fun x y z -> assoc (U.downgrade_val x) (U.downgrade_val y) (U.downgrade_val z))
       (fun x y -> comm (U.downgrade_val x) (U.downgrade_val y))

let pcm_of (n:nat) = (MS.pcm_of (raise_monoid u#0 u#1 MS.nat_plus_cm) (U.raise_val n))
let elim_compatible (n:nat) (i:nat)
: Lemma
  (requires FStar.PCM.compatible (pcm_of n) (U.raise_val u#0 u#1 i) (U.raise_val u#0 u#1 n))
  (ensures i <= n)
= assert (U.downgrade_val (U.raise_val n) == n);
  assert (U.downgrade_val (U.raise_val i) == i)

let gref (n:nat) = ghost_pcm_ref (pcm_of n)

let gref_pts_to #n (g:gref n) (i:nat)
: boxable
= ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val i)

let identity_frame_compatible
      #a (p:FStar.PCM.pcm a)
      (x:a)
      (v:a{FStar.PCM.compatible p x v})
: y:a { FStar.PCM.compatible p y v /\ FStar.PCM.frame_compatible p x v y }
= x

let ghost_read_simple
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:ghost_pcm_ref p)
    (#x:erased a)
: stt_ghost (erased (v:a{FStar.PCM.compatible p x v /\ p.refine v}))
    emp_inames
    (ghost_pcm_pts_to r x)
    (fun v -> ghost_pcm_pts_to r x)
= ghost_read #a #p r x (identity_frame_compatible p x)

```pulse
ghost
fn extract_gref_bound (#n:nat) (g:gref n) (#i:erased nat)
requires
  gref_pts_to g i
ensures
  gref_pts_to g i ** pure (i <= n)
{
  unfold gref_pts_to;
  rewrite (ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val (reveal i)))
        as (ghost_pcm_pts_to #_ #(pcm_of n) g (reveal (hide (U.raise_val (reveal i)))));
  let v = ghost_read_simple #_ #(pcm_of n) g;
  rewrite (ghost_pcm_pts_to #_ #(pcm_of n) g (reveal (hide (U.raise_val (reveal i)))))
      as (ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val (reveal i)));
  assert (pure (FStar.PCM.compatible (pcm_of n) (U.raise_val (reveal i)) v));
  fold gref_pts_to;
  elim_compatible n i;
  ()
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
  rewrite (ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val (reveal i)))
        as (ghost_pcm_pts_to #_ #(pcm_of n) g (reveal (hide (U.raise_val (reveal i)))));
  rewrite (ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val (reveal j)))
        as (ghost_pcm_pts_to #_ #(pcm_of n) g (reveal (hide (U.raise_val (reveal j)))));
  ghost_gather #(U.raise_t nat) #(pcm_of n) g (hide (U.raise_val (reveal i))) (hide (U.raise_val (reveal j)));
  with v.
    rewrite (ghost_pcm_pts_to #_ #(pcm_of n) g v)
        as  (ghost_pcm_pts_to #_ #(pcm_of n) g (U.raise_val (reveal i + reveal j)));
  fold (gref_pts_to g (reveal i + reveal j));
  extract_gref_bound g;
}
```

#push-options "--print_implicits --print_universes"
```pulse
ghost
fn share_gref_pts_to (#n:nat) (g:gref n) (#v:erased nat { v > 0 })
requires
  gref_pts_to g v
ensures
  gref_pts_to g (v - 1) **
  gref_pts_to g 1
{
  open FStar.PCM;
  unfold gref_pts_to;
  rewrite (ghost_pcm_pts_to g (U.raise_val #nat v))
       as (ghost_pcm_pts_to g (op (pcm_of n) (U.raise_val (v - 1)) (U.raise_val u#0 u#1 #nat 1)));
  ghost_share g (U.raise_val (v - 1)) (U.raise_val u#0 u#1 #nat 1);
  with v.
    rewrite 
         ghost_pcm_pts_to g (reveal #(U.raise_t u#0 u#1 nat) (hide #(U.raise_t u#0 u#1 nat) v)) 
    as   ghost_pcm_pts_to g v ;
  fold gref_pts_to;
  rewrite ghost_pcm_pts_to g (reveal #(U.raise_t u#0 u#1 nat) (hide  #(U.raise_t u#0 u#1 nat) (U.raise_val 1))) 
      as  ghost_pcm_pts_to g (U.raise_val u#0 u#1 #nat 1);
  fold (gref_pts_to g 1);
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
    with t. assert (gref_pts_to gs.to_give t);
    share_gref_pts_to gs.to_give;
    atomic_incr r;
    fold (contributions n initial gs r);
    fold (has_given gs);
    CI.pack_cinv_vp #(contributions n initial gs r) i;
  }
}
```

#push-options "--print_implicits --print_universes"
```pulse
ghost
fn init_ghost_state (initial:nat) (r:ref nat)
requires pts_to r initial
returns gs:ghost_state 2
ensures contributions 2 initial gs r **
        can_give #2 gs **
        can_give #2 gs
{
  let given = ghost_alloc #_ #(pcm_of 2) (hide (U.raise_val 2));
  with _v .rewrite (ghost_pcm_pts_to given _v) as (ghost_pcm_pts_to given (U.raise_val 2));
  fold (gref_pts_to #2 given 2);
  share_gref_pts_to given;
  share_gref_pts_to given;

  let to_give = ghost_alloc #_ #(pcm_of 2) (hide (U.raise_val 2));
  with _v .rewrite (ghost_pcm_pts_to to_give _v) as (ghost_pcm_pts_to to_give (U.raise_val 2));
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

#push-options "--print_implicits"
```pulse //par$
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
  unfold (has_given #2 gs);
  unfold (has_given #2 gs);
  gather_gref_pts_to gs.to_give;
  elim_ghost_state 'i r gs;
}
```