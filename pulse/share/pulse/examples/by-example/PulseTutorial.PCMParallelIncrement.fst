module PulseTutorial.PCMParallelIncrement
#lang-pulse
open Pulse.Lib.Pervasives
module MS = Pulse.Lib.PCM.MonoidShares
module GPR = Pulse.Lib.GhostPCMReference
module CI = Pulse.Lib.CancellableInvariant
module R = Pulse.Lib.Reference

// For this example: we assume we have an atomic operation
// to increment a ref nat
// We could use a ref U32 and use Pulse.Lib.Primitives
// but that adds needless noise, unrelated to the main point
// of this example

atomic
fn atomic_incr (r:ref nat)
requires R.pts_to r 'i
ensures  R.pts_to r ('i + 1)
{
  admit()
}


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

// A tank is a ghost reference from the above PCM
let tank (n:nat) = GPR.gref (pcm_of n)

// A predicate asserting ownership of `i` units of the tank
let owns_tank_units #n ([@@@mkey] g : tank n) (i:nat)
: timeless_slprop
= GPR.pts_to #_ #(pcm_of n) g i


// You cannot own more than the tank capacity

ghost
fn extract_tank_bound (#n:nat) (g:tank n) (#i:erased nat)
requires
  owns_tank_units g i
ensures
  owns_tank_units g i ** pure (i <= n)
{
  unfold owns_tank_units;
  let v = GPR.read_simple g; 
  fold owns_tank_units;
}


// Ownership of tank units can be combined additively
[@@allow_ambiguous]

ghost
fn gather_tank_units (#n:nat) (g:tank n) (#i #j:erased nat)
requires
  owns_tank_units g i **
  owns_tank_units g j
ensures
  owns_tank_units g (i + j) **
  pure (i <= n /\ j <= n /\ i + j <= n)
{
  extract_tank_bound g #i;
  extract_tank_bound g #j;
  unfold (owns_tank_units g i);
  unfold (owns_tank_units g j);
  GPR.gather g _ _;
  fold owns_tank_units;
  extract_tank_bound g;
}


// Ownership of a unit can also split out and shared

ghost
fn share_tank_units (#n:nat) (g:tank n) (#u #v:nat)
requires
  owns_tank_units g (u + v)
ensures
  owns_tank_units g u **
  owns_tank_units g v
{
  open FStar.PCM;
  unfold owns_tank_units;
  rewrite (GPR.pts_to g (u + v))
       as (GPR.pts_to g (op (pcm_of n) u v));
  GPR.share g u v;  //leaving the arguments as _ _ causes a crash
  fold (owns_tank_units g u);
  fold (owns_tank_units g v)
}



ghost
fn share_one_tank_units (#n:nat) (g:tank n) (#u:nat { u > 0 })
requires
  owns_tank_units g u
returns k:erased nat
ensures
  owns_tank_units g (u - 1) **
  owns_tank_units g 1 **
  pure (k == u - 1)
{
  open FStar.PCM;
  unfold owns_tank_units;
  rewrite (GPR.pts_to g u)
       as (GPR.pts_to g (op (pcm_of n) (u - 1) 1));
  GPR.share g (u-1) 1;  //leaving the arguments as _ _ causes a crash
  fold (owns_tank_units g (u - 1));
  fold (owns_tank_units g 1);
  (hide #nat (u - 1))
}


// 
// ghost
// fn share_owns_tank_units_unit (#n:nat) (g:tank n) (#v:nat)
// requires
//   owns_tank_units g v
// ensures
//   owns_tank_units g v **
//   owns_tank_units g 0
// {
//   open FStar.PCM;
//   unfold owns_tank_units;
//   rewrite (GPR.pts_to g v)
//        as (GPR.pts_to g (op (pcm_of n) v 0));
//   GPR.share g v 0; //leaving the arguments (v - 1) and 1 as _ _ causes a crash
//   fold (owns_tank_units g v);
//   fold owns_tank_units
// }
// 

// The ghost state is a pair of tanks of capacity `n`
[@@erasable]
noeq
type ghost_state (n:nat) = {
  given:tank n;
  to_give:tank n
} 

instance non_informative_gs (n:nat)
: Pulse.Lib.NonInformative.non_informative (ghost_state n)
= { reveal = (fun r -> FStar.Ghost.reveal r) <: Pulse.Lib.NonInformative.revealer (ghost_state n) }

// Now for the main invariant
// The total volume of the given and to_give tanks owned by the invariant is n
// The value of r is v, and v == initial + g, the owned units in the given tank
let contributions
    (n:nat)
    (initial:nat)
    (gs:ghost_state n)
    (r:ref nat)
: timeless_slprop
= exists* (v g t:nat).
    pts_to r v **    
    owns_tank_units gs.given g **
    owns_tank_units gs.to_give t **
    pure (v == initial + g /\ g + t == n)


ghost
fn fold_contribs 
    (n:nat)
    (initial:nat)
    (gs:ghost_state n)
    (r:ref nat)
    (v g t:nat)
requires
    pts_to r v **    
    owns_tank_units gs.given g **
    owns_tank_units gs.to_give t **
    pure (v == initial + g /\ g + t == n)
ensures
    contributions n initial gs r
{
  fold (contributions n initial gs r)
}



// can_give gs k: Knowledge that the given tank has at least `k` units
// remaining to be filled
let can_give #n (gs:ghost_state n) (k:nat) = owns_tank_units gs.given k


// has_given gs k: Knowledge that the to_give tank is at least `k` units
// from being full
let has_given #n (gs:ghost_state n) (k:nat) = owns_tank_units gs.to_give k

// A utility to share out can_give units

ghost
fn share_can_give (#n:nat) (gs:ghost_state n) (#i:nat { i > 0 })
requires can_give gs i
ensures can_give gs (i - 1) ** can_give gs 1
{
  unfold can_give;
  share_tank_units gs.given #(i - 1) #1;
  fold (can_give gs (i - 1));
  fold can_give;
}


// A utility to gather has_given units
[@@allow_ambiguous]

ghost
fn gather_has_given (#n:nat) (gs:ghost_state n) (#i #j:nat)
requires has_given gs i ** has_given gs j
ensures has_given gs (i + j)
{
  unfold (has_given gs i);
  unfold (has_given gs j);
  gather_tank_units gs.to_give;
  fold (has_given gs (i + j));
}



// Initializing the ghost state and building the invariant

ghost
fn init_ghost_state (initial:nat) (capacity:nat) (r:ref nat)
requires pts_to r initial
returns gs:ghost_state capacity
ensures contributions capacity initial gs r **
        can_give gs capacity 
{
  let given = GPR.alloc #_ #(pcm_of capacity) capacity;
  fold (owns_tank_units given capacity);
  share_tank_units given #capacity #0;

  let to_give = GPR.alloc #_ #(pcm_of capacity) capacity;
  fold (owns_tank_units to_give capacity);
  
  let gs : ghost_state capacity = { given; to_give };
  rewrite each given as gs.given;
  rewrite each to_give as gs.to_give;
  fold (can_give gs capacity);
  fold (contributions capacity initial gs r);
  gs
}


// Tearing down the ghost state and recovering the main postcondition

ghost
fn elim_ghost_state (initial:nat) (capacity:nat) (r:ref nat) (gs:ghost_state capacity)
requires
  contributions capacity initial gs r **
  has_given gs capacity
ensures
  R.pts_to r (initial + capacity)
{
  unfold contributions;
  unfold has_given;
  gather_tank_units gs.to_give;
  drop_ (owns_tank_units gs.to_give _);
  drop_ (owns_tank_units gs.given _);
}


// The core function to increment a reference

atomic
fn incr_core
    (#n:erased nat)
    (#initial:erased nat)
    (gs:ghost_state n)
    (r:ref nat)
requires
    can_give gs 1 **     //we have permission to add one to the reference
    contributions n initial gs r
ensures
    has_given gs 1 **    //we have contributed 1 unit to the reference
    contributions n initial gs r
{
   unfold contributions;
   unfold can_give;  gather_tank_units gs.given;
   atomic_incr r;
   let remaining = share_one_tank_units gs.to_give; fold (has_given gs 1);
   fold (contributions n initial gs r)
}


// The core function to increment a reference

atomic
fn increment 
    (#n:erased nat)
    (#initial:erased nat)
    (#gs:ghost_state n)
    (#p:perm)
    (r:ref nat)
    (i:CI.cinv)
requires
    can_give gs 1 **     //we have permission to add one to the reference
    CI.active i p **     //the invariant is active
    later_credit 1 **    // we can open one invariant
    inv (CI.iname_of i)   //the invariant itself
        (CI.cinv_vp i (contributions n initial gs r))
ensures
    has_given gs 1 **    //we have contributed 1 unit to the reference
    CI.active i p **     //and the invariant remains ...
    inv (CI.iname_of i) 
        (CI.cinv_vp i (contributions n initial gs r))
opens [CI.iname_of i] //we used the invariant
{ 
  with_invariants (CI.iname_of i)
  {
    later_elim _;
    CI.unpack_cinv_vp i;
    incr_core gs r;
    CI.pack_cinv_vp i;
    later_intro (CI.cinv_vp i (contributions n initial gs r));
  }
}



// First, a simple variant to increment a reference in parallel in two threads,
// the classic Owicki-Gries example

fn incr2 (r:ref nat)
requires R.pts_to r 'i
ensures  R.pts_to r ('i + 2)
{
  let gs = init_ghost_state 'i 2 r; // initialize the ghost state with a capacity of 2
  let ci = CI.new_cancellable_invariant (contributions 2 'i gs r); // allocate an invariant
  share_can_give gs; // split permission to can_give for use in two threads
  //These next two rewrites are ugly!
  rewrite (can_give #2 gs (2 - 1)) as (can_give #(reveal (hide 2)) gs 1);
  rewrite (can_give #2 gs 1) as (can_give #(reveal (hide 2)) gs 1);
  // share permission to the invariant for use in two threads
  CI.share ci;
  // and duplicate the invariant itself
  dup_inv _ _;
  // Now, spawn two threads in which to run increment
  // Note: the code on the two sides is identical! Unlike
  // in classic variants of this example, where you have to run
  // different ghost steps to account for contributions in each thread
  later_credit_buy 1;
  later_credit_buy 1;
  par_atomic
    (fun _ -> increment #2 r ci)
    (fun _ -> increment #2 r ci);
  later_credit_buy 1;
  CI.gather ci; CI.cancel ci; // Collect back permission to the invariant and then cancel it
  drop_ (inv _ _); //drop the other copy of the invariant; it is now useless
  // collect up the has_given predicates from each thread
  gather_has_given gs;
  // recover the postcondition by the main ghost state eliminator lemma
  elim_ghost_state _ _ _ gs;
}


// We can now generalize this to an arbitrary number of threads


// We first need an auxilary function that allows us to take
// ownership of 0 units of the has_given tank from the invariant

ghost
fn has_given_zero 
        (#initial:erased nat)
        (#capacity:nat)
        (#gs:ghost_state capacity)
        (#p:perm)
        (r:ref nat)
        (ci:CI.cinv)
requires
    CI.active ci p **
    later_credit 1 **
    inv (CI.iname_of ci) 
        (CI.cinv_vp ci (contributions capacity initial gs r))
ensures
   has_given gs 0 **
   CI.active ci p **
   inv (CI.iname_of ci) 
       (CI.cinv_vp ci (contributions capacity initial gs r))
opens [CI.iname_of ci]
{
  with_invariants (CI.iname_of ci)
  {
    later_elim _;
    CI.unpack_cinv_vp ci;
    unfold contributions;
    with u. assert (owns_tank_units gs.to_give u);
    share_tank_units gs.to_give #u #0;
    fold (has_given gs 0);
    fold (contributions capacity initial gs r);
    CI.pack_cinv_vp #(contributions capacity initial gs r) ci;
    later_intro (CI.cinv_vp ci (contributions capacity initial gs r));
  }
}



// Now, we can recursively spawn `n` threads to increment `r`

fn rec incr_n_aux
        (#capacity:erased nat)
        (#initial:erased nat)
        (#gs:ghost_state capacity)
        (#p:perm)
        (r:ref nat)
        (remaining:nat)
        (ci:CI.cinv)
requires
    can_give gs remaining ** // if we have permission to add remaining to r
    CI.active ci p **        // and the invariant ...
    inv (CI.iname_of ci) 
        (CI.cinv_vp ci (contributions capacity initial gs r))
ensures
   has_given gs remaining ** // we have added remaining to r
   CI.active ci p **         // and retain the invariant ... 
   inv (CI.iname_of ci) 
       (CI.cinv_vp ci (contributions capacity initial gs r))
decreases remaining
{
  if (remaining = 0)
  { //we're done; just take out has_given 0 from the invariant
    drop_ (can_give gs remaining);
    later_credit_buy 1;
    has_given_zero #_ #capacity r ci;
  }
  else
  {
    share_can_give gs;
    CI.share ci;
    dup_inv _ _;
    later_credit_buy 1;
    par_atomic_l
      (fun _ -> increment #capacity r ci) //call increment in one thread
      (fun _ -> incr_n_aux #capacity r (remaining - 1) ci); //recursively call to spawn more
    drop_ (inv _ _);
    CI.gather ci;
    gather_has_given gs;
  }
}


/// Finally, the main `incr_n r n`

fn incr_n (r:ref nat) (n:nat)
requires R.pts_to r 'i
ensures  R.pts_to r ('i + n)
{
  let gs = init_ghost_state 'i n r;
  let ci = CI.new_cancellable_invariant (contributions n 'i gs r);
  incr_n_aux #n r n ci;
  later_credit_buy 1;
  CI.cancel ci;
  elim_ghost_state _ _ _ gs; //elim_ghost_state 'i _ r gs;
}

