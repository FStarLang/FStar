module Dekker
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference
open Pulse.Class.PtsTo

(* Dekker's algorithm for mutual exclusion relies on sequential consistency

a := 0; b := 0;
par 
(  
  atomic_write a 1;
  if atomic_read b = 0
  then /* critical section */
)
(  
  atomic_write b 1;
  if atomic_read a = 0
  then /* critical section */
)

This is provable in Pulse with an invariant & ghost state
*)


// Some primitives for atomic read and write
atomic
fn read_atomic (r:R.ref bool) (#p:perm) (#v:erased bool)
requires
  r |-> Frac p v
returns b:bool
ensures
  r |-> Frac p v
ensures
  pure (b == reveal v)
{admit()}

atomic
fn write_atomic (r:R.ref bool) (b:bool)
requires
  exists* v. r |-> v
ensures
  r |-> b
{ admit() }

//The main invariant
let dekker_inv (ra rb:R.ref bool) (ga gb:GR.ref bool) (p:slprop)
: slprop
= exists* (va vb ua ub:bool).
    (ra |-> Frac 0.5R va) **
    (rb |-> Frac 0.5R vb) **
    (ga |-> Frac 0.5R ua) **
    (gb |-> Frac 0.5R ub) **
    cond (ua || ub) emp p ** //if both ghost variables are false, then p is available
    pure ( //ghost vars are false if their concrete counterparts are
      (va=false ==> ua=false) /\ 
      (vb=false ==> ub=false)
    )

ghost
fn init_dekker_inv 
      (ra rb:R.ref bool)
      (ga gb:GR.ref bool)
      (p:slprop)
requires
    (ra |-> false) **
    (rb |-> false) **
    (ga |-> false) **
    (gb |-> false) ** 
    p
returns i:iname
ensures
  inv i (dekker_inv ra rb ga gb p)  
ensures 
  (ra |-> Frac 0.5R false) **
  (rb |-> Frac 0.5R false) **
  (ga |-> Frac 0.5R false) **
  (gb |-> Frac 0.5R false)
{
  R.share ra; R.share rb;
  GR.share ga; GR.share gb;
  intro_cond_false emp p;
  fold (dekker_inv ra rb ga gb p);
  new_invariant (dekker_inv ra rb ga gb p);
}

fn procA (i:iname) (ra rb:R.ref bool) (ga gb:GR.ref bool) (p:slprop)
preserves 
  inv i (dekker_inv ra rb ga gb p) //with the invariant
requires
  (ra |-> Frac 0.5R false) **        //if a is initially false
  (exists* (ua:bool). ga |-> Frac 0.5R ua)  //and with ga
returns b:bool
ensures
  (ra |-> Frac 0.5R true) **  //a is true
  (ga |-> Frac 0.5R b)        //g is set to the return value
ensures
  (if b then p else emp)      //and if this returns true then we have the resource p 
{
  later_credit_buy 1;
  with_invariants i
  returns _:unit
  ensures
    later (dekker_inv ra rb ga gb p) **
    (ra |-> Frac 0.5R true) **
    (ga |-> Frac 0.5R false)
  {
    later_elim _;
    unfold dekker_inv;
    R.gather ra;
    write_atomic ra true;   // x := true
    R.share ra;
    GR.gather ga;
    GR.share ga;
    fold (dekker_inv ra rb ga gb p);
    later_intro (dekker_inv ra rb ga gb p);
  };
  later_credit_buy 1;
  with_invariants i
  {
    later_elim _;
    unfold dekker_inv;
    R.gather ra; R.share ra;
    if (read_atomic rb)
    { 
      fold (dekker_inv ra rb ga gb);
      later_intro (dekker_inv _ _ _ _ _);
      false
    }
    else
    {
      GR.gather ga;
      elim_cond_false _ _ _;
      GR.write ga true;
      GR.share ga;
      intro_cond_true emp p;
      fold (dekker_inv ra rb ga gb p);
      later_intro (dekker_inv _ _ _ _ _);
      true
    }
  };
}