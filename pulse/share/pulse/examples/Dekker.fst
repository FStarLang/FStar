module Dekker
#lang-pulse
open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference
module A = Pulse.Lib.Atomic
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


//The main invariant
let dekker_inv (ra rb:A.atomic_ref bool) (ga gb:GR.ref bool) (p:slprop)
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
      (ra rb:A.atomic_ref bool)
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
  A.share ra; A.share rb;
  GR.share ga; GR.share gb;
  intro_cond_false emp p;
  fold (dekker_inv ra rb ga gb p);
  new_invariant (dekker_inv ra rb ga gb p);
}

fn procA (i:iname) (ra rb:A.atomic_ref bool) (ga gb:GR.ref bool) (p:slprop)
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
  (cond b p emp)      //and if this returns true then we have the resource p 
{
  with_invariants unit emp_inames i (dekker_inv ra rb ga gb p)
    (ra |-> Frac 0.5R false ** live ga #0.5R)
    (fun _ -> ra |-> Frac 0.5R true ** ga |-> Frac 0.5R false)
  fn _ {
    unfold dekker_inv;
    A.gather ra;
    A.store ra true;   // x := true
    A.share ra;
    GR.gather ga;
    GR.share ga;
    fold (dekker_inv ra rb ga gb p);
  };
  with_invariants bool emp_inames i (dekker_inv ra rb ga gb p)
    (ra |-> Frac 0.5R true ** ga |-> Frac 0.5R false)
    (fun b -> (ra |-> Frac 0.5R true) ** (ga |-> Frac 0.5R b) **
      (cond b p emp))
  fn _ {
    unfold dekker_inv;
    A.gather ra; A.share ra;
    if (A.load rb)
    { 
      fold (dekker_inv ra rb ga gb);
      fold cond false p emp;
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
      // later_intro (dekker_inv _ _ _ _ _);
      fold cond true p emp;
      true
    }
  };
}