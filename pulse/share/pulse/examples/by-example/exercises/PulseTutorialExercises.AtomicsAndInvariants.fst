module PulseTutorialExercies.AtomicsAndInvariants
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Atomic

let owns (x:A.atomic_ref U32.t) = exists* v. x |-> v


fn create_invariant (r:A.atomic_ref U32.t) (v:erased U32.t)
requires r |-> v
returns i:inv (owns r)
{
    fold owns;
    new_invariant (owns r)
}



atomic
fn update_ref_atomic (r:A.atomic_ref U32.t) (i:inv (owns r)) (v:U32.t)
opens [i]
{
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. r |-> u
     A.store r v;        //atomic step; r |-> v
     fold owns;          //ghost step;  owns r
  }
}



ghost
fn pts_to_dup_impossible (#a: Type0) (x:A.atomic_ref a)
preserves x |-> 'v
preserves x |-> 'u
ensures pure False
{
    A.gather x;
    A.pts_to_perm_bound x;
    A.share x;    
}


[@@expect_failure]

fn double_open_bad (r:A.atomic_ref U32.t) (i:inv (owns r))
ensures pure False
{
    with_invariants i {
      with_invariants i {
        unfold owns;
        unfold owns;
        pts_to_dup_impossible r;
        fold owns;
        fold owns
      }
    }
}




fn update_ref (r:A.atomic_ref U32.t) (i:inv (owns r)) (v:U32.t)
{                    
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. r |-> u
     A.store r v;        //atomic step; r |-> v
     fold owns;          //ghost step;  owns r
  }
}


[@@expect_failure]
 
fn update_ref_fail (r:A.atomic_ref U32.t) (i:inv (owns r)) (v:U32.t)
{
  with_invariants i {
    unfold owns;
    A.store r 0ul;
    A.store r v; //two atomic steps are not atomic
    fold owns;
  }
}




let readable (r:A.atomic_ref U32.t) = exists* p v. r |-> Frac p v

//Finish the implementation of this function
//hint: you also need to adjust the spec slightly
 //split_readable$
atomic
fn split_readable (r:A.atomic_ref U32.t) (i:inv (readable r))
ensures readable r
{
  admit()
}




