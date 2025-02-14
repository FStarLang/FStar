module PulseTutorialExercies.AtomicsAndInvariants
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

let owns (x:ref U32.t) = exists* v. pts_to x v


fn create_invariant (r:ref U32.t) (v:erased U32.t)
requires pts_to r v
returns i:inv (owns r)
ensures emp
{
    fold owns;
    new_invariant (owns r)
}



atomic
fn update_ref_atomic (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
opens [i]
{
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
  }
}



ghost
fn pts_to_dup_impossible #a (x:ref a)
requires pts_to x 'v ** pts_to x 'u
ensures  pts_to x 'v ** pts_to x 'u ** pure False
{
    gather x;
    pts_to_perm_bound x;
    share x;    
}


[@@expect_failure]

fn double_open_bad (r:ref U32.t) (i:inv (owns r))
requires emp
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




fn update_ref (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
{                    
  with_invariants i {    //owns r
     unfold owns;        //ghost step;  exists* u. pts_to r u
     write_atomic r v;   //atomic step; pts_to r v
     fold owns;          //ghost step;  owns r
  }
}


[@@expect_failure]
 
fn update_ref_fail (r:ref U32.t) (i:inv (owns r)) (v:U32.t)
requires emp
ensures emp
{
  with_invariants i {
    unfold owns;
    r := v; //not atomic
    fold owns;
  }
}




let readable (r:ref U32.t) = exists* p v. pts_to r #p v

//Finish the implementation of this function
//hint: you also need to adjust the spec slightly
 //split_readable$
atomic
fn split_readable (r:ref U32.t) (i:inv (readable r))
requires emp
ensures readable r
{
  admit()
}




