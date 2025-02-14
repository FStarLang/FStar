module PulseTutorialExercises.Basics
#lang-pulse
open Pulse.Lib.Pervasives

let fstar_five : int = 5


fn five ()
requires emp
returns n:int
ensures pure (n == 5)
{ 
  fstar_five
}



fn incr (r:ref int) (#n:erased int) // since n is purely specificational, it is erased
  requires pts_to r n
  ensures pts_to r (n + 1)
{
    let x = !r;
    r := x + 1
}



fn read (r:ref int) p (n:erased int) // any permission is ok for reading
requires pts_to r #p n
returns x:int
ensures pts_to r #p n ** pure (x == n)
{
    !r
}



fn write (r:ref int) (n:erased int) // write requires full permission
  requires pts_to r #full_perm n
  ensures pts_to r #full_perm n
{
    let y = !r;
    r := y
}


[@@ expect_failure] // fails

fn write (r:ref int) p (n:erased int)
  requires pts_to r #p n
  ensures pts_to r #p n
{
    let y = !r;
    r := y
}



fn incr2 (r1 r2:ref int)
  requires pts_to r1 'n1 ** pts_to r2 'n2
  ensures pts_to r1 ('n1 + 1) ** pts_to r2 ('n2 + 1)
{
    // pts_to r1 ‘n1 ** pts_to r2 ‘n2
    incr r1;

    // pts_to r1 (‘n1 + 1) ** pts_to r2 ‘n2
    incr r2;

    // pts_to r1 (‘n1 + 1) ** pts_to r2 (‘n2 + 1)
}



fn incr_stack ()
  requires emp
  returns x:int
  ensures pure (x == 1)
{
    let mut i = 0;
    incr i;
    !i  // explicit dereference, no need to free i, automatically reclaimed when the function returns
}


module Box = Pulse.Lib.Box

fn incr_heap ()
  requires emp
  returns x:int
  ensures pure (x == 1)
{
    let r = Box.alloc 0;
    Box.to_ref_pts_to r;  // explicit coercions from Box to ref, we plan to automate these coercions in the prover
    incr (Box.box_to_ref r);
    Box.to_box_pts_to r;
    let x = Box.(!r);
    Box.free r;  // need to free explicitly
    x
}


//Exercise 1: Fill in the spec and implementation of swap

fn swap #a (r1 r2:ref a)
requires emp
ensures emp
{
    admit()
}

