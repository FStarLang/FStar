module PulseTutorial.MonotonicCounterShareable
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Preorder
module MR = Pulse.Lib.MonotonicGhostRef
module B = Pulse.Lib.Box

assume
val incr_atomic_box (r:B.box int) (#n:erased int)
  : stt_atomic int emp_inames
        (B.pts_to r n) 
        (fun i -> B.pts_to r i ** pure (i == n + 1))

noeq
type ctr = {
    inv:  int -> slprop;
    next: i:erased int -> stt int (inv i) (fun j -> inv j ** pure (i < j));
    dup:  i:erased int -> stt_ghost unit emp_inames (inv i) (fun y -> inv i ** inv i);
}

let next c #i = c.next i
let dup c #i = c.dup i
let increases : preorder int = fun x y -> b2t (x <= y)
let mctr = MR.mref increases

let inv_core (x:B.box int) (mr:MR.mref increases)
: timeless_slprop
= exists* j. B.pts_to x j ** MR.pts_to mr #1.0R j

fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 0
{
    open Pulse.Lib.Box;
    let x = alloc 0;
    let mr : MR.mref increases = MR.alloc #int #increases 0;
    MR.take_snapshot mr #1.0R 0;
    fold (inv_core x mr);
    let ii = new_invariant (inv_core x mr);
    fn next (i:erased int)
    requires inv ii (inv_core x mr) ** MR.snapshot mr i
    returns j:int
    ensures (inv ii (inv_core x mr) ** MR.snapshot mr j) ** pure (i < j)
    {
        with_invariants ii {
            later_elim_timeless _;
            unfold inv_core;
            let res = incr_atomic_box x;
            MR.recall_snapshot mr;
            MR.update mr res;
            drop_ (MR.snapshot mr i);
            MR.take_snapshot mr #1.0R res;
            fold (inv_core);
            later_intro (inv_core x mr);
            res
        }
    };
    ghost
    fn dup (i:erased int)
    requires inv ii (inv_core x mr) ** MR.snapshot mr i
    ensures (inv ii (inv_core x mr) ** MR.snapshot mr i) **
            (inv ii (inv_core x mr) ** MR.snapshot mr i)
    {
        MR.dup_snapshot mr;
        dup_inv ii _;
    };
    let c = { inv = (fun i -> inv ii (inv_core x mr) ** MR.snapshot mr i);
              next; dup };
    rewrite (inv ii (inv_core x mr) ** MR.snapshot mr 0) as (c.inv 0);
    c
}

fn do_something (c:ctr) (#i:erased int) (_:unit)
requires c.inv i
ensures exists* j. c.inv j
{ 
    let v1 = next c;
    let v2 = next c;
    assert pure (v1 < v2);
}

fn test_counter ()
requires emp
ensures emp
{
    let c = new_counter ();
    dup c;
    par (do_something c #0) (do_something c #0);
    // with j. assert (c.inv j);
    // show_proof_state;
    admit() //ambiguity with identical slprops in the context
}

let named (name:string) (p:slprop) = p

fn do_something' (name:string) (c:ctr) (#i:erased int) (_:unit)
requires c.inv i
ensures named name (exists* j. c.inv j)
{ 
    let v1 = next c;
    let v2 = next c;
    assert pure (v1 < v2);
    fold (named name (exists* j. c.inv j));
}

fn test_counter' ()
requires emp
ensures emp
{
    let c = new_counter ();
    dup c;
    par (do_something' "left" c #0) (do_something' "right" c #0);
    drop_ (named "left" _);
    drop_ (named "right" _)
}