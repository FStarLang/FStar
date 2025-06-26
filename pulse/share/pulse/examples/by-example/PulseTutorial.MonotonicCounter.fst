module PulseTutorial.MonotonicCounter
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Preorder
module MR = Pulse.Lib.MonotonicGhostRef
noeq
type ctr = {
    inv: int -> slprop;
    snapshot : int -> slprop;
    next:    i:erased int -> stt int (inv i) (fun y -> inv (i + 1) ** pure (y == reveal i));
    destroy: i:erased int -> stt unit (inv i) (fun _ -> emp);
    snap:    i:erased int -> stt_ghost unit emp_inames (inv i) (fun _ -> snapshot i ** inv i);
    recall:  i:erased int -> j:erased int -> stt_ghost unit emp_inames (snapshot i ** inv j) (fun y -> snapshot i ** inv j ** pure (i <= j));
    dup:     i:erased int -> stt_ghost unit emp_inames (snapshot i) (fun y -> snapshot i ** snapshot i);
}

let next c #i = c.next i
let destroy c #i = c.destroy i
let snap c #i = c.snap i
let recall c #i #j = c.recall i j
let dup c #i = c.dup i
let increases : preorder int = fun x y -> b2t (x <= y)
let mctr = MR.mref increases

fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 0
{
    open Pulse.Lib.Box;
    let x = alloc 0;
    let mr : MR.mref increases = MR.alloc #int #increases 0;
    fn next (i:erased int)
    requires pts_to x i ** MR.pts_to mr #1.0R i
    returns j:int
    ensures (pts_to x (i + 1) ** MR.pts_to mr #1.0R (i + 1)) ** pure (j == reveal i)
    {
        let j = !x;
        x := j + 1;
        MR.update mr (j + 1);
        j
    };
    fn destroy (i:erased int)
    requires pts_to x i ** MR.pts_to mr #1.0R i
    ensures emp
    {
       free x;
       drop_ (MR.pts_to mr _);
    };
    ghost
    fn snap (i:erased int)
    requires pts_to x i ** MR.pts_to mr #1.0R i
    ensures  MR.snapshot mr i ** (pts_to x i ** MR.pts_to mr #1.0R i)
    {
        MR.take_snapshot mr #1.0R i;
    };
    ghost
    fn recall (i:erased int) (j:erased int)
    requires  MR.snapshot mr i ** (pts_to x j ** MR.pts_to mr #1.0R j)
    ensures  MR.snapshot mr i ** (pts_to x j ** MR.pts_to mr #1.0R j) ** pure (i <= j)
    {
        MR.recall_snapshot mr;
    };
    ghost
    fn dup (i:erased int)
    requires MR.snapshot mr i
    ensures MR.snapshot mr i ** MR.snapshot mr i
    {
        MR.dup_snapshot mr;
    };
    let c = { 
        inv = (fun i -> pts_to x i ** MR.pts_to mr #1.0R i);
        snapshot = MR.snapshot mr;
        next;
        destroy;
        snap;
        recall;
        dup 
    };
    rewrite (pts_to x 0 ** MR.pts_to mr #1.0R 0) as (c.inv 0);
    c
}


fn do_something (c:ctr) (#i #k:erased int)
requires c.inv i ** c.snapshot k
ensures exists* j. c.inv j
{
  let recall = c.recall;
  recall _ _;
  drop_ (c.snapshot _);
}

fn test_counter ()
requires emp
ensures emp
{
    let c = new_counter ();
    snap c;
    assert (c.snapshot 0);
    let x = next c;
    assert pure (x == 0);
    let x = next c;
    assert pure (x == 1);
    dup c;
    do_something c;
    recall c;
    let z = next c;
    assert pure (z >= 0);
    destroy c;
    drop_ (c.snapshot _);
    assert pure (z >= 0);
}
