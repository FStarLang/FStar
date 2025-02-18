module PulseTutorial.MonotonicCounterShareableFreeable
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Preorder
module MR = Pulse.Lib.MonotonicGhostRef
module B = Pulse.Lib.Box
module CI = Pulse.Lib.CancellableInvariant

assume
val incr_atomic_box (r:B.box int) (#n:erased int)
  : stt_atomic int emp_inames
        (B.pts_to r n) 
        (fun i -> B.pts_to r i ** pure (i == n + 1))

noeq
type ctr = {
    inv:     perm -> int -> slprop;
    next:    p:perm -> i:erased int -> stt int (inv p i) (fun j -> inv p j ** pure (i < j));
    share:   p:perm -> i:erased int -> stt_ghost unit emp_inames (inv p i) (fun y -> inv (p /. 2.0R) i ** inv (p /. 2.0R) i);
    gather:  p:perm -> q:perm -> i:erased int -> j:erased int -> stt_ghost unit emp_inames (inv p i ** inv q j) (fun y -> inv (p +. q) i);
    destroy: i:erased int -> stt unit (inv 1.0R i) (fun _ -> emp);
}

let next c #p #i = c.next p i
let share c #p #i = c.share p i
let destroy c #i = c.destroy i
[@@allow_ambiguous]
ghost
fn gather (c:ctr) #p #q #i #j
requires c.inv p i ** c.inv q j
ensures c.inv (p +. q) i
{
    let gather = c.gather;
    gather p q i j
}

let increases : preorder int = fun x y -> b2t (x <= y)
let mctr = MR.mref increases

let inv_core (x:B.box int) (mr:MR.mref increases)
: slprop
= exists* j. B.pts_to x j ** MR.pts_to mr #1.0R j

fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 1.0R 0
{
    open Pulse.Lib.Box;
    open CI;
    let x = alloc 0;
    let mr : MR.mref increases = MR.alloc #int #increases 0;
    MR.take_snapshot mr #1.0R 0;
    fold (inv_core x mr);
    let ii = CI.new_cancellable_invariant (inv_core x mr);

    fn next (p:perm) (i:erased int)
    requires inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii p ** MR.snapshot mr i
    returns j:int
    ensures (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii p ** MR.snapshot mr j) ** pure (i < j)
    { 
        later_credit_buy 1;
        with_invariants (iname_of ii) {
            later_elim _;
            unpack_cinv_vp ii;
            unfold inv_core;
            let res = incr_atomic_box x;
            MR.recall_snapshot mr;
            MR.update mr res;
            drop_ (MR.snapshot mr i);
            MR.take_snapshot mr #1.0R res;
            fold (inv_core);
            pack_cinv_vp ii;
            later_intro (cinv_vp ii (inv_core x mr));
            res
        }
    };

    ghost
    fn share (p:perm) (i:erased int)
    requires inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii p ** MR.snapshot mr i
    ensures (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii (p /. 2.0R) ** MR.snapshot mr i) **
            (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii (p /. 2.0R) ** MR.snapshot mr i)
    {
        MR.dup_snapshot mr;
        dup_inv (iname_of ii) _;
        CI.share ii;
    };

    ghost
    fn gather (p q:perm) (i j:erased int)
    requires (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii p ** MR.snapshot mr i) **
             (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii q ** MR.snapshot mr j)
    ensures (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii (p +. q) ** MR.snapshot mr i)
    {
        CI.gather #p #q ii;
        drop_ (MR.snapshot mr j);
        drop_ (inv (iname_of ii) (cinv_vp ii (inv_core x mr)));
    };

    fn destroy (i:erased int)
    requires inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii 1.0R ** MR.snapshot mr i
    ensures emp
    {
        later_credit_buy 1;
        CI.cancel ii;
        unfold inv_core;
        B.free x;
        drop_ (MR.pts_to mr _);
        drop_ (MR.snapshot mr _);
    };

    let c = { inv = (fun p i -> inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii p ** MR.snapshot mr i);
              next; share; gather; destroy };
            
    rewrite (inv (iname_of ii) (cinv_vp ii (inv_core x mr)) ** CI.active ii 1.0R ** MR.snapshot mr 0) as (c.inv 1.0R 0);
    c
}

fn do_something (c:ctr) #p (#i:erased int) (_:unit)
requires c.inv p i
ensures exists* j. c.inv p j
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
    share c;
    par (do_something c #_ #_) (do_something c #_ #_);
    gather c;
    destroy c
}