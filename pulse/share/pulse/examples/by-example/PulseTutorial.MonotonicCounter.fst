module PulseTutorial.MonotonicCounter
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Preorder
module MR = Pulse.Lib.MonotonicGhostRef

inline_for_extraction let next_f (inv: int -> slprop) =
    i:erased int -> stt int (inv i) (fun y -> inv (i + 1) ** pure (y == reveal i))
inline_for_extraction let destroy_f (inv: int -> slprop) =
    i:erased int -> stt unit (inv i) (fun _ -> emp)
inline_for_extraction let snap_f (inv: int -> slprop) (snapshot: int -> slprop) =
    i:erased int -> stt_ghost unit emp_inames (inv i) (fun _ -> snapshot i ** inv i)
inline_for_extraction let recall_f (inv: int -> slprop) (snapshot: int -> slprop) =
    i:erased int -> j:erased int -> stt_ghost unit emp_inames (snapshot i ** inv j) (fun y -> snapshot i ** inv j ** pure (i <= j))
inline_for_extraction let dup_f (snapshot: int -> slprop) =
    i:erased int -> stt_ghost unit emp_inames (snapshot i) (fun y -> snapshot i ** snapshot i)

noeq
type ctr = {
    inv: int -> slprop;
    snapshot : int -> slprop;
    next: next_f inv;
    destroy: destroy_f inv;
    snap: snap_f inv snapshot;
    recall: recall_f inv snapshot;
    dup: dup_f snapshot;
}

let next c #i = c.next i
let destroy c #i = c.destroy i
let snap c #i = c.snap i
let recall c #i #j = c.recall i j
let dup c #i = c.dup i
let increases : preorder int = fun x y -> b2t (x <= y)
let mctr = MR.mref increases

fn new_counter ()
returns c:ctr
ensures c.inv 0
{
    open Pulse.Lib.Box;
    let x = alloc 0;
    let mr : MR.mref increases = MR.alloc #int #increases 0;
    with inv. assert pure (inv == (fun (i: int) -> pts_to x i ** MR.pts_to mr #1.0R i));
    fn next (#_:unit) : next_f inv = i {
        let j = !x;
        x := j + 1;
        MR.update mr (j + 1);
        j
    };
    fn destroy (#_:unit) : destroy_f inv = i {
       free x;
       drop_ (MR.pts_to mr _);
    };
    with snapshot. assert pure (snapshot == MR.snapshot mr);
    ghost
    fn snap (#_:unit) : snap_f inv snapshot = i {
        MR.take_snapshot mr #1.0R i;
    };
    ghost
    fn recall (#_:unit) : recall_f inv snapshot = i j {
        MR.recall_snapshot mr;
    };
    ghost
    fn dup (#_:unit) : dup_f snapshot = i {
        MR.dup_snapshot mr;
    };
    let c = { inv; snapshot; next; destroy; snap; recall; dup };
    rewrite (inv 0) as (c.inv 0);
    c
}


fn do_something (c:ctr) (#i #k:erased int)
requires c.inv i
requires c.snapshot k
ensures exists* j. c.inv j
{
  let recall = c.recall;
  recall _ _;
  drop_ (c.snapshot _);
}

fn test_counter ()
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
