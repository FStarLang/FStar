module PulseTutorialSolutions.SpinLock2
#lang-pulse
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Atomic
module U32 = FStar.UInt32
module GR = Pulse.Lib.GhostReference

//lock$
let maybe (b:bool) (p:slprop) =
    if b then p else emp

let lock_inv (r:A.atomic_ref U32.t) (gr:GR.ref U32.t) (p:slprop) =
  exists* v perm. 
    (r |-> v) **
    GR.pts_to gr #perm v **
    maybe (v = 0ul) p **
    pure (if v=0ul then perm == 1.0R else perm == 0.5R)

noeq
type lock (p:slprop) = {
  r:A.atomic_ref U32.t;
  gr:GR.ref U32.t;
  i:inv (lock_inv r gr p);
}
//lock$

let locked #p (l:lock p) = GR.pts_to l.gr #one_half 1ul


fn new_lock (p:slprop)
requires p
returns l:lock p
{
   let r = A.alloc_box 0ul;
   let gr = GR.alloc 0ul;
   A.to_ref_pts_to r;
   fold (maybe (0ul = 0ul) p);
   fold (lock_inv (A.box_to_ref r) gr p);
   let i = new_invariant (lock_inv (A.box_to_ref r) gr p);
   let l = { r = A.box_to_ref r; gr; i };
   l
}




fn rec acquire #p (l:lock p)
ensures p
ensures locked l
{
  let b = 
    with_invariants l.i
    returns b:bool
    ensures maybe b (p ** locked l) 
    { 
      unfold lock_inv;
      let b = A.compare_exchange l.r 0ul 1ul;
      if b
      { 
        with _b. rewrite (maybe _b p) as p;
        fold (maybe false p);
        rewrite (maybe false p) as (maybe (1ul = 0ul) p);
        open GR;
        l.gr := 1ul;
        GR.share l.gr;
        fold (lock_inv l.r l.gr p);
        fold (locked l);
        fold (maybe true (p ** locked l));
        true
      }
      else
      {
        fold (lock_inv l.r l.gr p);
        fold (maybe false p);
        false
      }
    };
  if b { with q. rewrite (maybe b q) as q; }
  else { with q. rewrite (maybe b q) as emp; acquire l }
}



fn release #p (l:lock p)
requires p
requires locked l
{
  with_invariants l.i {
    unfold lock_inv;
    unfold locked;
    GR.gather l.gr;
    with _b _q. rewrite (maybe _b _q) as emp;
    A.store l.r 0ul;
    open GR;
    l.gr := 0ul;
    fold (maybe (0ul = 0ul) p);
    fold (lock_inv l.r l.gr p);
  }

}



fn acquire_loop #p (l:lock p)
ensures p
ensures locked l
{
  let mut acquired = false;
  fold (maybe false (p ** locked l));
  while (
    let v = !acquired;
    not v
  )
  invariant b.
    exists* v.
        pts_to acquired v **
        maybe v (p ** locked l) **
        pure (b == not v)
  {
    with _b _p. rewrite (maybe _b _p) as emp;
    let b = 
      with_invariants l.i
      returns b:bool
      ensures maybe b (p ** locked l)
      ensures pts_to acquired false
      { 
        unfold lock_inv;
        let b = A.compare_exchange l.r 0ul 1ul;
        if b
        { 
            with _b. rewrite (maybe _b p) as p;
            fold (maybe false p);
            rewrite (maybe false p) as (maybe (1ul = 0ul) p);
            open GR;
            l.gr := 1ul;
            GR.share l.gr;
            fold (lock_inv l.r l.gr p);
            fold (locked l);
            fold (maybe true (p ** locked l));
            true
        }
        else
        {
            fold (lock_inv l.r l.gr p);
            fold (maybe false p);
            false
        }
      };
    acquired := b;
  };
  with _b _q. rewrite (maybe _b _q) as _q;
}

