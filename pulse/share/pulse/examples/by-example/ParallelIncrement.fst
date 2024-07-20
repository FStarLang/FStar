(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module ParallelIncrement
#lang-pulse
open Pulse.Lib.Pervasives

module U32 = FStar.UInt32
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference
module R = Pulse.Lib.Reference


fn increment (#p:perm)
             (x:ref nat)
             (l:L.lock)
requires (L.lock_alive l #p (exists* v. pts_to x #0.5R v)) ** pts_to x #0.5R 'i
ensures (L.lock_alive l #p (exists* v. pts_to x #0.5R v)) ** pts_to x #0.5R ('i + 1)
 {
    let v = !x;
    L.acquire l;
    R.gather x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x _v);
    x := (v + 1);
    R.share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #0.5R _v);
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #0.5R _v);
}


#push-options "--print_implicits --ext 'pulse:env_on_err' --print_full_names"

fn increment_f (x: ref nat)
               (#p:perm)
               (#pred #qpred: nat -> slprop)
               (l:L.lock)
               (f: (v:nat -> stt_ghost unit
                        emp_inames
                        (pred v ** qpred v ** pts_to x #0.5R (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (v + 1) ** pts_to x #0.5R (v + 1))))
requires L.lock_alive l #p (exists* v. pts_to x #0.5R v ** pred v) ** pts_to x #0.5R 'i ** qpred 'i
ensures L.lock_alive l #p (exists* v. pts_to x #0.5R v ** pred v) ** pts_to x #0.5R ('i + 1) ** qpred ('i + 1)
 {
    let vx = !x;
    rewrite (qpred 'i) as (qpred vx);
    L.acquire l;
    R.gather x;
    with p v. rewrite (pts_to x #p v) as (pts_to x v);
    x := (vx + 1);
    R.share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #0.5R _v);
    with _v. rewrite (pred _v) as (pred vx);
    f vx;
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #0.5R _v);
    rewrite (qpred (vx + 1)) as (qpred ('i + 1));
}



fn increment_f2 (x: ref int)
                (#p:perm)
                (#pred #qpred: int -> slprop)
                (l:L.lock)
                (f: (v:int -> vq:int -> stt_ghost unit
                        emp_inames
                        (pred v ** qpred vq ** pts_to x (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires L.lock_alive l #p (exists* v. pts_to x v ** pred v) ** qpred 'i
ensures L.lock_alive l #p (exists* v. pts_to x v ** pred v) ** qpred ('i + 1)
 {
    L.acquire l;
    let vx = !x;
    with _v. rewrite (pred _v) as (pred vx);
    x := vx + 1;
    f vx 'i;
    L.release l;
}


#push-options "--warn_error -249"

fn parallel_increment
        (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc #int 0;
    let right = GR.alloc #int 0;
    GR.share left;
    GR.share right;
    let lock = L.new_lock (
      exists* (v:int).
        pts_to x v **
        (exists* (vl vr:int).
          GR.pts_to left #0.5R vl **
          GR.pts_to right #0.5R vr **
          pure (v == 'i + vl + vr))
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        (exists* (vl vr:int).
            GR.pts_to left #0.5R vl **
            GR.pts_to right #0.5R vr **
            pure (v == 'i + vl + vr)) **
        GR.pts_to lr #0.5R vq **
        pts_to x (v + 1)
      ensures
        (exists* (vl vr:int).
            GR.pts_to left #0.5R vl **
            GR.pts_to right #0.5R vr **
            pure (v + 1 == 'i + vl + vr)) **
        GR.pts_to lr #0.5R (vq + 1) **
        pts_to x (v + 1)
    { 
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
        GR.( left := vq + 1 );
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
        GR.( right := vq + 1 );
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
      }
    };

    with pred. assert (L.lock_alive lock #1.0R (exists* v. pts_to x v ** pred v));
    L.share2 lock;
    parallel
    requires GR.pts_to left #0.5R 0 **
             L.lock_alive lock #0.5R (exists* v. pts_to x v ** pred v)
         and GR.pts_to right #0.5R 0 **
             L.lock_alive lock #0.5R (exists* v. pts_to x v ** pred v)
    ensures  GR.pts_to left #0.5R 1 **
             L.lock_alive lock #0.5R (exists* v. pts_to x v ** pred v)
         and GR.pts_to right #0.5R 1 **
             L.lock_alive lock #0.5R (exists* v. pts_to x v ** pred v)
    { increment_f2 x lock (step left true) }
    { increment_f2 x lock (step right false) };

    L.gather2 lock;
    L.acquire lock;
    GR.gather left;
    GR.gather right;
    with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
    with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
    GR.free left;
    GR.free right;
    L.free lock
}


assume
val atomic_increment (r:ref int) (#i:erased int)
  : stt_atomic unit emp_inames 
    (pts_to r i)
    (fun _ -> pts_to r (i + 1))
     
module F = Pulse.Lib.FlippableInv

let test (l:iname) = assert (not (mem_inv emp_inames l))
let pts_to_refine #a (x:ref a) (p:a -> slprop) = exists* v. pts_to x v ** p v 

fn atomic_increment_f2
        (x: ref int)
        (#pred #qpred: int -> slprop)
        (l:iname)
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires inv l (pts_to_refine x pred) ** qpred 'i
ensures inv l (pts_to_refine x pred) ** qpred ('i + 1)
{
  with_invariants l {
    unfold pts_to_refine;
    with v. _;
    atomic_increment x;
    f v 'i;
    fold pts_to_refine;
  }
}


open Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
module I = Pulse.Lib.Stick.Util

fn atomic_increment_f3
        (x: ref int)
        (#pred #qpred: int -> slprop)
        (l:iname)
requires
  inv l (pts_to_refine x pred) **
  qpred 'i **
  (forall* v vq.
     (pred v ** qpred vq ** pts_to x (v + 1)) @==>
     (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1)))
ensures inv l (pts_to_refine x pred) ** qpred ('i + 1)
{
  with_invariants l {
    unfold pts_to_refine;
    with v. _;
    atomic_increment x;
    FA.elim #_ #(fun v -> forall* vq. (pred v ** qpred vq ** pts_to x (v + 1)) @==>
                                      (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))) v;

    FA.elim #_ #(fun vq -> (pred v ** qpred vq ** pts_to x (v + 1)) @==>
                           (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))) 'i;
    I.elim _ _;
    fold pts_to_refine;
  }
}

#pop-options

fn atomic_increment_f4
        (x: ref int)
        (#invp : slprop)
        (#pred #qpred: int -> slprop)
        (l:iname)
        (f: (v:int -> vq:int -> stt_ghost unit
                  emp_inames
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires
  inv l invp **
  qpred 'i **
  (invp @==> (exists* v. pts_to x v ** pred v)) ** 
  ((exists* v. pts_to x v ** pred v) @==> invp)
ensures inv l invp ** qpred ('i + 1)
{
  with_invariants l {
    I.elim invp _;
    atomic_increment x;
    f _ 'i;
    I.elim (exists* v. pts_to x v ** pred v) invp;
  }
}



assume
val atomic_read (r:ref int) (#p:_) (#i:erased int)
  : stt_atomic int emp_inames 
    (pts_to r #p i)
    (fun v -> pts_to r #p v ** pure (reveal i == v))

assume
val cas (r:ref int) (u v:int) (#i:erased int)
  : stt_atomic bool emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))



fn atomic_increment_f5
        (x: ref int)
        (#invp #tok : slprop)
        (#pred #qpred: int -> slprop)
        (l:iname)
        (elim_inv: 
          (_:unit -> stt_ghost unit emp_inames invp (fun _ ->
                    ((exists* v. pts_to x v ** pred v) ** tok))))
        (intro_inv:
            (_:unit -> stt_ghost unit
                        emp_inames
                        ((exists* v. pts_to x v ** pred v) ** tok)
                        (fun _ -> invp)))
        (f: (v:int -> vq:int -> stt_ghost unit 
                  emp_inames
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires inv l invp ** qpred 'i
ensures inv l invp ** qpred ('i + 1)
{
  fn read ()
  requires inv l invp
  returns v:int
  ensures inv l invp
  {
    with_invariants l {
        elim_inv ();
        with i. _;
        let v = atomic_read x;
        rewrite (pts_to x v) as (pts_to x i);
        intro_inv ();
        v
    }
  };
  let mut continue = true;
  fold (cond true (qpred 'i) (qpred ('i + 1)));
  while (
    with _b. _;
    let b = !continue;
    rewrite each _b as b;
    b
  )
  invariant b.
    inv l invp **
    pts_to continue b **
    cond b (qpred 'i) (qpred ('i + 1))
  {
    let v = read ();
    let next = 
      with_invariants l
      returns b1:bool
      ensures invp 
          ** cond b1 (qpred 'i) (qpred ('i + 1))
          ** pts_to continue true
      {
        elim_inv ();
        unfold cond;
        let b = cas x v (v + 1);
        if b
        {
          unfold cond;
          with vv. assert (pred vv);
          f vv _;
          intro_inv ();
          fold (cond false (qpred 'i) (qpred ('i + 1)));
          false
        }
        else
        {
          unfold cond;
          intro_inv ();
          fold (cond true (qpred 'i) (qpred ('i + 1)));
          true
        }
      };
    continue := next
  };
  unfold cond;
}
 


module C = Pulse.Lib.CancellableInvariant


fn atomic_increment_f6
        (x: ref int)
        (#p:_)
        (#pred #qpred: int -> slprop)
        (c:C.cinv)
        (f: (v:int -> vq:int -> stt_ghost unit
                  emp_inames
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v)) ** qpred 'i ** C.active c p
ensures inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v)) ** qpred ('i + 1) ** C.active c p
{
  with_invariants (C.iname_of c) {
    C.unpack_cinv_vp c;
    atomic_increment x;
    f _ 'i;
    C.pack_cinv_vp #(exists* v. pts_to x v ** pred v) c
  }
}




fn parallel_increment_inv
        (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc #int 0;
    let right = GR.alloc #int 0;
    GR.share left;
    GR.share right;
    let c = C.new_cancellable_invariant (
      exists* (v:int).
          pts_to x v **
          (exists* (vl vr:int).
            GR.pts_to left #0.5R vl **
            GR.pts_to right #0.5R vr **
            pure (v == 'i + vl + vr))

    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        (exists* (vl vr:int).
            GR.pts_to left #0.5R vl **
            GR.pts_to right #0.5R vr **
            pure (v == 'i + vl + vr)) **
        GR.pts_to lr #0.5R vq **
        pts_to x (v + 1)
      ensures
        (exists* (vl vr:int).
            GR.pts_to left #0.5R vl **
            GR.pts_to right #0.5R vr **
            pure (v + 1 == 'i + vl + vr)) **
        GR.pts_to lr #0.5R (vq + 1) **
        pts_to x (v + 1)
    { 
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
        GR.( left := vq + 1 );
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
        GR.( right := vq + 1 );
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
      }
    };

    C.share2 c;
    with pred. assert (inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v)));
    dup_inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v));

    parallel
    requires GR.pts_to left #0.5R 0 **
             C.active c 0.5R **
             inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v))
         and GR.pts_to right #0.5R 0 **
             C.active c 0.5R **
             inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v))
    ensures  GR.pts_to left #0.5R 1 **
             C.active c 0.5R **
             inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v))
         and GR.pts_to right #0.5R 1 **
             C.active c 0.5R **
             inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v))
    { atomic_increment_f6 x c (step left true) }
    { atomic_increment_f6 x c (step right false) };

    C.gather2 c;
    drop_ (inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v)));
    C.cancel c;
    GR.gather left;
    GR.gather right;
    with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
    with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
    GR.free left;
    GR.free right;
}

