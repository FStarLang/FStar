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

module PulseTutorial.ParallelIncrement
#lang-pulse
open Pulse.Lib.Pervasives
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference

//par$
fn par (#pf #pg #qf #qg:_)
       (f: unit -> stt unit pf (fun _ -> qf))
       (g: unit -> stt unit pg (fun _ -> qg))
requires pf ** pg
ensures qf ** qg
{
  parallel 
  requires pf and pg
  ensures qf and qg
  { f () }
  { g () };
  ()
}
//end par$


fn incr2 (x y:ref int)
requires pts_to x 'i ** pts_to y 'j
ensures pts_to x ('i + 1) ** pts_to y ('j + 1)
{
  fn incr (x:ref int) (#i:erased int)
  requires pts_to x i
  ensures pts_to x (i + 1)
  {
    let v = !x;
    x := v + 1;
  };
  par (fun _ -> incr x) (fun _ -> incr y);
}



[@@expect_failure]
fn attempt0 (x:ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
  fn incr (#i:erased int)
  requires pts_to x i
  ensures pts_to x (i + 1)
  {
    let v = !x;
    x := v + 1;
  };
  par (fun _ -> incr) (fun _ -> incr);
}


//attempt$
fn attempt (x:ref int)
requires pts_to x 'i
ensures exists* v. pts_to x v
{
  let l = L.new_lock (exists* v. pts_to x v);
  fn incr ()
  requires L.lock_alive l #0.5R (exists* v. pts_to x v)
  ensures L.lock_alive l #0.5R (exists* v. pts_to x v)
  {
    L.acquire l;
    let v = !x;
    x := v + 1;
    L.release l
  };
  L.share l;
  par incr incr;
  L.gather l;
  L.acquire l;
  L.free l
}
//end attempt$

//lock_inv$
let contributions (left right: GR.ref int) (i v:int) : timeless_slprop =
  exists* (vl vr:int).
    GR.pts_to left #0.5R vl **
    GR.pts_to right #0.5R vr **
    pure (v == i + vl + vr)

let lock_inv (x:ref int) (init:int) (left right:GR.ref int) : timeless_slprop =
  exists* v. 
    pts_to x v **
    contributions left right init v
//end lock_inv$

//incr_left$
fn incr_left (x:ref int)
             (#p:perm)
             (#left:GR.ref int)
             (#right:GR.ref int)
             (#i:erased int)
             (lock:L.lock )
requires L.lock_alive lock #p (lock_inv x i left right) ** GR.pts_to left #0.5R 'vl
ensures L.lock_alive lock #p (lock_inv x i left right) ** GR.pts_to left #0.5R ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather left;
  GR.write left ('vl + 1);
  GR.share left;
  fold (contributions left right i (v + 1));
  fold lock_inv;
  L.release lock
}
//end incr_left$

//incr_right$
fn incr_right (x:ref int)
              (#p:perm)
              (#left:GR.ref int)
              (#right:GR.ref int)
              (#i:erased int)
              (lock:L.lock)
requires L.lock_alive lock #p (lock_inv x i left right) ** GR.pts_to right #0.5R 'vl
ensures L.lock_alive lock #p (lock_inv x i left right) ** GR.pts_to right #0.5R ('vl + 1)
{
  L.acquire lock;
  unfold lock_inv;
  unfold contributions;
  let v = !x;
  x := v + 1;
  GR.gather right;
  GR.write right ('vl + 1);
  GR.share right;
  fold (contributions left right i (v + 1));
  fold (lock_inv x i left right);
  L.release lock
}
//end incr_right$

//add2$
fn add2 (x:ref int)
requires pts_to x 'i
ensures  pts_to x ('i + 2)
{
  let left = GR.alloc 0;
  let right = GR.alloc 0;
  GR.share left;
  GR.share right;
  fold (contributions left right 'i 'i);
  fold (lock_inv x 'i left right);
  let lock = L.new_lock (lock_inv x 'i left right);
  L.share lock;
  par (fun _ -> incr_left x lock)
      (fun _ -> incr_right x lock);
  L.gather lock;
  L.acquire lock;
  L.free lock;
  unfold lock_inv;
  unfold contributions;
  GR.gather left;
  GR.gather right;
  GR.free left;
  GR.free right;
}
//end add2$

/////////////////////////////////////////////////////////////////////////
// A bit more generic, with ghost functions
// A similar style to Bart Jacobs & Frank Piessens POPL '11
/////////////////////////////////////////////////////////////////////////

//Parameterize incr by the ghost steps it needs to take
//give it an abstract spec in terms of some call-provided aspec
//incr$
fn incr (x: ref int)
        (#p:perm)
        (#refine #aspec: int -> slprop)
        (l:L.lock)
        (ghost_steps: 
          (v:int -> vq:int -> stt_ghost unit
               emp_inames
               (refine v ** aspec vq ** pts_to x (v + 1))
               (fun _ -> refine (v + 1) ** aspec (vq + 1) ** pts_to x (v + 1))))
requires L.lock_alive l #p (exists* v. pts_to x v ** refine v) ** aspec 'i
ensures L.lock_alive l #p (exists* v. pts_to x v ** refine v) ** aspec ('i + 1)
 {
    L.acquire l;
    with _v. _;
    let vx = !x;
    rewrite each _v as vx;
    x := vx + 1;
    ghost_steps vx 'i;
    L.release l;
}
//end incr$

//At the call-site, we instantiate incr twice, with different
//ghost steps
//add2_v2$
fn add2_v2 (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc 0;
    let right = GR.alloc 0;
    GR.share left;
    GR.share right;
    fold (contributions left right 'i 'i);
    let lock = L.new_lock (
      exists* (v:int).
        pts_to x v ** contributions left right 'i v
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        contributions left right 'i v **
        GR.pts_to lr #0.5R vq **
        pts_to x (v + 1)
      ensures
        contributions left right 'i (v + 1) **
        GR.pts_to lr #0.5R (vq + 1) **
        pts_to x (v + 1)
    { 
      unfold contributions;
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        GR.write left (vq + 1);
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        GR.write right (vq + 1);
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
    };
    L.share lock;
    par (fun _ -> incr x lock (step left true))
        (fun _ -> incr x lock (step right false));
    L.gather lock;
    L.acquire lock;
    L.free lock;
    unfold (contributions left right 'i);
    GR.gather left;
    GR.gather right;
    GR.free left;
    GR.free right;
}
//end add2_v2$

//Note, rather than using two ghost references and duplicating code
//monoids and use just a single piece of ghost state. But, that's for another
//chapter

/////////////////////////////////////////////////////////////////////////
// Using invariants instead of locks
/////////////////////////////////////////////////////////////////////////

// Doing this with int instead of U32, just to keep it a bit simpler
// assuming atomic_read and cas on int
//atomic_primitives$
assume
val atomic_read (r:ref int) (#p:_) (#i:erased int)
  : stt_atomic int emp_inames 
    (pts_to r #p i)
    (fun v -> pts_to r #p i ** pure (reveal i == v))

assume
val cas (r:ref int) (u v:int) (#i:erased int)
  : stt_atomic bool emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))
//end atomic_primitives$

//This provides a way to allocate an invariant
//and then discard it
module C = Pulse.Lib.CancellableInvariant

//incr_atomic_spec$
fn incr_atomic
        (x: ref int)
        (#p:perm)
        (#refine #aspec: int -> slprop)
        (c:C.cinv)
        (f: (v:int -> vq:int -> stt_ghost unit
                  emp_inames
                  (refine v ** aspec vq ** pts_to x (v + 1))
                  (fun _ -> refine (v + 1) ** aspec (vq + 1) ** pts_to x (v + 1))))
requires inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** refine v)) ** aspec 'i ** C.active c p
ensures inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** refine v)) ** aspec ('i + 1) ** C.active c p
//end incr_atomic_spec$
//incr_atomic_body$
{
  //incr_atomic_body_read$
  atomic
  fn read ()
  requires inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** refine v)) ** C.active c p ** later_credit 1
  opens [C.iname_of c]
  returns v:int
  ensures inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** refine v)) ** C.active c p
  {
    with_invariants (C.iname_of c)
    {
        later_elim _;
        C.unpack_cinv_vp #p c;
        let v = atomic_read x;
        C.pack_cinv_vp #(exists* v. pts_to x v ** refine v) c;
        later_intro (C.cinv_vp c (exists* v. pts_to x v ** refine v));
        v
    }
  };
  //end incr_atomic_body_read$
  //incr_atomic_body_loop$
  let mut continue = true;
  fold (cond true (aspec 'i) (aspec ('i + 1)));
  while (
    with _b. _;
    let b = !continue;
    rewrite each _b as b;
    b
  )
  invariant b.
    inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** refine v)) **
    pts_to continue b **
    C.active c p **
    cond b (aspec 'i) (aspec ('i + 1))
  {
    later_credit_buy 1;
    let v = read ();
    later_credit_buy 1;
    let next = 
      with_invariants (C.iname_of c)
      returns b1:bool
      ensures later (C.cinv_vp c (exists* v. pts_to x v ** refine v))
          ** cond b1 (aspec 'i) (aspec ('i + 1))
          ** pts_to continue true
          ** C.active c p
      {
        later_elim _;
        C.unpack_cinv_vp c;
        unfold cond;
        let b = cas x v (v + 1);
        if b
        { 
          unfold cond;
          with vv. assert (refine vv);
          f vv _;
          C.pack_cinv_vp #(exists* v. pts_to x v ** refine v) c;
          fold (cond false (aspec 'i) (aspec ('i + 1)));
          later_intro (C.cinv_vp c (exists* v. pts_to x v ** refine v));
          false
        }
        else
        {
          unfold cond;
          C.pack_cinv_vp #(exists* v. pts_to x v ** refine v) c;
          fold (cond true (aspec 'i) (aspec ('i + 1)));
          later_intro (C.cinv_vp c (exists* v. pts_to x v ** refine v));
          true
        }
      };
    continue := next
  };
  //end incr_atomic_body_loop$
  unfold cond;
}
//end incr_atomic_body$


//add2_v3$
fn add2_v3 (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc 0;
    let right = GR.alloc 0;
    GR.share left;
    GR.share right;
    fold (contributions left right 'i 'i);
    let c = C.new_cancellable_invariant (
      exists* (v:int).
          pts_to x v **
          contributions left right 'i v
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        contributions left right 'i v **
        GR.pts_to lr #0.5R vq **
        pts_to x (v + 1)
      ensures
        contributions left right 'i (v + 1) **
        GR.pts_to lr #0.5R (vq + 1) **
        pts_to x (v + 1)
    { 
      unfold contributions;
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        GR.write left (vq + 1);
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        GR.write right (vq + 1);
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
        fold (contributions left right 'i (v + 1));
      }
    };
    C.share c;
    with pred. assert (inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v)));
    dup_inv (C.iname_of c) (C.cinv_vp c (exists* v. pts_to x v ** pred v));
    par (fun _ -> incr_atomic x c (step left true))
        (fun _ -> incr_atomic x c (step right false));
    
    C.gather c;
    later_credit_buy 1;
    C.cancel c;
    unfold contributions;
    GR.gather left;
    GR.gather right;
    GR.free left;
    GR.free right;
    drop_ (inv _ _)
}
//end add2_v3$


///////////////////////////////////////////////////////////////////////////////
// Using single ghost state with a pcm to manage the views of the two threads
// We pick product of two fractional permission PCMs as the ghost state
///////////////////////////////////////////////////////////////////////////////

open FStar.PCM

module U = FStar.Universe
module G = FStar.Ghost
module Prod = Pulse.Lib.PCM.Product
module Frac = Pulse.Lib.PCM.Fraction

type int1 : Type u#1 = U.raise_t int

type ghost_st : Type u#1 = Frac.fractional int1 & Frac.fractional int1

let pcm : pcm ghost_st = Prod.pcm_prod Frac.pcm_frac Frac.pcm_frac

let with_p (n:int1) (p:perm) : Frac.fractional int1 = Some (n, p)
let full (n:int1) : Frac.fractional int1 = Some (n, 1.0R)
let half (n:int1) : Frac.fractional int1 = Some (n, 0.5R)

let fp_upd_t1
  (t1_old:G.erased int1) 
  (t1_new:int1)
  (t2:int1)
  (p2:perm)
  
  : frame_preserving_upd pcm (full t1_old, with_p t2 p2) (full t1_new, with_p t2 p2) =
  
  Prod.mk_frame_preserving_upd_fst
    #_
    #_
    #Frac.pcm_frac
    #Frac.pcm_frac
    _
    _
    (with_p t2 p2)
    (Frac.mk_frame_preserving_upd t1_old t1_new)

let fp_upd_t2
  (t1:int1)
  (p1:perm)
  (t2_old:G.erased int1) 
  (t2_new:int1)
  
  : frame_preserving_upd pcm (with_p t1 p1, full t2_old) (with_p t1 p1, full t2_new) =
  
  Prod.mk_frame_preserving_upd_snd
    #_
    #_
    #Frac.pcm_frac
    #Frac.pcm_frac
    (with_p t1 p1)
    _
    _
    (Frac.mk_frame_preserving_upd t2_old t2_new)


ghost
fn share (r:ghost_pcm_ref pcm) (#n1 #n2:int1)
  requires ghost_pcm_pts_to r (full n1, full n2)
  ensures ghost_pcm_pts_to r (half n1, None) **
          ghost_pcm_pts_to r (None, half n2) **
          ghost_pcm_pts_to r (half n1, half n2)
{
  rewrite (ghost_pcm_pts_to r (full n1, full n2)) as
          (ghost_pcm_pts_to r ((half n1, None) `op pcm` (half n1, full n2)));
  ghost_share r (half n1, None) (half n1, full n2);
  rewrite (ghost_pcm_pts_to r (half n1, full n2)) as
          (ghost_pcm_pts_to r ((None, half n2) `op pcm` (half n1, half n2)));
  ghost_share r (None, half n2) (half n1, half n2)
}



ghost
fn gather (r:ghost_pcm_ref pcm) (#n1 #n2:int1) (#v1 #v2:int1)
  requires ghost_pcm_pts_to r (half n1, None) **
           ghost_pcm_pts_to r (None, half n2) **
           ghost_pcm_pts_to r (half v1, half v2)
  returns _:squash (v1 == n1 /\ v2 == n2)
  ensures ghost_pcm_pts_to r (full n1, full n2)

{
  ghost_gather r (None, half n2) (half v1, half v2);
  rewrite (ghost_pcm_pts_to r ((None, half n2) `op pcm` (half v1, half v2))) as
          (ghost_pcm_pts_to r (half v1, full n2));
  ghost_gather r (half n1, None) (half v1, full n2);
  rewrite (ghost_pcm_pts_to r ((half n1, None) `op pcm` (half v1, full n2))) as
          (ghost_pcm_pts_to r (full n1, full n2))
}


let lock_inv_ghost (ghost_r:ghost_pcm_ref pcm) (n:int) : timeless_slprop =
  exists* n1 n2. ghost_pcm_pts_to ghost_r (half n1, half n2) **
                 pure (n == U.downgrade_val n1 + U.downgrade_val n2)

let lock_inv_pcm (r:ref int) (ghost_r:ghost_pcm_ref pcm) : timeless_slprop =
  exists* n. pts_to r n ** lock_inv_ghost ghost_r n

let t1_perm (ghost_r:ghost_pcm_ref pcm) (n:int1) (t1:bool) =
  if t1
  then ghost_pcm_pts_to ghost_r (half n, None)
  else ghost_pcm_pts_to ghost_r (None, half n)

let add_one (n:int1) : int1 = U.raise_val (U.downgrade_val n + 1)

//
// Lock, increment the reference, and
//  update the ghost state's first component if t1 = true, else the second
// 

fn incr_pcm_t (r:ref int) (ghost_r:ghost_pcm_ref pcm) (l:L.lock) (t1:bool) (#n:int1)
  requires L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
           t1_perm ghost_r n t1
  ensures L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
          t1_perm ghost_r (add_one n) t1
{
  L.acquire l;
  unfold lock_inv_pcm;
  unfold lock_inv_ghost;
  let v = !r;
  r := v + 1;
  if t1 {
    rewrite (t1_perm ghost_r n t1) as
            (ghost_pcm_pts_to ghost_r (half n, None));
    with n1 n2. assert (ghost_pcm_pts_to ghost_r (half n1, half n2));
    ghost_gather ghost_r (half n, None) (half n1, half n2);
    rewrite (ghost_pcm_pts_to ghost_r ((half n, None) `op pcm` (half n1, half n2))) as
            (ghost_pcm_pts_to ghost_r (full n1, half n2));
    ghost_write ghost_r
      (full n1, half n2)
      (full (add_one n1), half n2)
      (fp_upd_t1 n1 (add_one n1) n2 0.5R);
    rewrite (ghost_pcm_pts_to ghost_r (full (add_one n1), half n2)) as
            (ghost_pcm_pts_to ghost_r ((half (add_one n1), half n2) `op pcm` (half (add_one n1), None)));
    ghost_share ghost_r (half (add_one n1), half n2) (half (add_one n1), None);
    fold lock_inv_ghost;
    fold lock_inv_pcm;
    L.release l;
    fold (t1_perm ghost_r (add_one n) true);
  } else {
    rewrite (t1_perm ghost_r n t1) as
            (ghost_pcm_pts_to ghost_r (None, half n));
    with n1 n2. assert (ghost_pcm_pts_to ghost_r (half n1, half n2));
    ghost_gather ghost_r (None, half n) (half n1, half n2);
    rewrite (ghost_pcm_pts_to ghost_r ((None, half n2) `op pcm` (half n1, half n2))) as
            (ghost_pcm_pts_to ghost_r (half n1, full n2));
    ghost_write ghost_r
      (half n1, full n2)
      (half n1, full (add_one n2))
      (fp_upd_t2 n1 0.5R n2 (add_one n2));
    rewrite (ghost_pcm_pts_to ghost_r (half n1, full (add_one n2))) as
            (ghost_pcm_pts_to ghost_r ((half n1, half (add_one n2)) `op pcm` (None, half (add_one n2))));
    ghost_share ghost_r (half n1, half (add_one n2)) (None, half (add_one n2));
    fold lock_inv_ghost;
    fold lock_inv_pcm;
    L.release l;
    fold (t1_perm ghost_r (add_one n) false)
  }
}


let zero1 : int1 = U.raise_val 0


fn incr_pcm (r:ref int) (#n:erased int)
  requires pts_to r 0
  ensures pts_to r 2
{
  let ghost_r = ghost_alloc #_ #pcm (G.hide (full zero1, full zero1));
  with _v. rewrite (ghost_pcm_pts_to ghost_r (G.reveal (G.hide _v))) as
                   (ghost_pcm_pts_to ghost_r _v);
  share ghost_r;
  fold lock_inv_ghost;
  fold lock_inv_pcm;

  rewrite (ghost_pcm_pts_to ghost_r (half zero1, None)) as
          (t1_perm ghost_r zero1 true);
  rewrite (ghost_pcm_pts_to ghost_r (None, half zero1)) as
          (t1_perm ghost_r zero1 false);

  let l = L.new_lock (lock_inv_pcm r ghost_r);
  
  L.share l;

  parallel
    requires L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
             t1_perm ghost_r zero1 true and
             L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
             t1_perm ghost_r zero1 false
    ensures L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
            t1_perm ghost_r (add_one zero1) true and
            L.lock_alive l #0.5R (lock_inv_pcm r ghost_r) **
            t1_perm ghost_r (add_one zero1) false
    { incr_pcm_t r ghost_r l true }
    { incr_pcm_t r ghost_r l false };

  L.gather l;
  L.acquire l;
  unfold lock_inv_pcm;
  unfold lock_inv_ghost;
  unfold (t1_perm ghost_r (add_one zero1) true);
  unfold (t1_perm ghost_r (add_one zero1) false);
  gather ghost_r;
  L.free l;
  drop_ (ghost_pcm_pts_to ghost_r _)
}


//////////////////////////////////////////////////////////////////////////////////////////
// Passing ghost steps to incr, a similar style to Bart Jacobs & Frank Piessens POPL '11
//////////////////////////////////////////////////////////////////////////////////////////


fn incr_pcm_t_abstract (r:ref int) (l:L.lock)
  (#ghost_inv:int -> slprop)
  (#ghost_pre:slprop)
  (#ghost_post:slprop)
  (ghost_steps:
     (v:int ->
      stt_ghost unit emp_inames
        (ghost_pre ** ghost_inv v)
        (fun _ -> ghost_post ** ghost_inv (v + 1))))
  requires L.lock_alive l #0.5R (exists* v. pts_to r v ** ghost_inv v) **
           ghost_pre
  ensures L.lock_alive l #0.5R (exists* v. pts_to r v ** ghost_inv v) **
          ghost_post
{
  L.acquire l;
  let v = !r;
  r := v + 1;
  with _v. rewrite (ghost_inv _v) as (ghost_inv v);
  ghost_steps v;
  L.release #(exists* v. pts_to r v ** ghost_inv v) l
}



fn incr_pcm_abstract (r:ref int)
  requires pts_to r 0
  ensures pts_to r 2
{
  let ghost_r = ghost_alloc #_ #pcm (G.hide (full zero1, full zero1));

  ghost
  fn t1 (v:int)
    requires ghost_pcm_pts_to ghost_r (half zero1, None) ** lock_inv_ghost ghost_r v
    ensures ghost_pcm_pts_to ghost_r (half (add_one  zero1), None) ** lock_inv_ghost ghost_r (v + 1)
  {
    unfold lock_inv_ghost;
    with n1 n2. assert (ghost_pcm_pts_to ghost_r (half n1, half n2));
    ghost_gather ghost_r (half zero1, None) (half n1, half n2);
    rewrite (ghost_pcm_pts_to ghost_r ((half zero1, None) `op pcm` (half n1, half n2))) as
            (ghost_pcm_pts_to ghost_r (full n1, half n2));
    ghost_write ghost_r
      (full n1, half n2)
      (full (add_one n1), half n2)
      (fp_upd_t1 n1 (add_one n1) n2 0.5R);
    rewrite (ghost_pcm_pts_to ghost_r (full (add_one n1), half n2)) as
            (ghost_pcm_pts_to ghost_r ((half (add_one n1), half n2) `op pcm` (half (add_one n1), None)));
    ghost_share ghost_r (half (add_one n1), half n2) (half (add_one n1), None);
    fold ((lock_inv_ghost ghost_r) (v + 1))
  };

  ghost
  fn t2 (v:int)
    requires ghost_pcm_pts_to ghost_r (None, half zero1) ** lock_inv_ghost ghost_r v
    ensures ghost_pcm_pts_to ghost_r (None, half (add_one  zero1)) ** lock_inv_ghost ghost_r (v +1)
  {
    unfold lock_inv_ghost;
    with n1 n2. assert (ghost_pcm_pts_to ghost_r (half n1, half n2));
    ghost_gather ghost_r (None, half zero1) (half n1, half n2);
    rewrite (ghost_pcm_pts_to ghost_r ((None, half n2) `op pcm` (half n1, half n2))) as
            (ghost_pcm_pts_to ghost_r (half n1, full n2));
    ghost_write ghost_r
      (half n1, full n2)
      (half n1, full (add_one n2))
      (fp_upd_t2 n1 0.5R n2 (add_one n2));
    rewrite (ghost_pcm_pts_to ghost_r (half n1, full (add_one n2))) as
            (ghost_pcm_pts_to ghost_r ((half n1, half (add_one n2)) `op pcm` (None, half (add_one n2))));
    ghost_share ghost_r (half n1, half (add_one n2)) (None, half (add_one n2));
    fold ((lock_inv_ghost ghost_r) (v + 1))
  };

  with _v. rewrite (ghost_pcm_pts_to ghost_r (G.reveal (G.hide _v))) as
                   (ghost_pcm_pts_to ghost_r _v);
  share ghost_r;
  fold lock_inv_ghost;
  let l = L.new_lock (exists* v. pts_to r v ** lock_inv_ghost ghost_r v);
  L.share l;

  parallel
    requires L.lock_alive l #0.5R (exists* v. pts_to r v ** lock_inv_ghost ghost_r v) **
             ghost_pcm_pts_to ghost_r (half zero1, None) and
             L.lock_alive l #0.5R (exists* v. pts_to r v ** lock_inv_ghost ghost_r v) **
             ghost_pcm_pts_to ghost_r (None, half zero1)
    
    ensures L.lock_alive l #0.5R (exists* v. pts_to r v ** lock_inv_ghost ghost_r v) **
            ghost_pcm_pts_to ghost_r (half (add_one zero1), None) and
            L.lock_alive l #0.5R (exists* v. pts_to r v ** lock_inv_ghost ghost_r v) **
            ghost_pcm_pts_to ghost_r (None, half (add_one zero1))

    { incr_pcm_t_abstract r l t1 }
    { incr_pcm_t_abstract r l t2 };

  L.gather l;
  L.acquire l;
  unfold lock_inv_ghost;
  gather ghost_r;
  L.free l;
  drop_ (ghost_pcm_pts_to ghost_r _)
}
