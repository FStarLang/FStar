(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.CountingSemaphore2
#lang-pulse
open Pulse.Lib.Primitives
module B = Pulse.Lib.Box
module CInv = Pulse.Lib.CancellableInvariant

noeq type sem (p: slprop) : Type0 = {
  counter: B.box U32.t;
  ptank: Tank.tank (U32.v sem_max);
  i: CInv.cinv;
}

let permit_tank #p (s: sem p) : Tank.tank (U32.v sem_max) = s.ptank

(** Full invariant *)
let sem_inv (p: slprop) (counter: B.box U32.t) (ptank: Tank.tank (U32.v sem_max)) : slprop =
  exists* (n: U32.t).
    counter |-> n **
    replicate p (U32.v n) **
    Tank.owns ptank (U32.v n)

let sem_alive #p ([@@@mkey] s: sem p) (#[full_default()] f:perm) : slprop =
  inv (CInv.iname_of s.i) (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank)) **
  CInv.active s.i f

(** Replicate equality lemmas *)
let replicate_eq_emp (p: slprop)
: Lemma (replicate p 0 == emp)
= ()

let replicate_eq_cons (p: slprop) (i: pos)
: Lemma (replicate p i == (p ** replicate p (i - 1)))
= ()

let replicate_eq_cons' (p: slprop) (i: nat)
: Lemma (replicate p (i + 1) == (p ** replicate p i))
= ()

(** Replicate lemma: add one to front *)
ghost fn replicate_cons (p: slprop) (i: nat)
  requires p ** replicate p i
  ensures replicate p (i + 1)
{
  replicate_eq_cons' p i;
  rewrite (p ** replicate p i) as (replicate p (i + 1))
}

(** Replicate lemma: extract one from front *)
ghost fn replicate_uncons (p: slprop) (i: pos)
  requires replicate p i
  ensures p ** replicate p (i - 1)
{
  replicate_eq_cons p i;
  rewrite (replicate p i) as (p ** replicate p (i - 1))
}

(** Split replicate into two parts *)
ghost fn rec replicate_split (p: slprop) (i j: nat)
  requires replicate p (i + j)
  ensures replicate p i ** replicate p j
  decreases i
{
  if (i = 0) {
    // We have: replicate p (i + j) where i = 0, so (i + j) = j
    // Need: replicate p i ** replicate p j = replicate p 0 ** replicate p j
    assert (pure (i + j == j));
    rewrite (replicate p (i + j)) as (replicate p j);
    replicate_eq_emp p;
    rewrite emp as (replicate p i)
  } else {
    // Have: replicate p (i + j)
    // i + j > 0 when i > 0
    replicate_uncons p (i + j);
    // Now have: p ** replicate p ((i + j) - 1)
    // Note: (i + j) - 1 = (i - 1) + j when i > 0
    assert (pure ((i + j) - 1 == (i - 1) + j));
    rewrite (replicate p ((i + j) - 1)) as (replicate p ((i - 1) + j));
    replicate_split p (i - 1) j;
    // Now have: p ** replicate p (i - 1) ** replicate p j
    replicate_cons p (i - 1);
    // Now have: replicate p ((i-1)+1) ** replicate p j
    assert (pure ((i - 1) + 1 == i));
    rewrite (replicate p ((i - 1) + 1)) as (replicate p i)
  }
}

(** Join two replicates into one *)
ghost fn rec replicate_join (p: slprop) (i j: nat)
  requires replicate p i ** replicate p j
  ensures replicate p (i + j)
  decreases i
{
  if (i = 0) {
    // Have: replicate p i ** replicate p j = replicate p 0 ** replicate p j
    // Need: replicate p (i + j) = replicate p j (since i = 0)
    assert (pure (i + j == j));
    replicate_eq_emp p;
    rewrite (replicate p i) as emp;
    rewrite (replicate p j) as (replicate p (i + j))
  } else {
    // Have: replicate p i ** replicate p j
    replicate_uncons p i;
    // Have: p ** replicate p (i - 1) ** replicate p j
    replicate_join p (i - 1) j;
    // Have: p ** replicate p ((i - 1) + j)
    replicate_cons p ((i - 1) + j);
    // Have: replicate p ((i-1)+j+1)
    assert (pure ((i - 1) + j + 1 == i + j));
    rewrite (replicate p ((i - 1) + j + 1)) as (replicate p (i + j))
  }
}

fn new_sem (p: slprop) {| is_send p |} (n: U32.t)
  requires replicate p (U32.v n)
  returns s: sem p
  ensures sem_alive s
  ensures permit s (U32.v sem_max - U32.v n)
{
  let counter = B.alloc n;
  let ptank = Tank.alloc (U32.v sem_max);
  // ptank owns sem_max initially
  // We need to split: owns ptank (U32.v n) for invariant, owns ptank (sem_max - n) for permit
  Tank.share ptank #(U32.v n) #(U32.v sem_max - U32.v n);
  
  fold (sem_inv p counter ptank);
  let i = CInv.new_cancellable_invariant (sem_inv p counter ptank);
  let s : sem p = { counter; ptank; i };
  rewrite each counter as s.counter, ptank as s.ptank, i as s.i;
  fold (sem_alive s);
  rewrite (Tank.owns s.ptank (U32.v sem_max - U32.v n)) as (permit s (U32.v sem_max - U32.v n));
  s
}

fn new_sem_0 (p: slprop) {| is_send p |}
  returns s: sem p
  ensures sem_alive s
  ensures permit s (U32.v sem_max)
{
  fold (replicate p 0);
  let s = new_sem p 0ul;
  s
}

(** Read the counter value *)
fn read_counter (#p: slprop) (#f: perm) (s: sem p)
  preserves sem_alive s #f
  returns v: U32.t
{
  unfold (sem_alive s #f);
  
  let result =
    with_invariants U32.t emp_inames (CInv.iname_of s.i)
        (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank))
        (CInv.active s.i f)
        (fun _ -> CInv.active s.i f)
    fn _ {
      CInv.unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.ptank);
      
      with n. _;
      
      let v = read_atomic_box s.counter;
      
      fold (sem_inv p s.counter s.ptank);
      CInv.pack_cinv_vp s.i;
      v
    };
  
  fold (sem_alive s #f);
  result
}

(** Read counter for release - proves counter < sem_max when holding a permit *)
fn read_counter_for_release (#p: slprop) (#f: perm) (s: sem p) (#perm_amt: erased nat)
  requires sem_alive s #f ** permit s perm_amt ** pure (perm_amt > 0)
  returns v: (v:U32.t{U32.v v < U32.v sem_max})
  ensures sem_alive s #f ** permit s perm_amt
{
  unfold (sem_alive s #f);
  rewrite (permit s perm_amt) as (Tank.owns s.ptank perm_amt);
  
  let result : (v:U32.t{U32.v v < U32.v sem_max}) =
    with_invariants (v:U32.t{U32.v v < U32.v sem_max}) emp_inames (CInv.iname_of s.i)
        (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank))
        (CInv.active s.i f ** Tank.owns s.ptank perm_amt ** pure (perm_amt > 0))
        (fun _ -> CInv.active s.i f ** Tank.owns s.ptank perm_amt)
    fn _ {
      CInv.unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.ptank);
      
      with n. _;
      
      // Gather permits to prove bound
      Tank.gather s.ptank #perm_amt #(U32.v n);
      // Now we know: perm_amt + U32.v n <= sem_max
      // Since perm_amt > 0, U32.v n < sem_max
      Tank.share s.ptank #perm_amt #(U32.v n);
      
      let v = read_atomic_box s.counter;
      
      fold (sem_inv p s.counter s.ptank);
      CInv.pack_cinv_vp s.i;
      v
    };
  
  fold (sem_alive s #f);
  rewrite (Tank.owns s.ptank perm_amt) as (permit s perm_amt);
  result
}

fn try_acquire_many (#p: slprop) (#f: perm) (s: sem p) (n: U32.t)
  preserves sem_alive s #f
  returns b: bool
  ensures (if b then permit s (U32.v n) ** replicate p (U32.v n) else emp)
{
  // Read counter outside the invariant
  let v = read_counter s;
  
  if (U32.lt v n) {
    // Not enough available
    false
  } else {
    unfold (sem_alive s #f);
    
    // Try CAS from v to v - n
    let new_v = U32.sub v n;
    
    let result : bool =
      with_invariants bool emp_inames (CInv.iname_of s.i)
          (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank))
          (CInv.active s.i f ** pure (U32.v v >= U32.v n))
          (fun b -> CInv.active s.i f **
                    cond b (Tank.owns s.ptank (U32.v n) ** replicate p (U32.v n)) emp)
      fn _ {
        CInv.unpack_cinv_vp s.i;
        unfold (sem_inv p s.counter s.ptank);
        
        with counter_val. _;
        
        // Try CAS from v to new_v
        let b = cas_box s.counter v new_v;
        
        if b {
          elim_cond_true b _ _;
          // CAS succeeded: counter was v (== counter_val), now is new_v
          // We have: replicate p (U32.v counter_val) and Tank.owns s.ptank (U32.v counter_val)
          // We need to split off: replicate p (U32.v n) and Tank.owns s.ptank (U32.v n)
          
          // counter_val == v and new_v = v - n, so counter_val = n + new_v
          assert (pure (U32.v counter_val == U32.v n + U32.v new_v));
          rewrite (replicate p (U32.v counter_val)) as (replicate p (U32.v n + U32.v new_v));
          rewrite (Tank.owns s.ptank (U32.v counter_val)) as (Tank.owns s.ptank (U32.v n + U32.v new_v));
          
          // Split the tank: U32.v v = U32.v n + U32.v new_v
          Tank.share s.ptank #(U32.v n) #(U32.v new_v);
          
          // Split replicate
          replicate_split p (U32.v n) (U32.v new_v);
          
          fold (sem_inv p s.counter s.ptank);
          CInv.pack_cinv_vp s.i;
          
          fold (cond true (Tank.owns s.ptank (U32.v n) ** replicate p (U32.v n)) emp);
          true
        } else {
          elim_cond_false b _ _;
          // CAS failed
          fold (sem_inv p s.counter s.ptank);
          CInv.pack_cinv_vp s.i;
          fold (cond false (Tank.owns s.ptank (U32.v n) ** replicate p (U32.v n)) emp);
          false
        }
      };
    
    fold (sem_alive s #f);
    
    if result {
      elim_cond_true result (Tank.owns s.ptank (U32.v n) ** replicate p (U32.v n)) emp;
      rewrite (Tank.owns s.ptank (U32.v n)) as (permit s (U32.v n));
      true
    } else {
      elim_cond_false result (Tank.owns s.ptank (U32.v n) ** replicate p (U32.v n)) emp;
      false
    }
  }
}

fn try_acquire (#p: slprop) (#f: perm) (s: sem p)
  preserves sem_alive s #f
  returns b: bool
  ensures (if b then permit s 1 ** p else emp)
{
  let b = try_acquire_many s 1ul;
  if b {
    replicate_uncons p 1;
    unfold (replicate p 0);
    true
  } else {
    false
  }
}

(** Release loop - retry CAS until success *)
fn rec release_loop (#p: slprop) (#f: perm) (s: sem p)
  requires sem_alive s #f ** permit s 1 ** p
  ensures sem_alive s #f
{
  // Read counter to get expected value, proving it's < sem_max since we hold a permit
  let v = read_counter_for_release s #1;
  // v < sem_max, so v + 1 won't overflow
  let new_v : U32.t = U32.add v 1ul;
  
  unfold (sem_alive s #f);
  rewrite (permit s 1) as (Tank.owns s.ptank 1);
  
  let result : bool =
    with_invariants bool emp_inames (CInv.iname_of s.i)
        (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank))
        (CInv.active s.i f ** Tank.owns s.ptank 1 ** p)
        (fun b -> CInv.active s.i f ** cond b emp (Tank.owns s.ptank 1 ** p))
    fn _ {
      CInv.unpack_cinv_vp s.i;
      unfold (sem_inv p s.counter s.ptank);
      
      with n. _;
      
      let b = cas_box s.counter v new_v;
      
      if b {
        elim_cond_true b _ _;
        // CAS succeeded: n was v, counter is now new_v = v + 1
        // We have: replicate p (U32.v n) and n == v (since CAS succeeded)
        // We need: replicate p (U32.v new_v) = replicate p (U32.v v + 1)
        
        // Rewrite using n == v
        rewrite (replicate p (U32.v n)) as (replicate p (U32.v v));
        rewrite (Tank.owns s.ptank (U32.v n)) as (Tank.owns s.ptank (U32.v v));
        
        // Join the replicate: p ** replicate p (U32.v v) -> replicate p (U32.v v + 1)
        replicate_cons p (U32.v v);
        // Now have: replicate p (U32.v v + 1) = replicate p (U32.v new_v)
        assert (pure (U32.v v + 1 == U32.v new_v));
        rewrite (replicate p (U32.v v + 1)) as (replicate p (U32.v new_v));
        
        // Join the tank permissions
        Tank.gather s.ptank #1 #(U32.v v);
        // Now have: Tank.owns s.ptank (1 + U32.v v) = Tank.owns s.ptank (U32.v new_v)
        rewrite (Tank.owns s.ptank (1 + U32.v v)) as (Tank.owns s.ptank (U32.v new_v));
        
        fold (sem_inv p s.counter s.ptank);
        CInv.pack_cinv_vp s.i;
        
        fold (cond true emp (Tank.owns s.ptank 1 ** p));
        true
      } else {
        elim_cond_false b _ _;
        // CAS failed
        fold (sem_inv p s.counter s.ptank);
        CInv.pack_cinv_vp s.i;
        
        fold (cond false emp (Tank.owns s.ptank 1 ** p));
        false
      }
    };
  
  fold (sem_alive s #f);
  
  if result {
    elim_cond_true result emp (Tank.owns s.ptank 1 ** p)
  } else {
    elim_cond_false result emp (Tank.owns s.ptank 1 ** p);
    rewrite (Tank.owns s.ptank 1) as (permit s 1);
    release_loop s
  }
}

fn release (#p: slprop) (#f: perm) (s: sem p)
  preserves sem_alive s #f
  requires permit s 1 ** p
{
  release_loop s
}

ghost fn share (#p: slprop) (#f: perm) (s: sem p)
  requires sem_alive s #f
  ensures sem_alive s #(f /. 2.0R) ** sem_alive s #(f /. 2.0R)
{
  unfold (sem_alive s #f);
  CInv.share s.i;
  dup_inv (CInv.iname_of s.i) (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank));
  fold (sem_alive s #(f /. 2.0R));
  fold (sem_alive s #(f /. 2.0R))
}

ghost fn gather (#p: slprop) (#p1 #p2: perm) (s: sem p)
  requires sem_alive s #p1 ** sem_alive s #p2
  ensures sem_alive s #(p1 +. p2)
{
  unfold (sem_alive s #p1);
  unfold (sem_alive s #p2);
  CInv.gather s.i;
  drop_ (inv (CInv.iname_of s.i) (CInv.cinv_vp s.i (sem_inv p s.counter s.ptank)));
  fold (sem_alive s #(p1 +. p2))
}

fn free (#p: slprop) (s: sem p)
  requires sem_alive s
{
  unfold (sem_alive s);
  
  later_credit_buy 1;
  CInv.cancel s.i;
  
  unfold (sem_inv p s.counter s.ptank);
  with n. _;
  
  B.free s.counter;
  
  drop_ (replicate p (U32.v n));
  drop_ (Tank.owns s.ptank (U32.v n))
}