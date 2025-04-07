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

module PulseTutorial.SpinLock
#lang-pulse

open Pulse.Lib.Pervasives

module B = Pulse.Lib.Box

module U32 = FStar.UInt32

//lock$
let maybe (b:bool) (p:slprop) =
  if b then p else emp

let lock_inv (r:B.box U32.t) (p:slprop) : slprop =
  exists* v. B.pts_to r v ** maybe (v = 0ul) p

noeq
type lock = {
  r:B.box U32.t;
  i:iname;
}

let lock_alive (l:lock) (p:slprop) =
  inv l.i (lock_inv l.r p)
//end lock$

 //dup_lock_alive$
ghost
fn dup_lock_alive (l:lock) (p:slprop)
  requires lock_alive l p
  ensures lock_alive l p ** lock_alive l p
{
  unfold lock_alive;
  dup_inv l.i (lock_inv l.r p);
  fold lock_alive;
  fold lock_alive
}
//end dup_lock_alive$

 //new_lock$
fn new_lock (p:slprop)
requires p
returns l:lock
ensures lock_alive l p
{
   let r = B.alloc 0ul;
   fold (maybe (0ul = 0ul) p);
   fold (lock_inv r p);
   let i = new_invariant (lock_inv r p);
   let l = {r;i};
   rewrite (inv i (lock_inv r p)) as
           (inv l.i (lock_inv l.r p));
   fold lock_alive;
   l
}
//end new_lock$


//acquire_sig$
fn rec acquire (#p:slprop) (l:lock)
requires lock_alive l p
ensures lock_alive l p ** p
//end acquire_sig$
//acquire_body$
{
  unfold lock_alive;
  later_credit_buy 1;
  let b = 
    with_invariants l.i
      returns b:bool
      ensures later (lock_inv l.r p) ** maybe b p
      opens [l.i] {
      later_elim _;
      unfold lock_inv;
      let b = cas_box l.r 0ul 1ul;
      if b
      { 
        elim_cond_true _ _ _;
        with _b. rewrite (maybe _b p) as p;
        fold (maybe false p);
        rewrite (maybe false p) as (maybe (1ul = 0ul) p);
        fold (lock_inv l.r p);
        fold (maybe true p);
        later_intro (lock_inv l.r p);
        true
      }
      else
      {
        elim_cond_false _ _ _;
        fold (lock_inv l.r p);
        fold (maybe false p);
        later_intro (lock_inv l.r p);
        false
      }
    };
  fold lock_alive;
  if b { rewrite (maybe b p) as p; }
  else { rewrite (maybe b p) as emp; acquire l }
}
//end acquire_body$

//release$
fn release (#p:slprop) (l:lock)
requires lock_alive l p ** p
ensures lock_alive l p
{
  unfold lock_alive;
  later_credit_buy 1;
  with_invariants l.i
    returns _:unit
    ensures later (lock_inv l.r p)
    opens [l.i] {
    later_elim _;
    unfold lock_inv;
    write_atomic_box l.r 0ul;
    drop_ (maybe _ _); //maybe release without acquire
    fold (maybe (0ul = 0ul) p);
    fold (lock_inv l.r p);
    later_intro (lock_inv l.r p);
  };
  fold lock_alive
}
//end release$
