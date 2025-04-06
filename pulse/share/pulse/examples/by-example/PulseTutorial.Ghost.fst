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

module PulseTutorial.Ghost
#lang-pulse
open Pulse.Lib.Pervasives


//incr_erased_non_ghost$
[@@expect_failure]
fn incr_erased_non_ghost (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  let x = reveal x;
  (x + 1)
}
//end incr_erased_non_ghost$

//incr_erased$
ghost
fn incr_erased (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  let x = reveal x;
  (x + 1)
}
//end incr_erased$


//try_use_incr_erased$
[@@expect_failure]
fn use_incr_erased (x:erased int)
requires emp
returns y:int
ensures emp ** pure (y == x + 1)
{
  incr_erased x;
}
//end try_use_incr_erased$


//use_incr_erased$
fn use_incr_erased (x:erased int)
requires emp
returns y:erased int
ensures emp ** pure (y == x + 1)
{
  ghost
  fn wrap (x:erased int)
  requires emp
  returns y:erased int
  ensures emp ** pure (y == x + 1)
  {
    let y = incr_erased x;
    hide y
  };
  wrap x
}
//end use_incr_erased$




//use_incr_erased_alt$
fn use_incr_erased_alt (x:erased int)
requires emp
returns y:erased int
ensures emp ** pure (y == x + 1)
{ 
  call_ghost incr_erased x;
}
//end use_incr_erased_alt$

//add_erased$
ghost
fn add_erased (x y:erased int)
requires emp
returns z:int
ensures emp ** pure (z == x + y)
{
  let x = reveal x;
  let y = reveal y;
  (x + y)
}
//end add_erased$


//use_add_erased$
fn use_add_erased (x y:erased int)
requires emp
returns z:erased int
ensures emp ** pure (z == x + y)
{
  call_ghost (add_erased x) y
}
//end use_add_erased$


//add_erased_erased$
ghost
fn add_erased_erased (x y:erased int)
requires emp
returns z:erased int
ensures emp ** pure (z == x + y)
{
  let x = reveal x;
  let y = reveal y;
  hide (x + y)
}
//end add_erased_erased$

let id p = p

//__rewrite_sig$
ghost
fn __rewrite (p q:slprop)
requires p ** pure (p == q)
ensures q
//end __rewrite_sig$
{
  rewrite p as q;
}



//intro_exists_sig$
ghost
fn intro_exists (#a:Type0) (p:a -> slprop) (x:erased a)
requires p x
ensures exists* x. p x
//end intro_exists_sig$
{
  ()
}


//all_at_most$
let rec all_at_most (l:list (ref nat)) (n:nat)
: slprop
= match l with
  | [] -> emp
  | hd::tl -> exists* (i:nat). pts_to hd i ** pure (i <= n) ** all_at_most tl n
//end all_at_most$


//weaken_at_most$
ghost
fn rec weaken_at_most (l:list (ref nat)) (n:nat) (m:nat)
requires all_at_most l n ** pure (n <= m)
ensures all_at_most l m
decreases l
{
  match l {
    [] -> {
      unfold (all_at_most [] n);
      fold (all_at_most [] n);
    }
    hd :: tl -> {
      unfold (all_at_most (hd::tl) n);
      weaken_at_most tl n m;
      fold (all_at_most (hd::tl) m);
    }
  }
}
//end weaken_at_most$

module GR = Pulse.Lib.GhostReference
//new_ghost_ref$
ghost
fn new_ghost_ref #a (x:a)
requires emp
returns r:GR.ref a
ensures GR.pts_to r x
{
  GR.alloc x;
}
//end new_ghost_ref$


//use_new_ghost_ref$
fn use_new_ghost_ref (x:ref nat)
requires pts_to x 'v
returns r:GR.ref nat
ensures pts_to x 'v ** GR.pts_to r 'v
{
  let v = !x;
  new_ghost_ref v
}
//end use_new_ghost_ref$


//correlated$
let correlated #a (x:ref a) (y:GR.ref a) (v:a)=
  pts_to x v ** GR.pts_to y #0.5R v
//end correlated$


//use_temp_sig$
fn use_temp (x:ref int) (y:GR.ref int)
requires exists* v0. correlated x y v0
ensures exists* v1. correlated x y v1
//end use_temp_sig$
//use_temp_body$
{
  unfold correlated;
  let v = !x;
  x := 17; //temporarily mutate x, give to to another function to use with full perm
  x := v; //but, we're forced to set it back to its original value
  fold correlated;
}
//end use_temp_body$



//use_correlated$
fn use_correlated ()
requires emp
ensures emp
{
  let mut x = 17;
  let g = GR.alloc 17;
  GR.share g;
  fold correlated;  // GR.pts_to g #0.5R 17 ** correlated x g 17
  use_temp x g;     // GR.pts_to g #0.5R 17 ** correlated x g ?v1
  unfold correlated; // GR.pts_to g #0.5R 17 ** GR.pts_to g #0.5R ?v1 ** pts_to x ?v1
  GR.gather g;       //this is the crucial step
                     // GT.pts_to g 17 ** pure (?v1 == 17) ** pts_to x ?v1
  assert (pts_to x 17);
  GR.free g;
}
//end use_correlated$