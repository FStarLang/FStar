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

module Test.Basic1
#lang-pulse

open Pulse.Lib.Pervasives

// #set-options "--debug ggg"

assume val foo1 : slprop
assume val foo2 : slprop
assume val foo3 : slprop
assume val foo4 : slprop
assume val foo5 : slprop
assume val foo6 : slprop
assume val foo7 : slprop
assume val foo8 : slprop
assume val foo9 : slprop
assume val foo10 : slprop


#push-options "--no_smt"
fn test_synt ()
  preserves foo1
  preserves foo2
  preserves foo3
  preserves foo4
  preserves foo5
  preserves foo6
  preserves foo7
  preserves foo8
  preserves foo9
  preserves foo10
{
  ();
}
#pop-options


(* Similar example, but all the heads match so we would attempt to use SMT if we didn't
just match everything syntactically. *)
assume val foo : int -> slprop


fn test_synt2 ()
  preserves foo 1
  preserves foo 2
  preserves foo 3
  preserves foo 4
  preserves foo 5
  preserves foo 6
  preserves foo 7
  preserves foo 8
  preserves foo 9
  preserves foo 10
{
  ();
}


assume val fooparam : erased int -> slprop


(* Works without SMT due to pulse simplifier *)
#push-options "--no_smt"
fn test_fastunif (x:erased int)
  requires fooparam (hide (reveal x))
  ensures  fooparam x
{
  ();
}
#pop-options

module SZ = FStar.SizeT

// #set-options "--debug pulse,prover,ggg --ugly --print_full_names"


// Actually, there are queries involved in re-typechecking the uvar solutions
// during matching...
// #push-options "--no_smt"
fn test1 (n:SZ.t)
{
  let mut i : SZ.t = 0sz;
  let mut max : nat = 0;
  i := 1sz;
  let vmax = !max;
  ();
}
// #pop-options


fn test2 (n:SZ.t)
{
  let mut max : nat = 0;
  let mut i : SZ.t = 0sz;
  i := 1sz;
  let vmax = !max;
  ();
}



fn test3 (r:ref int)
  requires r |-> 0
  ensures  exists* x. (r |-> x) ** pure (x == 0)
{
  ();
}

fn test4 (r:ref int)
  requires exists* x. (r |-> x) ** pure (x == 0)
  ensures  r |-> 0
{
  ();
}


fn test5 (r:ref int)
  preserves pts_to r 0
{
  test3 r;
  ();
}

