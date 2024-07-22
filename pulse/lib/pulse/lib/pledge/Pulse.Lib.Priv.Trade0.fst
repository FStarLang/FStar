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

module Pulse.Lib.Priv.Trade0
#lang-pulse
open PulseCore.Observability
open Pulse.Lib.Pervasives

module GW = Pulse.Lib.GhostWitness

#set-options "--print_universes"

(* Do NOT use this module. Use a simple Trade instead. This is only here
to be able to define subtyping of invariants for InvList, which cannot use trades. *)
   
let implication p q : Type u#4 =
  unit -> stt_ghost unit emp_inames p (fun _ -> q)

let exists_implication p q : Type u#0 =
  squash (implication p q)

let ctx (v:slprop) : slprop = v

let stick (p q:slprop)
: slprop
= exists* (v:slprop). ctx v ** pure (exists_implication (v ** p) q)


fn return (#a:Type u#2) (x:a)
requires emp
returns v:a
ensures pure (v == x)
{
  x
}


(* Fake squash *)
let psquash (a:Type u#a) : prop = squash a


ghost
fn elim_stick (hyp concl: slprop)
requires stick hyp concl ** hyp
ensures concl
{
  unfold (stick hyp concl);
  with v. assert ctx v;
  let u : squash (psquash (implication (v ** hyp) concl)) =
    elim_pure_explicit (psquash (implication (v ** hyp) concl));
  let u : squash (implication (v ** hyp) concl) =
    FStar.Squash.join_squash u;
  let f = GW.ghost_witness2 (implication (reveal v ** hyp) concl) u;
  unfold ctx;
  f ();
}



ghost
fn intro_stick
  (hyp concl: slprop)
  (v: slprop)
  (f_elim: unit -> (
    stt_ghost unit emp_inames
    (v ** hyp)
    (fun _ -> concl)
  ))
requires v
ensures stick hyp concl
{
  let f = FStar.Squash.return_squash #(implication (v ** hyp) concl) f_elim;
  fold (ctx v);
  fold (stick hyp concl);
}



ghost
fn frame_stick
  (hyp concl: slprop)
  (f: slprop)
requires stick hyp concl
ensures stick (hyp ** f) (concl ** f)
{
  ghost
  fn aux (_:unit)
    requires stick hyp concl ** (hyp ** f)
    ensures concl ** f
  {
    elim_stick hyp concl;
  };
  intro_stick (hyp ** f) (concl ** f) (stick hyp concl) aux;
}

