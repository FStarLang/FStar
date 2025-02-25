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

module Pulse.Lib.SmallTrade
#lang-pulse

open FStar.Ghost
open Pulse.Lib.Core
open Pulse.Lib.Pervasives


type small_slprop = v:slprop { timeless v }

let trade_elim_t (is:inames) (hyp:slprop) (extra:small_slprop) (concl:slprop) : Type u#4 =
  unit -> stt_ghost unit is (extra ** hyp) (fun _ -> concl)

let trade_elim_exists (is:inames) (hyp:slprop) (extra:small_slprop) (concl:slprop) : slprop =
  pure (squash (trade_elim_t is hyp extra concl))

let __trade (#is:inames) (hyp concl:slprop) : small_slprop =
  exists* (extra:small_slprop). extra ** trade_elim_exists is hyp extra concl

let trade (#is : inames)
  ([@@@mkey] hyp : slprop)
  ([@@@mkey] concl : slprop)
  : slprop
  = __trade #is hyp concl

let trade_is_timeless (#is:inames) (hyp concl:slprop)
  : Lemma (timeless (trade #is hyp concl)) = ()


ghost
fn intro_trade
  (#is:inames)
  (hyp concl:slprop)
  (extra:slprop { timeless extra })
  (f_elim:unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
  requires extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  fold (__trade #is hyp concl);
  fold (trade #is hyp concl)
}


let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a


ghost
fn pextract (a:Type u#4) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}



ghost
fn deconstruct_trade (is:inames) (hyp concl:slprop)
  requires trade #is hyp concl
  returns res:(extra:erased small_slprop & trade_elim_t is hyp (reveal extra) concl)
  ensures reveal (dfst res)
{
  unfold (trade #is hyp concl);
  unfold (__trade #is hyp concl);
  with (extra:small_slprop). assert (extra ** trade_elim_exists is hyp extra concl);
  unfold (trade_elim_exists is hyp (reveal extra) concl);
  let pf : squash (psquash (trade_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (trade_elim_t is hyp (reveal extra) concl));
  let pf : squash (trade_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;
  let f = pextract (trade_elim_t is hyp (reveal extra) concl) pf;
  let res =
    (| (extra <: erased small_slprop), f |) <: (p:erased small_slprop & trade_elim_t is hyp (reveal p) concl);
  rewrite extra as (dfst res);
  res
}



ghost
fn elim_trade
  (#is:inames)
  (hyp concl:slprop)
  requires trade #is hyp concl ** hyp
  ensures concl
  opens is
{
  let res = deconstruct_trade is hyp concl;
  let f = dsnd res;
  f ()
}



ghost
fn trade_sub_inv
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:slprop)
  requires trade #is1 hyp concl
  ensures trade #is2 hyp concl
{
  let res = deconstruct_trade is1 hyp concl;

  ghost
  fn aux ()
    requires (dfst res ** hyp)
    ensures concl
    opens is2
  {
    let f = dsnd res;
    f ()
  };
  
  intro_trade #is2 hyp concl (dfst res) aux
}



ghost
fn trade_map
  (#os : inames)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
  requires trade #os p q
  ensures trade #os p r
{
  ghost
  fn aux ()
    requires trade #os p q ** p
    ensures  r
    opens os
  {
    elim_trade #os p q;
    f ();
  };
  intro_trade #os p r (trade #os p q) aux;
}



ghost
fn trade_compose
  (#os : inames)
  (p q r : slprop)
  requires trade #os p q ** trade #os q r
  ensures trade #os p r
{
  ghost
  fn aux ()
    requires ((trade #os p q ** trade #os q r)) ** p
    ensures  (r)
    opens os
  {
    elim_trade #os p _;
    elim_trade #os _ _;
  };
  timeless_star (trade #os p q) (trade #os q r);
  intro_trade #os p r (trade #os p q ** trade #os q r) aux;
}

