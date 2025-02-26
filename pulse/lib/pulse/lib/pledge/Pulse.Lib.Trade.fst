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

module Pulse.Lib.Trade
#lang-pulse

open Pulse.Lib.Pervasives


let trade_elim_t is hyp extra concl : Type u#4 =
  unit -> stt_ghost unit is (extra ** hyp) (fun _ -> concl)

let trade_elim_exists (is:inames) (hyp extra concl:slprop) : slprop =
  pure (squash (trade_elim_t is hyp extra concl))

let trade (#is:inames) (hyp concl:slprop) =
  exists* extra. extra ** trade_elim_exists is hyp extra concl


ghost
fn intro_trade
  (#[T.exact (`emp_inames)]is:inames)
  (hyp concl extra:slprop)
  (f_elim: unit -> (
    stt_ghost unit is
    (extra ** hyp)
    (fun _ -> concl)
  ))
  requires extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  assert (extra ** trade_elim_exists is hyp extra concl);
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
fn deconstruct_trade (is:inames) (hyp concl: slprop)
  requires trade #is hyp concl
  returns res:(extra:erased slprop & trade_elim_t is hyp (reveal extra) concl)
  ensures reveal (dfst res)
{
  unfold (trade #is hyp concl);
  with extra. assert (extra ** trade_elim_exists is hyp extra concl);
  unfold (trade_elim_exists is hyp (reveal extra) concl);
  let pf : squash (psquash (trade_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (trade_elim_t is hyp (reveal extra) concl));
  let pf : squash (trade_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;
  let f = pextract (trade_elim_t is hyp (reveal extra) concl) pf;
  let res =
    (| (extra <: erased slprop), f |) <: (p:erased slprop & trade_elim_t is hyp (reveal p) concl);
  rewrite (reveal extra) as (reveal (dfst res));
  res
}



ghost
fn elim_trade
  (#[T.exact (`emp_inames)]is:inames)
  (hyp concl:slprop)
  requires trade #is hyp concl ** hyp
  ensures concl
  opens is
{
  let res = deconstruct_trade is hyp concl;
  let f = dsnd res;
  rewrite dfst res as res._1;
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
    rewrite dfst res as res._1;
    f ()
  };
  
  intro_trade #is2 hyp concl (dfst res) aux
}


ghost
fn trade_map
  (#is : inames)
  (p q r : slprop)
  (f : unit -> stt_ghost unit emp_inames q (fun _ -> r))
  requires trade #is p q
  ensures  trade #is p r
{
  ghost
  fn aux ()
    requires trade #is p q ** p
    ensures  r
    opens is
  {
    elim_trade #is _ _;
    f ();
  };
  intro_trade #is p r (trade #is p q) aux;
}


ghost
fn trade_compose
  (#is : inames)
  (p q r : slprop)
  requires trade #is p q ** trade #is q r
  ensures  trade #is p r
{
  ghost
  fn aux ()
    requires (trade #is p q ** trade #is q r) ** p
    ensures  r
    opens is
  {
    elim_trade #is p _;
    elim_trade #is _ _;
  };
  intro_trade #is p r (trade #is p q ** trade #is q r) aux;
}

ghost
fn eq_as_trade
  (p1 p2 : slprop)
  requires pure (p1 == p2)
  ensures  p2 @==> p1
{
  ghost
  fn aux ()
    requires emp ** p2
    ensures p1
  {
    rewrite p2 as p1;
  };
  intro_trade p2 p1 emp aux;
  ();
}

ghost
fn rewrite_with_trade
  (p1 p2 : slprop)
  requires p1 ** pure (p1 == p2)
  ensures  p2 ** (p2 @==> p1)
{
  eq_as_trade p1 p2;
  rewrite p1 as p2;
  ();
}
