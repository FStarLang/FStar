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

open Pulse.Lib.Core
open Pulse.Lib.Pervasives
open Pulse.Lib.InvList
module T = FStar.Tactics

let trade_elim_t is hyp extra concl : Type u#2 =
  unit -> stt_ghost unit (invlist_v is ** extra ** hyp) (fun _ -> invlist_v is ** concl)

let trade_elim_exists (is:invlist) (hyp extra concl : vprop) : vprop =
  pure (squash (trade_elim_t is hyp extra concl))

let trade (#is : invlist) (hyp : vprop) (concl : vprop) =
  exists* extra. extra ** trade_elim_exists is hyp extra concl

```pulse
ghost
fn __intro_trade
  (#is : invlist)
  (hyp concl : vprop)
  (extra : vprop)
  (f_elim: unit -> (
    stt_ghost unit
    (invlist_v is ** extra ** hyp)
    (fun _ -> invlist_v is ** concl)
  ))
  requires extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  assert (extra ** trade_elim_exists is hyp extra concl); // FIXME: why is this needed? somehow guiding the prover?
  fold (trade #is hyp concl);
}
```
let intro_trade #is = __intro_trade #is

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

```pulse
ghost
fn pextract (a:Type u#2) (_:squash a)
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
```

```pulse
ghost
fn __elim_trade_ghost
  (#is : invlist)
  (hyp concl : vprop)
  requires invlist_v is ** trade #is hyp concl ** hyp
  ensures invlist_v is ** concl
{
  unfold (trade #is hyp concl);

  with extra. assert (extra ** trade_elim_exists is hyp extra concl);
  
  unfold (trade_elim_exists is hyp extra concl);

  let pf : squash (psquash (trade_elim_t is hyp (reveal extra) concl)) =
    elim_pure_explicit (psquash (trade_elim_t is hyp (reveal extra) concl));

  let pf : squash (trade_elim_t is hyp (reveal extra) concl) =
    FStar.Squash.join_squash pf;

  let f = pextract (trade_elim_t is hyp (reveal extra) concl) pf;
  
  f();
}
```
let elim_trade_ghost #is = __elim_trade_ghost #is

```pulse
unobservable
fn elim_trade_helper
  (#is : invlist)
  (hyp concl : vprop)
  (_ : unit)
  requires invlist_v is ** (trade #is hyp concl ** hyp)
  ensures invlist_v is ** concl
{
  elim_trade_ghost #is hyp concl;
}
```

```pulse
unobservable
fn __elim_trade
  (#is : invlist)
  (hyp concl : vprop)
  requires trade #is hyp concl ** hyp
  ensures concl
  opens (invlist_names is)
{
  with_invlist is (elim_trade_helper #is hyp concl);
}
```
let elim_trade #is = __elim_trade #is

```pulse
ghost
fn __trade_sub_inv
  (#os1 : invlist)
  (#os2 : invlist{invlist_sub os1 os2})
  (hyp concl: vprop)
  requires trade #os1 hyp concl
  ensures  trade #os2 hyp concl
{
  ghost
  fn aux (_:unit)
    requires (invlist_v os2 ** trade #os1 hyp concl) ** hyp
    ensures  invlist_v os2 ** concl
  {
    invlist_sub_split os1 os2;
    elim_trade_ghost #os1 hyp concl;
    Pulse.Lib.Priv.Trade0.elim_stick (invlist_v os1) (invlist_v os2);
  };
  intro_trade hyp concl (trade #os1 hyp concl) aux;
}
```
let trade_sub_inv = __trade_sub_inv
