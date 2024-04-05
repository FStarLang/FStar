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

let trade_elim_t is hyp extra concl : Type u#4 =
  unit -> stt_ghost unit (invlist_names is)
                         (invlist_inv is ** extra ** hyp)
                         (fun _ -> invlist_inv is ** concl)

let trade_elim_exists (is:invlist) (hyp extra concl : vprop) : vprop =
  pure (squash (trade_elim_t is hyp extra concl))

let trade (#is : invlist) (hyp : vprop) (concl : vprop) =
  invlist_inv is **
  (exists* extra. extra ** trade_elim_exists is hyp extra concl)

```pulse
ghost
fn __intro_trade
  (#is : invlist)
  (hyp concl : vprop)
  (extra : vprop)
  (f_elim: unit -> (
    stt_ghost unit (invlist_names is)
    (invlist_inv is ** extra ** hyp)
    (fun _ -> invlist_inv is ** concl)
  ))
  requires invlist_inv is ** extra
  ensures trade #is hyp concl
{
  fold (trade_elim_exists is hyp extra concl);
  assert (extra ** trade_elim_exists is hyp extra concl);
  fold (trade #is hyp concl)
}
```
let intro_trade #is = __intro_trade #is

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

```pulse
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
```

```pulse
ghost
fn deconstruct_trade (is:invlist) (hyp concl: vprop)
  requires trade #is hyp concl
  returns res:(extra:erased vprop & trade_elim_t is hyp (reveal extra) concl)
  ensures invlist_inv is ** reveal (dfst res)
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
    (| (extra <: erased vprop), f |) <: (p:erased vprop & trade_elim_t is hyp (reveal p) concl);
  rewrite (reveal extra) as (reveal (dfst res));
  res
}
```

```pulse
ghost
fn elim_trade_aux
  (#is : invlist)
  (hyp concl : vprop)
  requires trade #is hyp concl ** hyp
  ensures invlist_inv is ** concl
  opens (invlist_names is)
{
  let res = deconstruct_trade is hyp concl;
  let f = dsnd res;
  f ()
}
```

let elim_trade #is = elim_trade_aux #is

```pulse
ghost
fn trade_sub_inv_aux
  (#is1 : invlist)
  (#is2 : invlist{invlist_sub is1 is2})
  (hyp concl: vprop)
  requires invlist_inv is2 ** trade #is1 hyp concl
  ensures  invlist_inv is1 ** trade #is2 hyp concl
  opens (invlist_names is1)
{
  let res = deconstruct_trade is1 hyp concl;
  let extra = dfst res;
  let f = dsnd res;

  ghost
  fn aux ()
    requires (invlist_inv is2 ** extra ** hyp)
    ensures (invlist_inv is2 ** concl)
    opens (invlist_names is2)
  {
    invlist_sub_inv is1 is2;
    f ();
    Pulse.Lib.Priv.Trade0.elim_stick (invlist_inv is1) (invlist_inv is2)
  };

  intro_trade hyp concl extra aux
}
```
let trade_sub_inv = trade_sub_inv_aux

```pulse
ghost
fn trade_invs_aux (#is:invlist) (#hyp #concl:vprop) ()
  requires trade #is hyp concl
  ensures trade #is hyp concl ** invlist_inv is
{
  unfold (trade #is hyp concl);
  with extra. assert (extra ** trade_elim_exists is hyp extra concl);

  dup_invlist_inv is;
  let w_extra : vprop = reveal extra;
  rewrite each (reveal extra) as w_extra;
  assert (w_extra ** trade_elim_exists is hyp w_extra concl);
  fold (trade #is hyp concl)
}
```

let trade_invs = trade_invs_aux
