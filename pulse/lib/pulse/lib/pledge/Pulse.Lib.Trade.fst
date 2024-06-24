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

open Pulse.Lib.Pervasives
open Pulse.Lib.InvList

module T = FStar.Tactics

let trade_elim_t is hyp extra concl : Type u#4 =
  unit -> stt_ghost unit is (extra ** hyp) (fun _ -> concl)

let trade_elim_exists (is:inames) (hyp extra concl:vprop) : vprop =
  pure (squash (trade_elim_t is hyp extra concl))

let trade (#is:inames) (hyp concl:vprop) =
  exists* extra. extra ** trade_elim_exists is hyp extra concl

```pulse
ghost
fn __intro_trade
  (#is:inames)
  (hyp concl extra:vprop)
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
```
let intro_trade #is = __intro_trade #is

```pulse
ghost
fn intro_trade_invs_aux
  (#is:invlist)
  (hyp concl extra:vprop)
  (f_elim: unit -> (
    stt_ghost unit emp_inames
    (invlist_v is ** extra ** hyp)
    (fun _ -> invlist_v is ** concl)
  ))
  requires invlist_inv is ** extra
  ensures trade #(invlist_names is) hyp concl
{
  ghost
  fn aux ()
    requires ((invlist_inv is ** extra) ** hyp)
    ensures concl
    opens (invlist_names is)
  {
    ghost fn aux' ()
      requires (invlist_v is ** (extra ** hyp))
      ensures (invlist_v is ** concl)
    {
      f_elim ()
    };
    with_invlist is aux';
    drop_ (invlist_inv _)
  };
  intro_trade #(invlist_names is) hyp concl (invlist_inv is ** extra) aux
}
```

let intro_trade_invs #is = intro_trade_invs_aux #is

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
fn deconstruct_trade (is:inames) (hyp concl: vprop)
  requires trade #is hyp concl
  returns res:(extra:erased vprop & trade_elim_t is hyp (reveal extra) concl)
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
    (| (extra <: erased vprop), f |) <: (p:erased vprop & trade_elim_t is hyp (reveal p) concl);
  rewrite (reveal extra) as (reveal (dfst res));
  res
}
```

```pulse
ghost
fn elim_trade_aux
  (#is:inames)
  (hyp concl:vprop)
  requires trade #is hyp concl ** hyp
  ensures concl
  opens is
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
  (#is1:inames)
  (#is2:inames { inames_subset is1 is2 })
  (hyp concl:vprop)
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
```
let trade_sub_inv = trade_sub_inv_aux

```pulse
ghost
fn __trade_map
  (#is : inames)
  (p q r : vprop)
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
```
let trade_map = __trade_map

```pulse
ghost
fn __trade_compose
  (#is : inames)
  (p q r : vprop)
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
```
let trade_compose = __trade_compose
