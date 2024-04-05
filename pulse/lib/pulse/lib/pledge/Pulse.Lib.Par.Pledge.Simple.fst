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

module Pulse.Lib.Par.Pledge.Simple

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Stick
module P = Pulse.Lib.Par.Pledge

let pledge (f:vprop) (v:vprop) : vprop =
  exists* is. P.pledge is f v

(* Anything that holds now holds in the future too. *)
```pulse
ghost
fn __return_pledge (f v : vprop)
     requires v
     ensures pledge f v
{
  rewrite emp as (invlist_inv []);
  P.return_pledge [] f v;
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn __make_pledge (#is:invlist) (f v extra : vprop)
                 (k : ustep is (f ** extra) (f ** v))
  requires invlist_inv is ** extra
  ensures pledge f v
{
  P.make_pledge is f v extra k;
  fold pledge;
}
```
let make_pledge #is f v extra k = __make_pledge #is f v extra k

// FIXME: marking this ghost gives an awful error, but it should just
// fail saying that `is` is not `emp_inames`
//
// - Tactic logged issue:
// - refl_check_prop_validity failed (not a prop):  Top ()
//   > top (Prims.squash (Pulse.Lib.Core.inames_subset Pulse.Lib.Core.emp_inames (FStar.Ghost.reveal _)))
//   >> app arg (Pulse.Lib.Core.inames_subset Pulse.Lib.Core.emp_inames (FStar.Ghost.reveal _))
//   >>> app arg (FStar.Ghost.reveal _)
//   >>>> app arg (_)
//   Variable not found: _#6
```pulse
fn __redeem_pledge (f v : vprop)
      requires f ** pledge f v
      ensures f ** v
{
  unfold (pledge f v);
  with is. assert (P.pledge is f v);
  let is2 : invlist = invlist_reveal is;
  rewrite P.pledge (reveal is) f v
       as P.pledge is2 f v;
  P.redeem_pledge is2 f v;
  drop_ (invlist_inv is)
}
```
let redeem_pledge = __redeem_pledge

```pulse
ghost
fn __bind_pledge (#is:invlist) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : ustep is (f ** extra ** v1) (f ** pledge f v2))
   requires pledge f v1 ** extra
   ensures pledge f v2
{
    (* FIXME: It's actually unclear if we can define this, since we
       would have to know the invariants that second pledge would use,
       but nothing prevents them from depending on whenever the function
       is called (i.e. classical order of quantifiers problem.) *)

  admit()
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
ghost
fn __bind_pledge' (#is : invlist) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : ustep is (extra ** v1) (pledge f v2))
   requires pledge f v1 ** extra
   ensures pledge f v2
{
  ghost fn
  framed (_:unit)
    requires invlist_inv is ** (f ** extra ** v1)
    ensures  invlist_inv is ** (f ** pledge f v2)
    opens (invlist_names is)
  {
    k ();
  };
  bind_pledge #is #f #v1 #v2 extra framed;
}
```
let bind_pledge' = __bind_pledge'

```pulse
ghost
fn __join_pledge (#f v1 v2 : vprop)
  requires pledge f v1 ** pledge f v2
  ensures pledge f (v1 ** v2)
{
  unfold (pledge f v1);
  with is1g. assert (P.pledge is1g f v1);
  let is1 : invlist = invlist_reveal is1g;
  rewrite P.pledge (reveal is1g) f v1
       as P.pledge is1 f v1;

  unfold (pledge f v2);
  with is2g. assert (P.pledge is2g f v2);
  let is2 : invlist = invlist_reveal is2g;
  rewrite P.pledge (reveal is2g) f v2
       as P.pledge is2 f v2;

  // (* FIXME: should instead join and use pledge_sub_inv. Requires
  // some lemmas about InvList inclusion. *)
  assume_ (pure (is1 == is2));

  rewrite (P.pledge is2 f v2) as (P.pledge is1 f v2);
  P.join_pledge #is1 #f v1 v2;

  fold (pledge f (v1 ** v2))
}
```
let join_pledge = __join_pledge

// ```pulse
// unobservable
// fn __split_pledge (#f v1 v2 : vprop)
//   requires pledge f (v1 ** v2)
//   ensures pledge f v1 ** pledge f v2
// {
//   unfold pledge;
  
//   with is. assert (P.pledge is f (v1 ** v2));
//   let is' = invlist_reveal is;
  
//   rewrite each (reveal is) as is';
  
//   P.split_pledge #is' #f v1 v2;

//   fold pledge;
//   fold pledge;
// }
// ```
// let split_pledge = __split_pledge

```pulse
ghost
fn __rewrite_pledge (#is : invlist) (#f : vprop) (v1 v2 : vprop)
   (k : ustep is v1 v2)
   requires pledge f v1
   ensures pledge f v2
{
  unfold (pledge f v1);
  with is1g. assert (P.pledge is1g f v1);
  let is1 : invlist = invlist_reveal is1g;
  rewrite P.pledge (reveal is1g) f v1
       as P.pledge is1 f v1;

  // FIXME: similar to above
  assume_ (pure (is == is1));
  
  rewrite (P.pledge is1 f v1) as (P.pledge is f v1);
  P.rewrite_pledge #is #f v1 v2 k;
  fold pledge;
}
```
let rewrite_pledge = __rewrite_pledge
