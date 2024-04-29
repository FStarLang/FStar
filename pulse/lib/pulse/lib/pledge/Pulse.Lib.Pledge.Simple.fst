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

module Pulse.Lib.Pledge.Simple

open Pulse.Lib.Pervasives

module P = Pulse.Lib.Pledge

let pledge (f:vprop) (v:vprop) : vprop =
  exists* is. P.pledge is f v

(* Anything that holds now holds in the future too. *)
```pulse
ghost
fn return_pledge (f v : vprop)
  requires v
  ensures pledge f v
{
  P.return_pledge f v;
  fold pledge;
}
```

```pulse
ghost
fn make_pledge
  (#is:inames)
  (f v extra:vprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  requires extra
  ensures pledge f v
{
  P.make_pledge is f v extra k;
  fold pledge;
}
```

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
fn redeem_pledge (f v:vprop)
  requires f ** pledge f v
  ensures f ** v
{
  unfold (pledge f v);
  P.redeem_pledge _ f v;
}
```

```pulse
ghost
fn join_pledge (#f v1 v2:vprop)
  requires pledge f v1 ** pledge f v2
  ensures pledge f (v1 ** v2)
{
  unfold pledge;
  unfold pledge;
  with is1. assert (P.pledge is1 f v1);
  with is2. assert (P.pledge is2 f v2);
  P.pledge_sub_inv is1 (join_inames is1 is2) f v1;
  P.pledge_sub_inv is2 (join_inames is1 is2) f v2;
  P.join_pledge #(join_inames is1 is2) #f v1 v2;
  fold pledge
}
```

```pulse
ghost
fn rewrite_pledge
  (#f v1 v2:vprop)
  (#is_k:inames)
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  requires pledge f v1
  ensures pledge f v2
{
  unfold pledge;
  with is. assert (P.pledge is f v1);
  P.pledge_sub_inv is (join_inames is is_k) f v1;
  P.rewrite_pledge #(join_inames is is_k) #f v1 v2 #is_k k;
  fold pledge
}
```
