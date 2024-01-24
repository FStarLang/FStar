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
  P.pledge_any f v

(* Anything that holds now holds in the future too. *)
```pulse
ghost
fn __return_pledge (f v : vprop)
     requires v
     ensures pledge f v
{
  P.return_pledge emp_inames f v;
  fold P.pledge_any;
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn __make_pledge (#os:inames) (f v extra : vprop)
               (k : ustep os (f ** extra) (f ** v))
  requires extra
  ensures pledge f v
{
  P.make_pledge os f v extra k;
  fold P.pledge_any;
  fold pledge;
}
```
let make_pledge #os f v extra k = __make_pledge #os f v extra k

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
  unfold (P.pledge_any f v);
  with is. assert (P.pledge is f v);
  P.redeem_pledge is f v
}
```
let redeem_pledge = __redeem_pledge

```pulse
unobservable
fn __bind_pledge_simple_aux (#f #v1 #v2 : vprop)
       (extra : vprop)
       (invs : inames)
       (k : (unit -> stt_unobservable unit invs (f ** extra ** v1) (fun _ -> f ** P.pledge invs f v2)))
       (_:unit)
       requires f ** extra ** v1
       ensures f ** P.pledge invs f v2
       opens invs
{
  k ();
}
```

#set-options "--log_failing_queries --split_queries always --print_implicits --print_full_names"

```pulse
ghost
fn __bind_pledge (#os : inames) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : ustep os (f ** extra ** v1) (f ** pledge f v2))
   requires pledge f v1 ** extra
    ensures pledge f v2
{
  unfold (pledge f v1);
  unfold (P.pledge_any f v1);
  with is. assert (P.pledge is f v1);
  
  let invs = join_inames is os;
  pledge_sub_inv is invs f v1;
  assert (P.pledge invs f v1 ** extra);
  
  let k' : (unit -> stt_unobservable unit invs (f ** extra ** v1) (fun _ -> f ** P.pledge invs f v2)) =
    (* FIXME: It's actually unclear if we can define this, since we
       would have to know the invariants that second pledge would use,
       but nothing prevents them from depending on whenever the function
       is called (i.e. classical order of quantifiers problem.) *)
    admit();
  
  P.bind_pledge #invs #f #v1 #v2 extra k';

  fold P.pledge_any;
  fold pledge;
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
ghost
fn __bind_pledge' (#os : inames) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : (unit -> stt_unobservable unit os (extra ** v1) (fun () -> pledge f v2)))
   requires pledge f v1 ** extra
    ensures pledge f v2
{
  unobservable fn
  framed (_:unit)
    requires f ** extra ** v1
    ensures f ** pledge f v2
    opens os
  {
    k ();
  };
  bind_pledge #os #f #v1 #v2 extra framed;
}
```
let bind_pledge' = __bind_pledge'

```pulse
ghost
fn __join_pledge (#f v1 v2 : vprop)
  requires pledge f v1 ** pledge f v2
  ensures pledge f (v1 ** v2)
{
  unfold pledge;
  unfold pledge;
  unfold P.pledge_any;
  unfold P.pledge_any;
  
  with is1. assert (P.pledge is1 f v1);
  with is2. assert (P.pledge is2 f v2);
  
  let is = join_inames is1 is2;
  
  pledge_sub_inv is1 is f v1;
  pledge_sub_inv is2 is f v2;

  P.join_pledge #is #f v1 v2;

  fold P.pledge_any;
  fold pledge;
}
```
let join_pledge = __join_pledge

```pulse
unobservable
fn __split_pledge (#f v1 v2 : vprop)
  requires pledge f (v1 ** v2)
  ensures pledge f v1 ** pledge f v2
{
  unfold pledge;
  unfold P.pledge_any;
  
  with is. assert (P.pledge is f (v1 ** v2));
  
  P.split_pledge #is #f v1 v2;

  fold P.pledge_any;
  fold P.pledge_any;
  fold pledge;
  fold pledge;
}
```
let split_pledge = __split_pledge

```pulse
ghost
fn __rewrite_pledge (#os : inames) (#f : vprop) (v1 v2 : vprop)
   (k : ustep os v1 v2)
   requires pledge f v1
    ensures pledge f v2
{
  unfold pledge;
  unfold P.pledge_any;
  with is. assert (P.pledge is f v1);
  
  let invs = join_inames is os;
  
  pledge_sub_inv is invs f v1;

  unobservable fn
  k' (_:unit)
    requires v1
    ensures v2
    opens invs
  {
    k ();
  };
    
  P.rewrite_pledge #invs #f v1 v2 k';

  fold P.pledge_any;
  fold pledge;
}
```
let rewrite_pledge = __rewrite_pledge
