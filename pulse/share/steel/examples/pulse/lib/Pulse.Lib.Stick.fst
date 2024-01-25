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

module Pulse.Lib.Stick
open Pulse.Lib.Pervasives

let implication opens p q =
  unit -> stt_unobservable unit opens p (fun _ -> q)

let is_implication opens p q : prop =
  squash (implication opens p q)

assume
val indefinite_description_implication
  (#opens: inames) (#p #q:vprop)
  (_:squash (is_implication opens p q))
: unit -> stt_ghost unit opens p (fun _ -> q) //implication opens p q

let token (v:vprop) = v

let trade #opens (p q:vprop)
: vprop
= exists* (v:vprop). token v ** pure (is_implication opens (v ** p) q)

```pulse
ghost
fn return (#a:Type u#2) (x:a)
requires emp
returns v:a
ensures pure (v == x)
{
  x
}
```

```pulse
ghost //this should be unobservable, but we don't have a way to annotate that yet
fn elim_trade #is (hyp concl: vprop)
requires trade #is hyp concl ** hyp
ensures concl
opens is
{
  unfold (trade #is hyp concl);
  with v. assert (token v);
  unfold token;
  let f = return (indefinite_description_implication #is #(reveal v ** hyp) #concl ());
  f ();
}
```

```pulse
ghost
fn intro_trade
  (#[T.exact (`emp_inames)] is : inames)
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: unit -> (
    stt_unobservable unit is
    (v ** hyp)
    (fun _ -> concl)
  ))
requires v
ensures trade #is hyp concl
{
  let f = FStar.Squash.return_squash #(implication is (v ** hyp) concl) f_elim;
  fold (token v);
  fold (trade #is hyp concl);
}
```

let sub_inv
    (os1 : inames) 
    (os2 : inames{inames_subset os1 os2})
    (hyp concl:vprop)
    (f:implication os1 hyp concl)
: implication os2 hyp concl
= fun _ -> sub_invs_stt_unobservable (f ()) ()

let sub_inv_squash
    (os1 : inames) 
    (os2 : inames{inames_subset os1 os2})
    (hyp concl:vprop)
    (f:squash (is_implication os1 hyp concl))
: squash (is_implication os2 hyp concl)
= let p : squash (implication os1 hyp concl) = FStar.Squash.join_squash f in
  FStar.Squash.bind_squash p
    (fun f ->
      FStar.Squash.return_squash (sub_inv os1 os2 hyp concl f))

```pulse
ghost
fn trade_sub_inv
  (#os1 : inames)
  (#os2 : inames{inames_subset os1 os2})
  (hyp concl: vprop)
requires trade #os1 hyp concl
ensures trade #os2 hyp concl
{
  unfold trade #os1 hyp concl;
  with v. assert (token v);
  let _ = sub_inv_squash os1 os2 (reveal v ** hyp) concl ();
  fold (trade #os2 hyp concl);
}
```

let stick #is = admit()
let elim_stick #is = admit()
let intro_stick #is = admit()
let stick_sub_inv #os1 #os2 = admit()