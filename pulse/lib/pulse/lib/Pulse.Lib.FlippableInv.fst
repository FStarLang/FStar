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

module Pulse.Lib.FlippableInv
#lang-pulse

open Pulse.Lib.Pervasives
module GR = Pulse.Lib.GhostReference

let finv_p (p:slprop) (r : GR.ref bool) : slprop =
  exists* (b:bool). pts_to r #0.5R b ** (if b then p else emp)

ghost
fn fold_finv_p (p:slprop) (r : GR.ref bool) (#b:bool)
  requires pts_to r #0.5R b
  requires (if b then p else emp)
  ensures  finv_p p r
{
  fold finv_p;
}

noeq
type finv (p:slprop) = {
  r : GR.ref bool;
  i : iname;
}

let off #p (fi : finv p) : slprop =
  pts_to fi.r #0.5R false ** inv fi.i (finv_p p fi.r)
let on  #p (fi : finv p) : slprop =
  pts_to fi.r #0.5R true ** inv fi.i (finv_p p fi.r)


ghost fn mk_finv (p:slprop)
   requires emp
   returns f:(finv p)
   ensures off f
{
   let r = GR.alloc false;
   GR.share r;
   rewrite emp
        as (if false then p else emp);
   fold finv_p p r;
   let i = new_invariant (finv_p p r);
   let fi = Mkfinv #p r i; // See #121
   rewrite (pts_to r #0.5R false)
        as (pts_to fi.r #0.5R false);
   rewrite (inv i (finv_p p r))
        as (inv fi.i (finv_p p fi.r));
   fold (off #p fi);
   fi
}



let iname_of #p (f : finv p) : iname = f.i


ghost
fn flip_on (#p:slprop) (fi:finv p)
   requires off fi
   requires p
   requires later_credit 1
   ensures on fi
   opens [iname_of fi]
{
  open Pulse.Lib.GhostReference;
  unfold off;
  with_invariants_g unit emp_inames fi.i (finv_p p fi.r)
    (p ** pts_to fi.r #0.5R false) (fun _ -> pts_to fi.r #0.5R true) fn _
  {
    unfold finv_p;
    with b.
      assert (pts_to fi.r #0.5R b ** pts_to fi.r #0.5R false);
    GR.gather fi.r #false #_;
    rewrite each b as false;
    fi.r := true;
    GR.share fi.r;
    fold_finv_p p fi.r;
  };
  fold on fi;
}

ghost
fn flip_off (#p:slprop) (fi : finv p)
   requires on fi
   requires later_credit 1
   ensures off fi ** p
   opens [iname_of fi]
{
  open Pulse.Lib.GhostReference;
  unfold on;
  with_invariants_g unit emp_inames fi.i (finv_p p fi.r)
    (pts_to fi.r #0.5R true) (fun _ -> p ** pts_to fi.r #0.5R false) fn _
  {
    unfold finv_p;
    with b.
      assert (pts_to fi.r #0.5R b ** pts_to fi.r #0.5R true);
    GR.gather fi.r;
    rewrite each b as true;
    fi.r := false;
    GR.share fi.r;
    fold_finv_p p fi.r;
  };
  fold off fi;
}
