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

let finv_p (p:slprop { is_storable p }) (r : GR.ref bool) : v:slprop { is_storable v } =
  exists* (b:bool). pts_to r #0.5R b ** (if b then p else emp)

noeq
type finv (p:slprop) = {
  r : GR.ref bool;
  i : iname;
  p_big : squash (is_storable p);
}

let off #p (fi : finv p) : slprop =
  pts_to fi.r #0.5R false ** inv fi.i (finv_p p fi.r)
let on  #p (fi : finv p) : slprop =
  pts_to fi.r #0.5R true ** inv fi.i (finv_p p fi.r)


fn mk_finv (p:slprop { is_storable p })
   requires emp
   returns f:(finv p)
   ensures off f
{
   let r = GR.alloc false;
   GR.share2 r;
   rewrite emp
        as (if false then p else emp);
   fold finv_p p r;
   let i = new_invariant (finv_p p r);
   let fi = Mkfinv r i (() <: squash (is_storable p)); // See #121
   rewrite (pts_to r #0.5R false)
        as (pts_to fi.r #0.5R false);
   rewrite (inv i (finv_p p r))
        as (inv fi.i (finv_p p fi.r));
   fold (off #p fi);
   fi
}



let iname_of #p (f : finv p) : iname = f.i


atomic
fn flip_on (#p:slprop) (fi:finv p)
   requires off fi ** p
   ensures on fi
   opens [iname_of fi]
{
  open Pulse.Lib.GhostReference;
  unfold off;
  with_invariants fi.i
    returns _:unit
    ensures later (finv_p p fi.r) **
            pts_to fi.r #0.5R true
    opens [fi.i]
  {
    later_elim_storable _;
    unfold finv_p;
    GR.gather2 fi.r;
    rewrite (if false then p else emp) as emp;
    fi.r := true;
    GR.share2 fi.r;
    rewrite p as (if true then p else emp);
    fold (finv_p p fi.r);
    later_intro (finv_p p fi.r);
  };
  fold (on fi)
}



atomic
fn flip_off (#p:slprop) (fi : finv p)
   requires on fi
   ensures off fi ** p
   opens [iname_of fi]
{
  open Pulse.Lib.GhostReference;
  unfold on;
  with_invariants fi.i
    returns _:unit
    ensures later (finv_p p fi.r) **
            pts_to fi.r #0.5R false ** p
    opens [fi.i]
  {
    later_elim_storable _;
    unfold finv_p;
    GR.gather2 fi.r;
    rewrite (if true then p else emp) as p;
    fi.r := false;
    GR.share2 fi.r;
    rewrite emp as (if false then p else emp);
    fold (finv_p p fi.r);
    later_intro (finv_p p fi.r);
  };
  fold (off fi)
}

