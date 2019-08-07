(*
   Copyright 2008-2019 Microsoft Research

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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module FStar.Profiling
open FStar
open FStar.All
open FStar.Options
module BU = FStar.Util

(*
   A counter id is the name of a profiling phase;
   The total_time is the cumulative time attributed to this phase.
   The running flag records if this phase is currently being measured
*)
type counter = {
  cid:string;
  total_time:ref<int>;
  running:ref<bool>;
  undercount:ref<bool>;
}

(* Creating a new counter *)
let new_counter cid = {
  cid = cid;
  total_time = BU.mk_ref 0;
  running = BU.mk_ref false;
  undercount = BU.mk_ref false;
}

(* A table of all profiling counters, indexed by their cids *)
let all_counters : BU.smap<counter> = BU.smap_create 20

(* Returns the current counter for cid *)
let create_or_lookup_counter cid =
  match BU.smap_try_find all_counters cid with
  | Some c -> c
  | None ->
    let c = new_counter cid in
    BU.smap_add all_counters cid c;
    c

(* Time an operation, if the the profiler is enabled *)
let profile  (f: unit -> 'a) (module_name:option<string>) (cid:string) : 'a =
  if Options.profile_enabled  module_name cid
  then let c = create_or_lookup_counter cid in
       if !c.running
       then f ()
       else begin
         try
           c.running := true;
           let res, elapsed = BU.record_time f in
           c.total_time := !c.total_time + elapsed;
           c.running := false;
           res
         with
         | e ->
           c.running := false;
           c.undercount := true;
           raise e
      end
  else f()

(* Report all profiles and clear all counters *)
let report_and_clear tag =
    let ctrs =
      BU.smap_fold all_counters (fun _ v l -> v :: l) []
    in
    BU.smap_clear all_counters;
    let ctrs =
      BU.sort_with (fun c1 c2 -> !c2.total_time - !c1.total_time) ctrs
    in
    ctrs |> List.iter
      (fun c ->
        let warn = if !c.running
                   then " (Warning, this counter is still running)"
                   else if !c.undercount
                   then " (Warning, some operations raised exceptions and we not accounted for)"
                   else ""
        in
        BU.print4 "%s, profiled %s:\t %s ms%s\n"
                      tag
                      c.cid
                      (BU.string_of_int (!c.total_time))
                      warn)
