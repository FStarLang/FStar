(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
open FSharp.Compatibility.OCaml
open FStar.Options

module BU = FStar.Util
let profiling = ref false

exception ProfilingException of string

type counter = {total_time:int ref;}
type profiler = {plevel:Options.profile_t; pname:string; ptime:int ref; counters:System.Collections.Generic.Dictionary<string, counter>; }
let stack:ref<(list<profiler>)> = BU.mk_ref []

let cur_counters () = 
  match !stack with
  | hd::tl -> Some (hd.counters)
  | _ -> None

let find_counter (counters:System.Collections.Generic.Dictionary<string, counter>) n =
  let (hit, res) = counters.TryGetValue n in
  if hit then Some res else None

let new_counter (counters:System.Collections.Generic.Dictionary<string, counter>) name =
  let ctr = {total_time= ref 0;} in
  counters.Add(name, ctr);
  ()

let add_counter counters name elapsed =
  match find_counter counters name with
    | Some ctr -> ctr.total_time := elapsed + !ctr.total_time;
    | _ -> 
      failwith ("counter for " ^ name ^ "not found")

let push_stack p =
  stack := p::!stack

let get_profiler l s new_level =
  if new_level then
    // create a counter for each profile_phase, instead of creating it lazily when the phase is
    // invoked. This is to ensure profile data will be consistent for all modules regardless 
    // whether a phase is invoked for all modules, e.g. for modules without decls, we will still
    // have normalization time as 0ms, instead of missing normalization time since normalization is
    // never called. 
    let cts = new System.Collections.Generic.Dictionary<string, counter>() in
    Options.get_profile_phase() |> List.iter (fun l ->  new_counter cts l);
    let p = {plevel=l; pname=s; ptime = ref 0; counters=cts} in 
    push_stack p;
    Some (p.counters)
  else
    cur_counters()

let propogate_profile_info p =
  match cur_counters() with
  | Some counters ->
    let c = p.counters in
    // propogate profile info from counter 'c' up the stack to the next level
    let all_keys = List.ofSeq (c.Keys) in 
    all_keys |> List.map (fun k -> let t = snd <| c.TryGetValue(k) in add_counter counters k !t.total_time) |> ignore
  | _ -> ()

let pop_stack  () =
  match !stack with
  | c::tl ->
    stack := tl;
    c
  | _ -> failwith "Impossible: Too many pops"

let print_profile p =
  let counters = p.counters in
  let ctr2string name =
    let ctr = 
      match find_counter counters name with 
      | Some ctr -> ctr 
      | _ ->  failwith ("counter for " ^ name ^ "not found") in
    Printf.sprintf "\t%s: %s ms" name (string_of_int (!ctr.total_time)) in
  let all_keys = List.ofSeq (counters.Keys) in
  let output = List.fold_left
    (fun accum c -> accum ^ (ctr2string c)) (p.pname + ": ") all_keys in
  Printf.printf "Profiled %s: %s\t total: %s ms\n" (Options.profile_name p.plevel) output (string_of_int !p.ptime)

let pop_and_print_profiler name elapsed =
  let p = pop_stack () in
  if not (p.pname = name) then failwith "stack not matching";
  p.ptime := elapsed + !p.ptime;
  propogate_profile_info p;
  print_profile p

let profile' (f: unit -> 'b) (name:string) (phasename:Options.profile_t) (new_level:bool) (new_phase:bool): 'b * int =
  let counters = get_profiler phasename name new_level in // push a new profiler if new_level
  let (r, ms) = BU.record_time f in
  let _ = match counters with
  | Some counters -> // has a profiler to aggregate time
    if new_phase then add_counter counters (Options.profile_name phasename) ms; // only aggregate the time on phases that are profiled.
    if new_level then pop_and_print_profiler name ms; // pop and print current level
  | None -> 
    // if there is no profiler (which means no profile_at_level), then don't
    // aggregate, just print out the time
    Printf.printf "%s: %s: %s ms\n" name (Options.profile_name phasename)(string_of_int ms)
  in 
  (r, ms)

let profile  (f: unit -> 'b) (msg:unit -> string) (phasename:Options.profile_t): 'b * int =
  let new_level = Options.profile_at_level phasename in
  let new_phase = Options.profile_phase phasename in
  if (!profiling && (new_level || new_phase)) then 
    profile' f (msg()) phasename new_level new_phase
  else BU.record_time f

let init_profiler () = profiling := true

let disable_profiler () = profiling := false