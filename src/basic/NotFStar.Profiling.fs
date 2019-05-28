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

type counter = {name:string; total_time:System.TimeSpan ref; nstarts:int ref; started_at:System.DateTime ref;}
type profiler = {name:string; counters:System.Collections.Generic.Dictionary<string, counter>; }
let stack:ref<(list<profiler>)> = BU.mk_ref []

let empty_stack () =
  match !stack with | [] -> true | _ -> false

let cur_counters () = 
  match !stack with
  | hd::tl -> hd.counters
  | _ -> failwith "empty stack"

let find_counter (counters:System.Collections.Generic.Dictionary<string, counter>) n =
  let (hit, res) = counters.TryGetValue n in
    if hit then Some res
    else None

let now () = System.DateTime.Now

let new_counter counters name =
  match find_counter counters name with
    | Some _ ->
(*         let _ = Util.pr "Already found counter %s\n" name in *)
          name
    | None ->
(*         let _ = Util.pr "Creating counter %s\n" name in *)
        let ctr = {name=name; total_time= ref (System.TimeSpan(0L)); nstarts=ref 0; started_at=ref (now())} in
        let _ = counters.Add(name, ctr) in
          name

let rec add_counter counters elapsed name =
  match find_counter counters name with
    | Some ctr ->
        //incr ctr.nstarts;
        ctr.total_time := elapsed + !ctr.total_time
    | None ->
        ignore <| new_counter counters name;
        add_counter counters elapsed name

let rec start_counter counters name =
  match find_counter counters name with
    | Some ctr ->
        incr ctr.nstarts;
        if !(ctr.nstarts) = 1 then ctr.started_at := now()
    | None -> ignore <| new_counter counters name; start_counter counters name

let stop_counter counters name : option<System.TimeSpan> =
  match find_counter counters name with
    | Some ctr ->
        decr ctr.nstarts;
        if !(ctr.nstarts) < 0 then raise (ProfilingException ("Starts and ends on counter "^name^" don't match up"));
        if !(ctr.nstarts) = 0 then
          let elapsed = now() - !ctr.started_at in
            ctr.total_time := elapsed + !ctr.total_time;
            Some elapsed
        else None
    | None -> raise (ProfilingException ("Counter " ^name^ " does not exist"))

let push_stack p =
  stack := p::!stack

let start_profile s =
  let p = {name=s; counters=new System.Collections.Generic.Dictionary<string, counter>()} in 
  push_stack p;
  p

let propogate_profile_info p =
  if (not (empty_stack())) then
    let counters = cur_counters () in
    let c = p.counters in
    // propogate profile info from counter 'c' up the stack to the next level
    let all_keys = List.ofSeq (c.Keys) in 
    all_keys |> List.map (fun k -> let t = snd <| c.TryGetValue(k) in add_counter counters !t.total_time k) |> ignore

let pop_stack  () =
  match !stack with
  | c::tl ->
    stack := tl;
    c
  | _ -> failwith "Impossible: Too many pops"

let print_profile p =
  let counters = p.counters in
  let name = p.name in
  let ctr2string (ctr:counter) =
    let n = 1 in
    //let n = !max_ctr_len - (String.length ctr.name) in
    let rec mk_pad out n = if n = 0 then out else mk_pad (" " ^ out) (n - 1) in
    let pad = mk_pad "" n in
    Printf.sprintf "%s:%s\t %sms " ctr.name pad (string_of_int (int32 (!ctr.total_time).TotalMilliseconds)) in
  let all_keys = List.ofSeq (counters.Keys) in (* Hashtbl.fold (fun name ctr accum -> ctr::accum) counters [] in *)
  let all_ctrs = all_keys |> List.map (fun k -> snd <| counters.TryGetValue(k)) in
  //let all_ctrs = List.sortWith (fun c1 c2 -> if (!c2.total_time).TotalSeconds >= (!c1.total_time).TotalSeconds then 1 else -1) all_ctrs in
  let output = List.fold_left
    (fun accum c ->
      if !c.nstarts > 0 then Printf.printf "Warning: counter %s is unreliable; %d starts were not stopped\n" c.name !c.nstarts;
      accum ^ (ctr2string c)) (name + ": ") all_ctrs in
  Printf.printf "%s\n" output

let stop_profile name: profiler =
  let p = pop_stack () in
  if not (p.name = name) then 
    failwith "stack not matching";
  propogate_profile_info p;
  p

let profile' (f: unit -> 'b) (name:string) (ctrname:string) printout: 'b * int =
  let counters = (start_profile name).counters in
  try
    let _ = start_counter counters ctrname in
    let result = f () in
    let time = match stop_counter counters ctrname with
      | Some elapsed -> add_counter counters elapsed ctrname; int32 elapsed.TotalMilliseconds
      | _ -> 0 in
    let p = stop_profile name in
    if printout then
      print_profile p; 
    result, time
  with
    e when (ignore <| stop_counter counters ctrname; false) -> raise e (* to ensure a counter is
                                                        always stopped without messing up the stack trace *)

let profile  (f: unit -> 'b) (name:string) (ctrname:string) (printout:bool): 'b * int =
  if !profiling then profile' f name ctrname printout else BU.record_time f

let init_profiler () = profiling := true

let disable_profiler () = profiling := false