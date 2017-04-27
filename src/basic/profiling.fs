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
let profiling = ref false

module On = struct

let startClock, messageWithTime =
  let s = ref None in
  let start () = match !s with None -> failwith "Clock not initialized" | Some s -> s in
  (fun () -> s := Some System.DateTime.Now),
  (fun msg ->
    let elapsed = System.DateTime.Now - (start()) in
    Printf.printf "%f: %s\n" (elapsed.TotalSeconds) msg)

exception ProfilingException of string

type counter = {name:string; total_time:System.TimeSpan ref; nstarts:int ref; started_at:System.DateTime ref;}
let max_ctr_len = ref 0
let counters = new System.Collections.Generic.Dictionary<string, counter>()
let ts0 = System.TimeSpan(0L)
let t0 = System.DateTime.Now

let find_counter n =
  let (hit, res) = counters.TryGetValue(n) in
    if hit then Some res
    else None

let now () = System.DateTime.Now

let new_counter name =
  match find_counter name with
    | Some _ ->
(*         let _ = Util.pr "Already found counter %s\n" name in *)
          name
    | None ->
(*         let _ = Util.pr "Creating counter %s\n" name in *)
        let ctr = {name=name; total_time=ref ts0; nstarts=ref 0; started_at=ref t0} in
        let _ = counters.Add(name, ctr) in
          if String.length name > !max_ctr_len then
            max_ctr_len := String.length name;
          name

let rec add_counter elapsed name =
  match find_counter name with
    | Some ctr ->
        incr ctr.nstarts;
        ctr.total_time := elapsed + !ctr.total_time
    | None ->
        ignore <| new_counter name;
        add_counter elapsed name

let rec start_counter name =
  match find_counter name with
    | Some ctr ->
        incr ctr.nstarts;
        if !(ctr.nstarts) = 1 then ctr.started_at := now()
    | None -> ignore <| new_counter name; start_counter name

let stop_counter name : option<System.TimeSpan> =
  match find_counter name with
    | Some ctr ->
        decr ctr.nstarts;
        if !(ctr.nstarts) < 0 then raise (ProfilingException ("Starts and ends on counter "^name^" don't match up"));
        if !(ctr.nstarts) = 0 then
          let elapsed = now() - !ctr.started_at in
            ctr.total_time := elapsed + !ctr.total_time;
            Some elapsed
        else None
    | None -> raise (ProfilingException ("Counter " ^name^ " does not exist"))

let profile (f: unit -> 'b) (ctrname:string) : 'b =
  try
    let _ = start_counter ctrname in
    let result = f () in
    let _ = stop_counter ctrname in
      result
  with
      e when (ignore <| stop_counter ctrname; false) -> raise e (* to ensure a counter is
                                                        always stopped without messing up the stack trace *)
let profilel (f: unit -> 'b) (ctrs:list<string>) : 'b =
  try
    let _ = List.iter start_counter ctrs in
    let result = f () in
    let _ = List.iter (fun x -> ignore (stop_counter x)) ctrs in
      result
  with
      e when (List.iter (fun x -> ignore (stop_counter x)) ctrs; false) -> raise e (* to ensure a counter is
                                                        always stopped without messing up the stack trace *)
let prof ctrname (f:Lazy<'b>) : 'b =
  try
    let _ = start_counter ctrname in
    let result = f.Force() in
    let _ = stop_counter ctrname in
      result
  with
      e when (ignore <| stop_counter ctrname; false) -> raise e (* to ensure a counter is
                                                        always stopped without messing up the stack trace *)
let dprof ctrname g (f:Lazy<'b>) : 'b =
  try
    let _ = start_counter ctrname in
    let result = f.Force() in
    let _ = match stop_counter ctrname with
      | Some elapsed -> add_counter elapsed (g result)
      | _ -> () in
      result
  with
      e when (ignore <| stop_counter ctrname; false) -> raise e (* to ensure a counter is
                                                        always stopped without messing up the stack trace *)
let print_profile () =
  let ctr2string ctr =
    let n = !max_ctr_len - (String.length ctr.name) in
    let rec mk_pad out n = if n = 0 then out else mk_pad (" " ^ out) (n - 1) in
    let pad = mk_pad "" n in
    Printf.sprintf "%s:%s\t %fmin %fsec\n" ctr.name pad (!ctr.total_time).TotalMinutes (!ctr.total_time).TotalSeconds in
  let all_keys = List.ofSeq (counters.Keys) in (* Hashtbl.fold (fun name ctr accum -> ctr::accum) counters [] in *)
  let all_ctrs = all_keys |> List.map (fun k -> snd <| counters.TryGetValue(k)) in
  let all_ctrs = List.sortWith (fun c1 c2 -> if (!c2.total_time).TotalSeconds >= (!c1.total_time).TotalSeconds then 1 else -1) all_ctrs in
  let output = List.fold_left
    (fun accum c ->
      if !c.nstarts > 0 then Printf.printf "Warning: counter %s is unreliable; %d starts were not stopped\n" c.name !c.nstarts;
      accum ^ (ctr2string c)) "" all_ctrs in
  Printf.printf "%s" output
end

module Off = struct
let startClock () = ()
let messageWithTime s = ()
let new_counter n = n
let start_counter n = ()
let stop_counter n = None
let profile (f: unit -> 'b) (ctrname:string) : 'b = f ()
let profilel (f: unit -> 'b) (ctrs:list<string>) : 'b = f ()
let print_profile () = ()
let prof c (f:Lazy<'a>) = f.Force()
let dprof c g (f:Lazy<'a>) = f.Force()
end

let startClock () =
  if !profiling
  then On.startClock ()
  else Off.startClock ()
let messageWithTime s =
  if !profiling
  then On.messageWithTime s
  else Off.messageWithTime s
let new_counter n = On.new_counter n
let start_counter n = if !profiling then On.start_counter n else Off.start_counter n
let stop_counter n : option<System.TimeSpan> = if !profiling then On.stop_counter n else Off.stop_counter n
let profile  (f: unit -> 'b) (ctrname:string) : 'b =
  if !profiling then On.profile f ctrname else Off.profile f ctrname
let profilel (f: unit -> 'b) (ctrs:list<string>) : 'b =
  if !profiling then On.profilel f ctrs else Off.profilel f ctrs
let prof (ctr:string) (f:Lazy<'a>) : 'a =
  if !profiling then On.prof ctr f else Off.prof ctr f
let dprof (ctr:string) g (f:Lazy<'a>) : 'a =
  if !profiling then On.dprof ctr g f else Off.dprof ctr g f
let print_profile () =
  if !profiling
  then
    (Printf.printf "Printing profile\n";
     flush stdout;
     On.print_profile ())
  else Off.print_profile ()

let (^^) ctr f = prof ctr f
