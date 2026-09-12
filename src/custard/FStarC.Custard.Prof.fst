(*
   Copyright 2008-2025 Microsoft Research

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

module FStarC.Custard.Prof

open FStarC
open FStarC.Effect
open FStarC.Class.Show

module BU   = FStarC.Util
module SMap = FStarC.SMap

type counter = {
  c_time:  ref int;                     (* exclusive nanoseconds *)
  c_calls: ref int;
}

let counters : SMap.t counter = SMap.create 50

let get (name:string) : ML counter =
  match SMap.try_find counters name with
  | Some c -> c
  | None ->
    let c = { c_time = mk_ref 0; c_calls = mk_ref 0 } in
    SMap.add counters name c; c

(* The time charged to the *caller* by everything measured since the caller
   started.  Each [timed] frame saves the running total, zeroes it, and adds
   its own whole elapsed time back on the way out; what it finds in the cell
   is exactly what its own children took. *)
let children : ref int = mk_ref 0

(* [Options.profile_enabled] is a namespace-filter match on a string, which is
   more than a counter on a function called a million times can afford. *)
let enabled : ref (option bool) = mk_ref None

let is_enabled () : ML bool =
  match !enabled with
  | Some b -> b
  | None ->
    let b = Options.profile_enabled None "FStarC.Custard" in
    enabled := Some b; b

let timed (name:string) (f : unit -> ML 'a) : ML 'a =
  if not (is_enabled ()) then f ()
  else
    let c = get name in
    let saved = !children in
    children := 0;
    let res, elapsed = Timing.record_ns f in
    let mine = !children in
    children := saved + elapsed;
    c.c_time := !c.c_time + elapsed - mine;
    c.c_calls := !c.c_calls + 1;
    res

let count (name:string) : ML unit =
  let c = get name in
  c.c_calls := !c.c_calls + 1

let report () : ML unit =
  if not (is_enabled ()) then () else begin
    let rows = SMap.fold counters (fun k v acc -> (k, v) :: acc) [] in
    let rows = BU.sort_with (fun (_, a) (_, b) -> !b.c_time - !a.c_time) rows in
    Format.print_string "Custard, exclusive time by counter:\n";
    rows |> List.iter (fun (k, c) ->
      Format.print3 "  %s ms\t%s\t(%s calls)\n"
        (show (!c.c_time / 1000000)) k (show !c.c_calls));
    SMap.clear counters
  end
