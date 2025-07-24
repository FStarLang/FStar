(*
   Copyright 2008-2025 Nikhil Swamy and Microsoft Research

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
module FStarC.Stats

open FStarC.Effect
open FStarC.Class.Monoid
open FStarC.Class.Show

let enabled = alloc false
let ever_enabled = alloc false

type stat = {
  ns_tree  : int;
  ns_exn   : int;
  ns_sub   : int;
  ncalls   : int;
}

instance _ : monoid stat = {
  mzero = {
    ns_tree = 0;
    ns_exn = 0;
    ns_sub = 0;
    ncalls = 0;
  };
  mplus = (fun s1 s2 ->
    {
      ns_tree  = s1.ns_tree + s2.ns_tree;
      ns_exn   = s1.ns_exn + s2.ns_exn;
      ns_sub   = s1.ns_sub + s2.ns_sub;
      ncalls   = s1.ncalls + s2.ncalls;
    });
}

(* the ref bool marks whether a given key is currently
   being recorded. This is so we avoid double counting
   the time taken by reentrant calls. *)
let st : SMap.t (ref bool & stat) = SMap.create 10

(* Current stats we are logging. This is used to distinguish
   "tree" time (all the time taken by some call)
   vs "point" time (time taken by some call, subtracting
   the time in subcalls, if any). *)
let stack : ref (list string) = mk_ref []

let r_running (k : string) : ref bool =
  match SMap.try_find st k with
  | None ->
    let r = alloc false in
    SMap.add st k (r, mzero);
    r
  | Some (r, _) ->
    r

let add (k : string) (s1 : stat) : unit =
  let (r, s0) =
    match SMap.try_find st k with
    | None -> (alloc false, mzero)
    | Some rs -> rs
  in
  SMap.add st k (r, mplus s0 s1)

let do_record
  (key : string)
  (f : unit -> 'a)
  : 'a
=
  stack := key :: !stack;
  let running = r_running key in
  let was_running = !running in
  running := true;
  let t0 = Timing.now_ns () in
  let resexn =
    try Inr (f ())
    with | e -> Inl e
  in
  running := was_running;
  let t1 = Timing.now_ns () in
  let ns = Timing.diff_ns t0 t1 in
  stack := List.tl !stack;
  if not was_running then (
    add key { mzero with ns_tree = ns };
    (* Take time out of the parent, if any. *)
    begin match !stack with
    | [] -> ()
    | k_par::_ -> add k_par { mzero with ns_sub = ns }
    end
  );
  add key { mzero with ncalls = 1 };
  match resexn with
  | Inr r ->
    r
  | Inl e ->
    add key { mzero with ns_exn = ns };
    raise e

let record key f =
  if !enabled then
    do_record key f
  else
    f ()

let lpad (len:int) (s:string) : string =
  let l = String.length s in
  if l >= len then s else String.make (len - l) ' ' ^ s

let max x y =
  if x > y then x else y

let print_all () : string =
  let keys = SMap.keys st in
  let points = List.map (fun k -> k, snd <| Some?.v <| SMap.try_find st k) keys in
  (* Sort by (point) time. *)
  let points =
    points |>
    Class.Ord.sort_by (fun (_, s1) (_, s2) ->
      (s2.ns_tree - s2.ns_sub) `Class.Ord.cmp` (s1.ns_tree - s1.ns_sub))
  in
  let longest_key = List.fold_left (fun acc (k, _) -> max acc (String.length k)) 20 points in
  let pr1 (p : (string & stat)) : string =
    let k, st = p in
    Format.fmt5 "  %s  %s %s ms %s ms %s ms"
      (lpad longest_key k)
      (lpad 8 (show st.ncalls))
      (lpad 6 (show (st.ns_tree  / 1000000)))
      (lpad 6 (show ((st.ns_tree - st.ns_sub) / 1000000)))
      (lpad 6 (show (st.ns_exn   / 1000000)))
  in
  Format.fmt5 "  %s  %s %s %s %s" (lpad longest_key "key") (lpad 8 "calls") (lpad 9 "tree") (lpad 9 "point") (lpad 9 "exn") ^ "\n" ^
  (points |> List.map pr1 |> String.concat "\n")
