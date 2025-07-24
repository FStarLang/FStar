(*
   Copyright 2008-2020 Microsoft Research

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

module FStarC.Debug

open FStarC.Effect

(* Mutable state *)
let anyref = mk_ref false
let _debug_all : ref bool = mk_ref false
let toggle_list : ref (PSMap.t (ref bool)) = mk_ref (PSMap.empty ())
let dbg_level = mk_ref 0

type saved_state = {
  toggles : list (string & bool);
  any     : bool;
  all     : bool;
  level   : int;
}

let snapshot () : saved_state = {
  toggles = PSMap.fold !toggle_list (fun k r acc -> (k, !r) :: acc) [];
  any     = !anyref;
  all     = !_debug_all;
  level   = !dbg_level;
}

let register_toggle (k : string) : ref bool =
  let r = mk_ref false in
  if !_debug_all then
    r := true;
  toggle_list := PSMap.add !toggle_list k r;
  r

let get_toggle (k : string) : ref bool =
  match PSMap.try_find !toggle_list k with
  | Some r -> r
  | None -> register_toggle k

let restore (snapshot : saved_state) : unit =
  (* Set everything to false, then set all the saved ones
  to true. *)
  PSMap.iter !toggle_list (fun k r -> r := false);
  snapshot.toggles |> List.iter (fun (k, b) ->
    let r = get_toggle k in
    r := b);
  (* Also restore these references. *)
  anyref := snapshot.any;
  _debug_all := snapshot.all;
  dbg_level := snapshot.level;
  ()

let list_all_toggles () : list string =
  PSMap.keys !toggle_list

let any () = !anyref || !_debug_all

let tag (s:string) =
  if any () then
    Format.print_string ("DEBUG:" ^  s ^ "\n")

let enable () = anyref := true

let low     () = !dbg_level >= 1 || !_debug_all
let medium  () = !dbg_level >= 2 || !_debug_all
let high    () = !dbg_level >= 3 || !_debug_all
let extreme () = !dbg_level >= 4 || !_debug_all

let set_level_low     () = dbg_level := 1
let set_level_medium  () = dbg_level := 2
let set_level_high    () = dbg_level := 3
let set_level_extreme () = dbg_level := 4

let enable_toggles (keys : list string) : unit =
  if Cons? keys then
    enable ();
  keys |> List.iter (fun k ->
    match k with
    | "Low" ->     set_level_low ()
    | "Medium" ->  set_level_medium ()
    | "High" ->    set_level_high ()
    | "Extreme" -> set_level_extreme ()
    | _ ->
      if String.length k > 0 && String.get k 0 = '-' then
        let k = String.substring k 1 (String.length k - 1) in
        let t = get_toggle k in
        t := false
      else
        let t = get_toggle k in
        t := true
  )

let disable_all () : unit =
  anyref := false;
  dbg_level := 0;
  PSMap.iter !toggle_list (fun k r -> r := false)

let set_debug_all () : unit =
  _debug_all := true;
  dbg_level := 4;
  PSMap.iter !toggle_list (fun k r -> r := true)
