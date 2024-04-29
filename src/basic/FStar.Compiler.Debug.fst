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

module FStar.Compiler.Debug

module BU = FStar.Compiler.Util

let toggle_list : ref (list (string & ref bool)) =
  BU.mk_ref []

let register_toggle (k : string) : ref bool =
  let r = BU.mk_ref false in
  toggle_list := (k, r) :: !toggle_list;
  r

let get_toggle (k : string) : ref bool =
  match List.tryFind (fun (k', _) -> k = k') !toggle_list with
  | Some (_, r) -> r
  | None -> register_toggle k

let list_all_toggles () : list string =
  List.map fst !toggle_list

let anyref = BU.mk_ref false
let any () = !anyref
let enable () = anyref := true

let dbg_level = BU.mk_ref 0

let low     () = !dbg_level >= 1
let medium  () = !dbg_level >= 2
let high    () = !dbg_level >= 3
let extreme () = !dbg_level >= 4

let set_level_low     () = dbg_level := 1
let set_level_medium  () = dbg_level := 2
let set_level_high    () = dbg_level := 3
let set_level_extreme () = dbg_level := 4

let enable_toggles (keys : list string) : unit =
  if Cons? keys then enable ();
  keys |> List.iter (fun k ->
    if k = "Low" then set_level_low ()
    else if k = "Medium" then set_level_medium ()
    else if k = "High" then set_level_high ()
    else if k = "Extreme" then set_level_extreme ()
    else
    let t = get_toggle k in
    t := true
  )

let disable_all () : unit =
  anyref := false;
  dbg_level := 0;
  List.iter (fun (_, r) -> r := false) !toggle_list
