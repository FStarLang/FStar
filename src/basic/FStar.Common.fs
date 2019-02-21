(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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

module FStar.Common
open FStar.String
open FStar.ST
open FStar.All
module BU = FStar.Util

let has_cygpath =
    try
        let t_out = BU.run_process "has_cygpath" "which" ["cygpath"] None in
        BU.trim_string t_out = "/usr/bin/cygpath"
    with
    | _ -> false

//try to convert filename passed from the editor to mixed path
//that works on both cygwin and native windows
//noop if not on cygwin
//on cygwin emacs this is required

let try_convert_file_name_to_mixed =
  let cache = BU.smap_create 20 in
  fun (s:string) ->
    if has_cygpath
    && BU.starts_with s "/" then
      match BU.smap_try_find cache s with
      | Some s ->
          s
      | None ->
          let label = "try_convert_file_name_to_mixed" in
          let out = BU.run_process label "cygpath" ["-m"; s] None |> BU.trim_string in
          BU.smap_add cache s out;
          out
    else
      s

let snapshot (push: 'a -> 'b) (stackref: ref<list<'c>>) (arg: 'a) : (int * 'b) = BU.atomically (fun () ->
  let len = List.length !stackref in
  let arg' = push arg in
  (len, arg'))

let rollback (pop: unit -> 'a) (stackref: ref<list<'c>>) (depth: option<int>) =
  let rec aux n =
    if n <= 0 then failwith "Too many pops"
    else if n = 1 then pop ()
    else (ignore (pop ()); aux (n - 1)) in
  let curdepth = List.length !stackref in
  let n = match depth with Some d -> curdepth - d | None -> 1 in
  BU.atomically (fun () -> aux n)

// This function is separate to make it easier to put breakpoints on it
let raise_failed_assertion msg =
  failwith (BU.format1 "Assertion failed: %s" msg)

let runtime_assert b msg =
  if not b then raise_failed_assertion msg

let string_of_list (f : 'a -> string) (l : list<'a>) : string =
  "[" ^ String.concat ", " (List.map f l) ^ "]"

let list_of_option (o:option<'a>) : list<'a> =
    match o with
    | None -> []
    | Some x -> [x]

let string_of_option f = function
  | None -> "None"
  | Some x -> "Some " ^ f x

open FStar.Util
type thunk<'a> = ref<(Util.either<(unit -> 'a), 'a>)>
let mk_thunk (f:unit -> 'a) : thunk<'a> = Util.mk_ref (Util.Inl f)
let force_thunk (t:thunk<'a>) =
    match !t with
    | Inr a -> a
    | Inl f ->
      let a = f () in
      t := Inr a;
      a

(* Was List.init, but F* doesn't have this in ulib *)
let tabulate (n:int) (f : int -> 'a) : list<'a> =
  let rec aux i =
    if i < n
    then f i :: aux (i + 1)
    else []
  in aux 0
