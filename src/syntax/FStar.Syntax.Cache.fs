(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Syntax.Cache

open FStar.ST
open FStar.All
(* Type definitions for the core AST *)

(* Prims is used for bootstrapping *)
open Prims
open FStar
open FStar.Util
open FStar.Range
open FStar.Ident
open FStar.Dyn

module S = FStar.Syntax.Syntax

type cache<'a> = imap<(S.term * 'a)>

let create (_:unit) = imap_create 100

let add (c:cache<'a>) (t:S.term) (v:'a) : unit =
  let hash = generic_hash t in
  imap_add c hash (t, v)

//an optional comparator function for additional checking on a cache hit
let find (c:cache<'a>) (t:S.term) (f_opt:option<(S.term -> S.term -> bool)>) : option<'a> =
  t |> generic_hash |> imap_try_find c |> (fun v_opt ->
    match v_opt with
    | None         -> None
    | Some (t', v) ->
      (match f_opt with
       | None   -> Some v
       | Some f -> if f t t' then Some v else None))
