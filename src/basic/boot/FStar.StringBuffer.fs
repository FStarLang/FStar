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
module FStar.StringBuffer
open FStar.All
open Prims
open FStar.BigInt
open System.Text

type t =
  | Mk of StringBuilder

let create (i:FStar.BigInt.t) = Mk (new StringBuilder(to_int i))

let add (s:string) t =
    let (Mk sb) = t in
    let _ = sb.Append(s) in
    t

let contents (Mk sb) = sb.ToString()

let clear t =
    let (Mk sb) = t in
    let _ = sb.Clear() in
    t

let output_channel chan t =
    let s = contents t in
    Printf.fprintf chan "%s" s