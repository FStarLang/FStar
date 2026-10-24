(*
   Copyright 2016 Microsoft Research

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
module FStarC.Pprint

open FStarC.Effect
open FStarC.BaseTypes
open FStar.Pprint

let doc_of_char c = FStar.Pprint.doc_of_char c

let concat_map f xs = concat (List.map f xs)

let separate_map sep f xs = separate sep (List.map f xs)

let optional f o =
  match o with
  | None -> empty
  | Some x -> f x

let split ok s = FStar.Pprint.split ok s

let flow_map sep f docs = flow sep (List.map f docs)

[@@custard_extern "int"]
private assume new type ocaml_int : Type0

[@@custard_extern "Z.to_int"]
private assume val oi (n:int) : ocaml_int

[@@custard_extern "(fun rfrac width doc -> let buf = Buffer.create 0 in PPrint.ToBuffer.pretty rfrac width buf doc; Buffer.contents buf)"]
private assume val ocaml_pretty_string : float -> ocaml_int -> document -> string

let pretty_string rfrac width doc = ocaml_pretty_string rfrac (oi width) doc

[@@custard_extern "(fun rfrac width doc ch -> PPrint.ToChannel.pretty rfrac width ch doc; Stdlib.flush ch)"]
private assume val ocaml_pretty_out_channel :
  float -> ocaml_int -> document -> FStarC.Util.out_channel -> ML unit

let pretty_out_channel rfrac width doc ch =
  ocaml_pretty_out_channel rfrac (oi width) doc ch
