(*
   Copyright 2008-2026 Microsoft Research

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

(* The Cherry implementation, on top of FStar.Pprint-c.cherry.fst.  The
   combinators recurse themselves rather than going through FStarC.List. *)

open FStarC.Effect
open FStarC.BaseTypes
open FStar.Pprint

let doc_of_char c = FStar.Pprint.doc_of_char c

let rec concat_map_acc (#a:Type) (acc:document) (f:a -> ML document) (xs:list a)
  : ML document =
  match xs with
  | [] -> acc
  | x :: tl -> concat_map_acc (acc ^^ f x) f tl

let concat_map f xs = concat_map_acc empty f xs

let rec separate_map_rest (#a:Type) (sep acc:document) (f:a -> ML document) (xs:list a)
  : ML document =
  match xs with
  | [] -> acc
  | x :: tl -> separate_map_rest sep (acc ^^ sep ^^ f x) f tl

let separate_map sep f xs =
  match xs with
  | [] -> empty
  | x :: tl -> separate_map_rest sep (f x) f tl

let optional f o =
  match o with
  | None -> empty
  | Some x -> f x

let split ok s = FStar.Pprint.split ok s

let rec map_docs (#a:Type) (f:a -> ML document) (xs:list a) : ML (list document) =
  match xs with
  | [] -> []
  | x :: tl -> let d = f x in d :: map_docs f tl

let flow_map sep f docs = flow sep (map_docs f docs)

let pretty_string rfrac width doc = FStar.Pprint.pretty_string (float64_of_float rfrac) width doc

let pretty_out_channel rfrac width doc ch =
  FStarC.Util.fprint ch "%s" [FStar.Pprint.pretty_string (float64_of_float rfrac) width doc];
  FStarC.Util.flush ch
