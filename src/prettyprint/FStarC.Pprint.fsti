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

(* This is really an extension of the basic FStar.Pprint module exposed to
userspace. The main reason this layer exists is that the F* compiler works in
the ALL effect, and hence cannot use the higher-order combinators of this
module. This module here provides combinators usable in the ALL effect. 

There are also mismatches between the types of char and float between the compiler
and userspace, so we also shadow all functions mentioning those types. *)
include FStar.Pprint

(** [doc_of_char c] is a document that consists of the single character [c]. This
    character must not be a newline. *)
val doc_of_char: FStar.Char.char -> document

(** [concat_map f xs] is equivalent to [concat (List.map f xs)]. *)
val concat_map: ('a -> document) -> list 'a -> document

(** [separate_map sep f xs] is equivalent to [separate sep (List.map f xs)]. *)
val separate_map: document -> ('a -> document) -> list 'a -> document

(** [optional f None] is the empty document. [optional f (Some x)] is
    the document [f x]. *)
val optional: ('a -> document) -> option 'a -> document

(** [split ok s] splits the string [s] before and after every occurrence of a
    character that satisfies the predicate [ok]. The substrings thus obtained
    are turned into documents, and a list of documents is returned. No
    information is lost: the concatenation of the documents yields the
    original string.  This code is not UTF-8 aware. *)
val split: (FStar.Char.char -> bool) -> string -> list document

(** [flow_map sep f docs] is equivalent to [flow sep (List.map f docs)]. *)
val flow_map: document -> ('a -> document) -> list 'a -> document

// Expose underlying Renderer.pretty implementations (avoid inner modules).
// [pretty_string] uses ToBuffer:RENDERER implementation;
// [print_out_channel] uses the ToChannel:RENDERER one.
val pretty_string : float -> int -> document -> string
val pretty_out_channel : float -> int -> document -> FStarC.Util.out_channel -> unit
