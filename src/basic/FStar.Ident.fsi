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
module FStar.Ident
open Prims
open FStar.ST
open FStar.All
open FStar.Range

type ident = {idText:string;
              idRange:Range.range}
type lident = {ns:list<ident>; //["FStar"; "Basic"]
               ident:ident;    //"lident"
               nsstr:string; // Cached version of the namespace
               str:string} // Cached version of string_of_lid

type path = list<string>
type lid = lident

val mk_ident            : (string * Range.range) -> ident
val reserved_prefix     : string
val gen                 : Range.range -> ident
val id_of_text          : string -> ident

val text_of_id          : ident -> string
val text_of_path        : path -> string
val path_of_text        : string -> path
val path_of_ns          : list<ident> -> path
val path_of_lid         : lident -> path
val ids_of_lid          : lident -> list<ident>
val range_of_id         : ident -> Range.range

val lid_of_ns_and_id    : list<ident> -> ident -> lident
val lid_of_ids          : list<ident> -> lident
val lid_of_str          : string -> lident
val lid_of_path         : path -> Range.range -> lident

val text_of_lid         : lident -> string

val lid_equals          : lident -> lident -> bool
val ident_equals        : ident -> ident -> bool
val range_of_lid        : lident -> Range.range
val set_lid_range       : lident -> Range.range -> lident
val lid_add_suffix      : lident -> string -> lident

val ml_path_of_lid      : lident -> string
val string_of_ident     : ident -> string
val string_of_lid       : lident -> string
