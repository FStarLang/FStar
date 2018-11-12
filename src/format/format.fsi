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
(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Format

(* -------------------------------------------------------------------- *)
type doc

(* -------------------------------------------------------------------- *)
val empty  : doc
val text   : string -> doc
val num    : int -> doc
val cat    : doc -> doc -> doc
val nest   : int -> doc -> doc
val group  : doc -> doc

val break_ : int -> doc
val break0 : doc
val break1 : doc

val hardline : doc

(* -------------------------------------------------------------------- *)
val cat1    : doc -> doc -> doc
val reduce  : list<doc> -> doc
val reduce1 : list<doc> -> doc
val combine : doc -> list<doc> -> doc
val groups  : list<doc> -> doc
val align   : list<doc> -> doc
val hbox    : doc -> doc

(* -------------------------------------------------------------------- *)
val enclose  : doc -> doc -> doc -> doc
val parens   : doc -> doc
val brackets : doc -> doc
val cbrackets : doc -> doc

(* -------------------------------------------------------------------- *)
val pretty : int -> doc -> string
