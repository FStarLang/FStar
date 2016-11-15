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
module FStar.Pprint

open Prims
open FStar.Char
open FStar.String

new type document // SI: check use of [new]

val empty: document

val char: 	char -> document

val string: string -> document

val substring: string -> int -> int -> document

val fancystring: string -> int -> document

val fancysubstring : string -> int -> int -> int -> document

val utf8string: string -> document

val hardline: document

val blank: int -> document

val break_: int -> document

val op_Hat_Hat: document -> document -> document

val nest: int -> document -> document

val group: document -> document

val column: (int -> document) -> document

val nesting: (int -> document) -> document

val position : (bol:int -> line:int -> column:int -> document) -> document

val ifflat: document -> document -> document

val lparen: document
val rparen: document
val langle: document
val rangle: document
val lbrace: document
val rbrace: document
val lbracket: document
val rbracket: document
val squote: document
val dquote: document
val bquote: document
val semi: document
val colon: document
val comma: document
val space: document
val dot: document
val sharp: document
val slash: document
val backslash: document
val equals: document
val qmark: document
val tilde: document
val at: document
val percent: document
val dollar: document
val caret: document
val ampersand: document
val star: document
val plus: document
val minus: document
val underscore: document
val bang: document
val bar: document

val precede: document -> document -> document

val terminate: document -> document -> document

val enclose: document -> document -> document -> document

val squotes: document -> document
val dquotes: document -> document
val bquotes: document -> document
val braces: document -> document
val parens: document -> document
val angles: document -> document
val brackets: document -> document

val twice: document -> document

val repeat: int -> document -> document

val concat: document list -> document

val separate: document -> document list -> document

val concat_map: ('a -> document) -> 'a list -> document

val separate_map: document -> ('a -> document) -> 'a list -> document

val separate2: document -> document -> document list -> document

val optional: ('a -> document) -> 'a option -> document

val lines: string -> document list

val arbitrary_string: string -> document

val words: string -> document list

val split: (char -> bool) -> string -> document list

val flow: document -> document list -> document

val flow_map: document -> ('a -> document) -> 'a list -> document

val url: string -> document

val align: document -> document

val hang: int -> document -> document

val prefix: int -> int -> document -> document -> document

val jump: int -> int -> document -> document

val infix: int -> int -> document -> document -> document -> document

val surround: int -> int -> document -> document -> document -> document

val soft_surround: int -> int -> document -> document -> document -> document

val surround_separate: int -> int -> document -> document -> document -> document -> document list -> document

val surround_separate_map: int -> int -> document -> document -> document -> document -> ('a -> document) -> 'a list -> document
