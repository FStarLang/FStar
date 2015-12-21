(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
// (c) Microsoft Corporation. All rights reserved
module FStar.Syntax.Print
open FStar.Syntax.Syntax
open FStar.Ident

val bv_to_string     : bv -> string
val lid_to_string    : lid -> string
val term_to_string   : term -> string
val uvar_to_string   : FStar.Unionfind.uvar<'a> -> string
val comp_to_string   : comp -> string
val tag_of_term      : term -> string
val lbname_to_string : lbname -> string
val pat_to_string    : pat -> string
val modul_to_string  : modul -> string
val lcomp_to_string  : lcomp -> string
val univ_to_string   : universe -> string
val sigelt_to_string : sigelt -> string
val binders_to_string: string -> binders ->string