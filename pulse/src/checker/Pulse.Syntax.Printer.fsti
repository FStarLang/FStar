(*
   Copyright 2023 Microsoft Research

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

module Pulse.Syntax.Printer
open Pulse.Syntax.Base
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
open FStar.Pprint

val tot_or_ghost_to_string (eff:T.tot_or_ghost) : string
val name_to_string (f:R.name) : string
// val constant_to_string (c:constant) : string
val univ_to_string (u:universe) : string
val qual_to_string (q:option qualifier) : T.Tac string
val term_to_string (t:term) : T.Tac string
val binder_to_doc (b:binder) : T.Tac document
val term_to_doc (t:term) : T.Tac document
val binder_to_string (b:binder) : T.Tac string
val ctag_to_string (c:ctag) : string
val observability_to_string (obs:observability) : string
val effect_annot_to_string (e:effect_annot) : T.Tac string
val comp_to_string (c:comp) : T.Tac string
val term_list_to_string (sep:string) (t:list term): T.Tac string
val pattern_to_string (p:pattern) : T.Tac string
val st_term_to_string (t:st_term) : T.Tac string
val tag_of_term (t:term) : string
val tag_of_st_term (t:st_term) : string
val tag_of_comp (c:comp): T.Tac string
val print_st_head (t:st_term) : string
val print_skel (t:st_term) : string
val decl_to_string (d:decl) : T.Tac string
