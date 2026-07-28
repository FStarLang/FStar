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

module Pulse.Show

open FStar.Tactics.V2
open FStar.Tactics.NamedView
open Pulse.Typing
open Pulse.Syntax.Base

class tac_showable (a:Type) = {
  show : a -> Tac string;
}

instance val tac_showable_string : tac_showable string
instance val tac_showable_unit : tac_showable unit
instance val tac_showable_bool : tac_showable bool
instance val tac_showable_int : tac_showable int
instance val tac_showable_option (a:Type) (_ : tac_showable a) 
  : tac_showable (option a)

instance val tac_showable_list (a:Type) (_ : tac_showable a)
  : tac_showable (list a)

instance val tac_showable_either (a b:Type) (_ : tac_showable a) (_ : tac_showable b)
  : tac_showable (either a b)

instance val tac_showable_pp_name_t : tac_showable FStar.Reflection.Typing.pp_name_t
instance val tac_showable_ppname : tac_showable ppname
instance val tac_showable_ctag : tac_showable ctag
instance val tac_showable_term : tac_showable term
instance val tac_showable_aqualv : tac_showable aqualv
instance val tac_showable_st_term : tac_showable st_term
instance val tac_showable_universe : tac_showable universe
instance val tac_showable_comp : tac_showable comp
instance val tac_showable_env : tac_showable env
instance val tac_showable_observability : tac_showable observability
instance val tac_showable_effect_annot : tac_showable effect_annot
instance val tac_showable_post_hint_t : tac_showable post_hint_t
instance val tac_showable_namedv : tac_showable Reflection.namedv

instance val tac_showable_range  : tac_showable Range.range

instance val tac_showable_tuple2 (a b : Type) (_:tac_showable a) (_:tac_showable b) : tac_showable (a & b)
instance val tac_showable_tuple3 (a b c : Type) (_:tac_showable a) (_:tac_showable b) (_:tac_showable c) : tac_showable (a & b & c)
instance val tac_showable_tuple4 (a b c d : Type) (_:tac_showable a) (_:tac_showable b) (_:tac_showable c) (_:tac_showable d) : tac_showable (a & b & c & d)
instance val tac_showable_tuple5 (a b c d e : Type) (_:tac_showable a) (_:tac_showable b) (_:tac_showable c) (_:tac_showable d) (_:tac_showable e) : tac_showable (a & b & c & d & e)
instance val tac_showable_tuple6 (a b c d e f : Type) (_:tac_showable a) (_:tac_showable b) (_:tac_showable c) (_:tac_showable d) (_:tac_showable e) (_:tac_showable f) : tac_showable (a & b & c & d & e & f)
instance val tac_showable_tuple7 (a b c d e f g : Type) (_:tac_showable a) (_:tac_showable b) (_:tac_showable c) (_:tac_showable d) (_:tac_showable e) (_:tac_showable f) (_:tac_showable g) : tac_showable (a & b & c & d & e & f & g)

instance val tac_showable_tot_or_ghost : tac_showable tot_or_ghost
instance val tac_showable_qualifier    : tac_showable qualifier
instance val tac_showable_issue        : tac_showable FStar.Issue.issue
