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

module Pulse.Checker.Match

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base

module T = FStar.Tactics.V2

val open_st_term_bs (t:st_term) (bs:list binding) : st_term 

val check
        (g:env)
        (pre:term)
        (pre_typing: tot_typing g pre tm_slprop)
        (post_hint:post_hint_for_env g)
        (res_ppname:ppname)
        (sc:term)
        (brs:list branch)
        (check:check_t)
  : T.Tac (checker_result_t g pre (PostHint post_hint))
