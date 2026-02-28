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

module Pulse.Typing.LN
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

val tot_typing_ln (g:env) (e:term) (t:term)
  : Lemma (ln e /\ ln t)

val comp_typing_ln (g:env) (c:comp) (u:universe)
  : Lemma (ln_c c)

val st_typing_ln  (g:env) (t:st_term) (c:comp)
  : Lemma (ln_st t /\ ln_c c)
