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
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Syntax.Naming
open Pulse.Typing

val tot_typing_ln (#g:_) (#e:_) (#t:_)
                  (d:tot_typing g e t)
  : Lemma (ln e /\ ln t)

val comp_typing_ln (#g:_) (#c:_) (#u:_)
                   (d:comp_typing g c u)
  : Lemma (ln_c c)

val st_typing_ln  (#g:_) (#t:_) (#c:_)
                  (st:st_typing g t c)
  : Lemma (ln_st t /\ ln_c c)
