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

module Pulse.Typing.Metatheory

open Pulse.Syntax
open Pulse.Typing


let tot_typing_weakening_single g t ty d x x_t = ()

let tot_typing_weakening_standard g t ty d g2 = ()

let st_typing_weakening g g' t c d g1 = ()

let st_typing_weakening_standard g t c d g1 = ()

let st_typing_weakening_end g g' t c d g'' = ()

let veq_weakening g g' v1 v2 d g1 = ()

let veq_weakening_end g g' v1 v2 d g'' = ()
