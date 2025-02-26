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

module Pulse.Lib.GhostWitness
#lang-pulse

open Pulse.Lib.Pervasives

val ghost_witness (a:Type u#0) (_:squash a) :
  stt_ghost a emp_inames emp (fun _ -> emp)

val ghost_witness2 (a:Type u#4) (_:squash a) :
  stt_ghost a emp_inames emp (fun _ -> emp)

val ghost_witness_exists (a:Type u#0) :
  stt_ghost a emp_inames (pure (exists (x:a). True)) (fun _ -> emp)

val ghost_witness_exists2 (a:Type u#4) :
  stt_ghost a emp_inames (pure (exists (x:a). True)) (fun _ -> emp)
