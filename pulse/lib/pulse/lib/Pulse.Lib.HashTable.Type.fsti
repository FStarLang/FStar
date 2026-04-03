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

module Pulse.Lib.HashTable.Type
#lang-pulse

open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT

open Pulse.Lib.HashTable.Spec

type pos_us = n:SZ.t{SZ.v n > 0}

noeq
type ht_t ([@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] keyt:eqtype)
          ([@@@ Rust_generics_bounds ["Clone"]] valt:Type) = {
  sz : pos_us;
  hashf: keyt -> SZ.t;
  contents : V.vec (cell keyt valt);
}
