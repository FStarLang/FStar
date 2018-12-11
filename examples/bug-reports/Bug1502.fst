(*
   Copyright 2008-2018 Microsoft Research

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
module Bug1502

#set-options "--initial_fuel 0 --initial_ifuel 0 --max_fuel 0 --max_ifuel 0"

type ty =
  | TGhost
  | TBuffer

type arg = string * ty

let is_buffer arg :Tot bool = let _, ty = arg in TBuffer? ty

let rec liveness (args:list arg) :Tot string =
  let args = List.Tot.Base.filter is_buffer args in
  let rec aux args = "" in
  aux args

let disjoint (args:list arg) :Tot string = let args = List.Tot.Base.filter is_buffer args in ""
