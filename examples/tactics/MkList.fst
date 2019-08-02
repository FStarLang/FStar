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
module MkList

(* Makes top-level list definitions annotated by their length *)

open FStar.Tactics
open FStar.Tactics.Derived

let constant_list (name: string) (l: list UInt8.t): Tac unit =
  let len = FStar.List.length l in
  let t = `(FStar.List.llist UInt8.t (`@len)) in
  let fv = pack_fv (cur_module () @ [ name ]) in
  let se = pack_sigelt (Sg_Let false fv [] t (quote l)) in
  exact (quote ([ se ]))

%splice[] (constant_list "l1" [ 1uy ])
%splice[] (constant_list "l2" [ 1uy; 2uy; 3uy; 99uy ])
