(*
   Copyright 2008-2022 Microsoft Research

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
module FStar.Reflection.Data

open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List

(* NOTE: This file is exactly the same as its .fs variant. It is only
here so the equally-named interface file in ulib/ is not taken by the
dependency analysis to be the interface of the .fs. We also cannot ditch
the .fs, since out bootstrapping process does not extract any .ml file
from an interface. Hence we keep both, exactly equal to each other. *)

open FStar.Syntax.Syntax
module Ident = FStar.Ident
module Range = FStar.Compiler.Range
module Z     = FStar.BigInt
open FStar.Ident
module PC = FStar.Parser.Const


let fstar_refl_vconfig = tconst (PC.psconst "vconfig")

let ref_Mkvconfig =
    let lid = PC.psconst "Mkvconfig" in
    let attr = Record_ctor (PC.psconst "vconfig", []) in
    let fv = lid_as_fv lid delta_constant (Some attr) in
    { lid = lid
    ; fv  = fv
    ; t   = fv_to_tm fv
    }

let ref_Q_Meta_attr = fstar_refl_data_const "Q_Meta_attr"
