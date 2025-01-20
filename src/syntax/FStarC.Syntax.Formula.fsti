(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.Syntax.Formula

open FStarC.Effect
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Class.Show

(**************************************************************************************)
(* Destructing a type as a formula *)
(**************************************************************************************)

type qpats = list args
type connective =
    | QAll of binders & qpats & typ
    | QEx of binders & qpats & typ
    | BaseConn of lident & args

instance val showable_connective : showable connective

val destruct_typ_as_formula (f:term) : option connective
