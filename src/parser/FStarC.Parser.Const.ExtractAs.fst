(*
   Copyright 2008-2025 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR C  ONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Parser.Const.ExtractAs

open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Ident
open FStarC.Range.Type
open FStarC.Const
open FStarC.Syntax
open FStarC.Syntax.Syntax

let p2l l = lid_of_path l dummyRange
let extract_as_lid = p2l ["FStar"; "ExtractAs"; "extract_as"]

let is_extract_as_attr (attr: attribute) : option term =
  let head, args = Syntax.Util.head_and_args attr in
  match (Subst.compress head).n, args with
  | Tm_fvar fv, [t, _] when Syntax.fv_eq_lid fv extract_as_lid ->
    (match (Subst.compress t).n with
    | Tm_quoted(impl, _) -> Some impl
    | _ -> None)
  | _ -> None

