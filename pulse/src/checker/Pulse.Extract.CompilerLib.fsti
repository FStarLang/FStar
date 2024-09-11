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

module Pulse.Extract.CompilerLib

module R = FStar.Reflection.V2

val const : Type0
val fv : Type0
type term = R.term
val binder : Type0
val unit_tm : term
val unit_ty : term
val binder_qualifier : Type0
val implicit_qual : binder_qualifier
val mk_binder (sort:term) (ppname:string) (q:option binder_qualifier) (attrs:list term)
  : Dv binder
val mk_abs (b:binder) (body:term) : Dv term
val mk_return (t:term) : Dv term
val mk_meta_monadic : term -> Dv term
val mk_let (b:binder) (head body:term) : Dv term
val mk_if (b then_ else_:term) : Dv term
val pattern : Type0
val mk_fv (s:list string) : Dv fv
val mk_fv_tm (fv:fv) : Dv term
val mk_pat_cons (fv:fv) (pats:list pattern) : Dv pattern
val mk_pat_constant (c:const) : Dv pattern
val mk_pat_var (ppname:string) (sort:term) : Dv pattern
val mk_dot_pat (t:option term) : Dv pattern
val mk_const (c:R.vconst) : Dv const
val branch : Type0
val mk_branch (pat:pattern) (body:term) : Dv branch
val mk_match (scrutinee:term) (brs:list branch) : Dv term

val mk_extracted_as_attr (impl: term) : Dv term
