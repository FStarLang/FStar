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

val unit_tm : R.term
val unit_ty : R.term
val mk_return (t:R.term) : Dv R.term
val mk_meta_monadic : R.term -> Dv R.term
val mk_pure_let (b:R.binder) (head body:R.term) : Dv R.term
val mk_let (b:R.binder) (head body:R.term) : Dv R.term
val mk_if (b then_ else_:R.term) : Dv R.term

val mk_extracted_as_attr (impl: R.term) : Dv R.term
