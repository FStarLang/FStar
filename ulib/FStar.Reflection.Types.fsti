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
module FStar.Reflection.Types

include FStar.VConfig

assume new type binder
assume new type bv
assume new type term
assume new type env
assume new type fv
assume new type comp
assume new type sigelt // called `def` in the paper, but we keep the internal name here
assume new type ctx_uvar_and_subst
assume new type letbinding

type name : eqtype = list string
type ident = range * string
type univ_name = ident
type typ     = term
type binders = list binder
