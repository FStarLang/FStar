(*
   Copyright 2008-2017 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the Licens
   You may obtain a copy of the License at

       http://www.apachorg/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the Licens
*)
#light "off"
module FStar.Extraction.ML.Term
open FStar.Extraction.ML.UEnv
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.Extraction.ML.Syntax

val normalize_abs: term -> term
val is_arity: env -> term -> bool
val ind_discriminator_body : env:env -> discName:lident -> constrName:lident -> mlmodule1
val term_as_mlty: env -> term -> mlty
val term_as_mlexpr: env -> term -> mlexpr * e_tag * mlty
val extract_lb_iface : env -> letbindings -> env * list<(fv * exp_binding)>