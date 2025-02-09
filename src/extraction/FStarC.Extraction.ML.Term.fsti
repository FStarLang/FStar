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
module FStarC.Extraction.ML.Term
open FStarC.Extraction.ML.UEnv
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Extraction.ML.Syntax

val normalize_abs: term -> term
val normalize_for_extraction (env:uenv) (e:term) : term
val is_arity: uenv -> term -> bool
val ind_discriminator_body : env:uenv -> discName:lident -> constrName:lident -> mlmodule1
val term_as_mlty: uenv -> term -> mlty

exception NotSupportedByExtension
let translate_typ_t = g:uenv -> t:term -> mlty
val register_pre_translate_typ (f : translate_typ_t) : unit
let translate_t = g:uenv -> t:term -> mlexpr & e_tag & mlty
val register_pre_translate (f : translate_t) : unit

val term_as_mlexpr: uenv -> term -> mlexpr & e_tag & mlty
val extract_lb_iface : uenv -> letbindings -> uenv & list (fv & exp_binding)
