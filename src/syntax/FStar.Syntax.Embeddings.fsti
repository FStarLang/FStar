﻿(*
   Copyright 2008-2014 Microsoft Research

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

module FStar.Syntax.Embeddings

open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Char
open FStar.VConfig

include FStar.Syntax.Embeddings.Base

module Range = FStar.Compiler.Range
module Z = FStar.BigInt
module BU = FStar.Compiler.Util

(* Embeddings, both ways and containing type information *)
val e_any         : embedding term // an identity
val e_unit        : embedding unit
val e_bool        : embedding bool
val e_char        : embedding char
val e_int         : embedding Z.t
val e_fsint       : embedding int
val e_string      : embedding string
val e_norm_step   : embedding Pervasives.norm_step
val e_vconfig     : embedding vconfig

val e_option      : embedding 'a -> embedding (option 'a)
val e_list        : embedding 'a -> embedding (list 'a)
val e_tuple2      : embedding 'a -> embedding 'b -> embedding ('a * 'b)
val e_tuple3      : embedding 'a -> embedding 'b -> embedding 'c -> embedding ('a * 'b * 'c)
val e_either      : embedding 'a -> embedding 'b -> embedding (either 'a 'b)
val e_string_list : embedding (list string)
val e_arrow       : embedding 'a -> embedding 'b -> embedding ('a -> 'b)
val e_sealed      : embedding 'a -> embedding 'a

val e___range     : embedding Range.range (* unsealed *)
val e_range       : embedding Range.range (* sealed *)
val e_issue       : embedding FStar.Errors.issue

val mk_any_emb : typ -> embedding term

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStar.Extraction.ML.Util

   See also FStar.TypeChecker.NBETerm.fsi *)
val arrow_as_prim_step_1:  embedding 'a
                        -> embedding 'b
                        -> ('a -> 'b)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option term)

val arrow_as_prim_step_2:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> ('a -> 'b -> 'c)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option term)

val arrow_as_prim_step_3:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> embedding 'd
                        -> ('a -> 'b -> 'c -> 'd)
                        -> n_tvars:int
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (args -> option term)

val debug_wrap : string -> (unit -> 'a) -> 'a
