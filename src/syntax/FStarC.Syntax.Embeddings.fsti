(*
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

module FStarC.Syntax.Embeddings

open FStar open FStarC
open FStarC.Compiler
open FStar.Pervasives
open FStarC.Compiler.Effect
open FStarC.Syntax.Syntax
open FStar.Char
open FStarC.VConfig

include FStarC.Syntax.Embeddings.Base

module Range = FStarC.Compiler.Range
module Z = FStarC.BigInt
module BU = FStarC.Compiler.Util

(* Embeddings, both ways and containing type information *)
val e_any         : embedding term
// An identity. Not an instance as sometimes
// we make different choices for embedding a term

instance val e_unit        : embedding unit
instance val e_bool        : embedding bool
instance val e_char        : embedding char
instance val e_int         : embedding Z.t
instance val e_fsint       : embedding int
instance val e_string      : embedding string
instance val e_real        : embedding Compiler.Real.real
instance val e_norm_step   : embedding Pervasives.norm_step
instance val e_vconfig     : embedding FStarC.VConfig.vconfig
instance val e_order       : embedding FStarC.Compiler.Order.order

instance val e_option      : embedding 'a -> Tot (embedding (option 'a))
instance val e_list        : embedding 'a -> Tot (embedding (list 'a))
instance val e_tuple2      : embedding 'a -> embedding 'b -> Tot (embedding ('a & 'b))
instance val e_tuple3      : embedding 'a -> embedding 'b -> embedding 'c -> Tot (embedding ('a & 'b & 'c))
instance val e_tuple4      : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> Tot (embedding ('a & 'b & 'c & 'd))
instance val e_tuple5      : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> embedding 'e -> Tot (embedding ('a & 'b & 'c & 'd & 'e))
instance val e_either      : embedding 'a -> embedding 'b -> Tot (embedding (either 'a 'b))
instance val e_string_list : embedding (list string)
val e_arrow       : embedding 'a -> embedding 'b -> Tot (embedding ('a -> 'b))
instance val e_sealed      : embedding 'a -> Tot (embedding (Sealed.sealed 'a))

val e___range     : embedding Range.range (* unsealed *)
instance val e_range       : embedding Range.range (* sealed *)
instance val e_document    : embedding FStarC.Pprint.document
instance val e_issue       : embedding FStarC.Errors.issue

type abstract_term = | Abstract : t:term -> abstract_term
instance val e_abstract_term : embedding abstract_term

val mk_any_emb : typ -> embedding term

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStarC.Extraction.ML.Util

   See also FStarC.TypeChecker.NBETerm.fsi *)
val arrow_as_prim_step_1:  embedding 'a
                        -> embedding 'b
                        -> ('a -> 'b)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> option term)

val arrow_as_prim_step_2:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> ('a -> 'b -> 'c)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> option term)

val arrow_as_prim_step_3:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> embedding 'd
                        -> ('a -> 'b -> 'c -> 'd)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> option term)

val debug_wrap : string -> (unit -> 'a) -> 'a
