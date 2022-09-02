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

module FStar.Syntax.Embeddings

open FStar open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Syntax.Syntax
open FStar.Char
open FStar.VConfig

module Range = FStar.Compiler.Range
module Z = FStar.BigInt
module BU = FStar.Compiler.Util

(* TODO: Find a better home for these *)
type norm_step =
    | Simpl
    | Weak
    | HNF
    | Primops
    | Delta
    | Zeta
    | ZetaFull
    | Iota
    | Reify
    | UnfoldOnly  of list string
    | UnfoldFully of list string
    | UnfoldAttr  of list string
    | UnfoldQual  of list string
    | Unascribe
    | NBE
    | Unmeta

type norm_cb = either Ident.lident term -> term // a callback to the normalizer

type shadow_term = option (Thunk.t term)

type embed_t = FStar.Compiler.Range.range -> shadow_term -> norm_cb -> term
type unembed_t 'a = bool -> norm_cb -> option 'a // bool = whether we should warn on a failure

type raw_embedder 'a   = 'a -> embed_t
type raw_unembedder 'a = term -> unembed_t 'a

val steps_Simpl         : term
val steps_Weak          : term
val steps_HNF           : term
val steps_Primops       : term
val steps_Delta         : term
val steps_Zeta          : term
val steps_ZetaFull      : term
val steps_Iota          : term
val steps_Reify         : term
val steps_UnfoldOnly    : term
val steps_UnfoldFully   : term
val steps_UnfoldAttr    : term
val steps_Unascribe     : term
val steps_NBE           : term
val steps_Unmeta        : term

(*
 * Unmbedding functions return an option because they might fail
 * to interpret the given term as valid data. The `try_` version will
 * simply return None in that case, but the unsafe one will also raise a
 * warning, and should be used only where we really expect to always be
 * able to unembed.
 *)

val id_norm_cb : norm_cb
exception Embedding_failure
exception Unembedding_failure

val embedding (a:Type0) : Type0
val emb_typ_of: embedding 'a -> emb_typ
val term_as_fv: term -> fv //partial!
val mk_emb : raw_embedder 'a -> raw_unembedder 'a -> fv -> embedding 'a
val mk_emb_full: raw_embedder 'a
              -> raw_unembedder 'a
              -> typ
              -> ('a -> string)
              -> emb_typ
              -> embedding 'a


// embed: turning a value into a term (compiler internals -> userland)
// unembed: interpreting a term as a value, which can fail (userland -> compiler internals)
val embed        : embedding 'a -> 'a -> embed_t
val unembed      : embedding 'a -> term -> unembed_t 'a
val warn_unembed : embedding 'a -> term -> norm_cb -> option 'a
val try_unembed  : embedding 'a -> term -> norm_cb -> option 'a
val type_of      : embedding 'a -> typ
val set_type     : typ -> embedding 'a -> embedding 'a

val embed_as     : embedding 'a ->
                   ('a -> 'b) ->
                   ('b -> 'a) ->
                   option typ -> (* optionally change the type *)
                   embedding 'b

(* Embeddings, both ways and containing type information *)
val e_any         : embedding term // an identity
val e_unit        : embedding unit
val e_bool        : embedding bool
val e_char        : embedding char
val e_int         : embedding Z.t
val e_fsint       : embedding int
val e_string      : embedding string
val e_norm_step   : embedding norm_step
val e_range       : embedding Range.range
val e_vconfig     : embedding vconfig

val e_option      : embedding 'a -> embedding (option 'a)
val e_list        : embedding 'a -> embedding (list 'a)
val e_tuple2      : embedding 'a -> embedding 'b -> embedding ('a * 'b)
val e_tuple3      : embedding 'a -> embedding 'b -> embedding 'c -> embedding ('a * 'b * 'c)
val e_either      : embedding 'a -> embedding 'b -> embedding (either 'a 'b)
val e_string_list : embedding (list string)
val e_arrow       : embedding 'a -> embedding 'b -> embedding ('a -> 'b)

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
