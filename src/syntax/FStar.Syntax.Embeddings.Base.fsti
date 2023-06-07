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

module FStar.Syntax.Embeddings.Base

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Pervasives
open FStar.Syntax.Syntax

module Range = FStar.Compiler.Range

type norm_cb = either Ident.lident term -> term // a callback to the normalizer

type shadow_term = option (Thunk.t term)

type embed_t = Range.range -> shadow_term -> norm_cb -> term

type unembed_t 'a = norm_cb -> option 'a // bool = whether we should warn on a failure

type raw_embedder 'a   = 'a -> embed_t
type raw_unembedder 'a = term -> unembed_t 'a
type printer 'a        = 'a -> string

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


(*
 * embed: turning a value into a term (compiler internals -> userland)
 * unembed: interpreting a term as a value, which can fail (userland -> compiler internals)
 *
 * Unmbedding functions return an option because they might fail
 * to interpret the given term as valid data. The `try_` version will
 * simply return None in that case, but the unsafe one will also raise a
 * warning, and should be used only where we really expect to always be
 * able to unembed.
 *)
val embed        : embedding 'a -> 'a -> embed_t
val try_unembed  : embedding 'a -> term -> norm_cb -> option 'a
val unembed      : embedding 'a -> term -> norm_cb -> option 'a

val type_of      : embedding 'a -> typ
val printer_of   : embedding 'a -> printer 'a
val set_type     : typ -> embedding 'a -> embedding 'a

val embed_as     : embedding 'a ->
                   ('a -> 'b) ->
                   ('b -> 'a) ->
                   option typ -> (* optionally change the type *)
                   embedding 'b

(* Construct a simple lazy embedding as a blob. *)
val e_lazy        : lazy_kind ->
                    ty:term ->
                    embedding 'a



(* Helpers for extracted embeddings of inductive types.
Do not use internally. *)
val mk_extracted_embedding :
  string -> (* name *)
  (string & list term -> option 'a) -> (* unembedding specialized to an applied fvar *)
  ('a -> term) -> (* embedding *)
  embedding 'a
val extracted_embed :
  embedding 'a ->
  'a ->
  term
val extracted_unembed :
  embedding 'a ->
  term ->
  option 'a
