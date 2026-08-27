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

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStar.Char

include FStarC.Syntax.Embeddings.Base

module Range = FStarC.Range.Type

val mk_any_emb : typ -> embedding term

(* Embeddings, both ways and containing type information *)
val e_any         : embedding term
// An identity. Not an instance as sometimes
// we make different choices for embedding a term

instance val e_unit        : embedding unit
instance val e_bool        : embedding bool
instance val e_char        : embedding char
instance val e_int         : embedding int
instance val e_string      : embedding string

(* NOTE: the compiler-side type Real.real (= FStar.RealLiteral.real_literal)
is the runtime representation of *two different* F* types:

  - FStar.Real.real, of which it represents the subset denotable by a literal,
    i.e. the values of Const_real. This is e_real below.
  - FStar.RealLiteral.real_literal, the record of a mantissa and an exponent
    that the reflection API uses as the payload of C_Real. This is
    e_real_literal below.

Neither embedding is an instance: they would overlap, and instance resolution
would silently pick one where the other was meant. Both must be passed
explicitly. *)

(* Embeds a real into a real constant (Const_real) of type FStar.Real.real.
Note that unembedding is partial: it only succeeds on literals, since no other
value of FStar.Real.real (an axiomatized type) has a runtime representation. *)
val e_real         : embedding Real.real

(* Embeds a real literal as a value of type FStar.RealLiteral.real_literal,
i.e. as an application of its record constructor. *)
val e_real_literal : embedding Real.real

instance val e_option      : embedding 'a -> Tot (embedding (option 'a))
instance val e_tuple2      : embedding 'a -> embedding 'b -> Tot (embedding ('a & 'b))
instance val e_tuple3      : embedding 'a -> embedding 'b -> embedding 'c -> Tot (embedding ('a & 'b & 'c))
instance val e_tuple4      : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> Tot (embedding ('a & 'b & 'c & 'd))
instance val e_tuple5      : embedding 'a -> embedding 'b -> embedding 'c -> embedding 'd -> embedding 'e -> Tot (embedding ('a & 'b & 'c & 'd & 'e))
instance val e_either      : embedding 'a -> embedding 'b -> Tot (embedding (either 'a 'b))
instance val e_list        : embedding 'a -> Tot (embedding (list 'a))
instance val e_string_list : embedding (list string)

instance val e_norm_step   : embedding NormSteps.norm_step
instance val e_vconfig     : embedding FStar.VConfig.vconfig
instance val e_order       : embedding FStarC.Order.order

val e_arrow       : embedding 'a -> embedding 'b -> Tot (embedding ('a -> 'b))
instance val e_sealed      : embedding 'a -> Tot (embedding (Sealed.sealed 'a))

instance val e_range       : embedding Range.t
instance val e_issue       : embedding FStarC.Errors.issue
instance val e_document    : embedding FStarC.Pprint.document

(* Arity specific raw_embeddings of arrows; used to generate top-level
   registrations of compiled functions in FStarC.Extraction.ML.Util

   See also FStarC.TypeChecker.NBETerm.fsi *)
val arrow_as_prim_step_1:  embedding 'a
                        -> embedding 'b
                        -> ('a -> 'b)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> ML (option term))

val arrow_as_prim_step_2:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> ('a -> 'b -> 'c)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> ML (option term))

val arrow_as_prim_step_3:  embedding 'a
                        -> embedding 'b
                        -> embedding 'c
                        -> embedding 'd
                        -> ('a -> 'b -> 'c -> 'd)
                        -> repr_f:Ident.lid
                        -> norm_cb
                        -> (universes -> args -> ML (option term))

val debug_wrap : string -> (unit -> ML 'a) -> ML 'a

type abstract_term = | Abstract : t:term -> abstract_term
instance val e_abstract_term : embedding abstract_term
