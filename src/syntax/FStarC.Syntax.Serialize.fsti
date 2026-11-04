(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Syntax.Serialize

(* Serializers (FStarC.Serialize) for ranges, identifiers and the syntax of
   checked modules.

   Ranges, identifiers and long identifiers are shared when they are equal,
   including their ranges.  Terms and bound variables are shared when they
   are physically equal, as with Marshal.  Terms are rebuilt with [mk], which
   recomputes their hash codes.

   Only deep-compressed syntax can be written: unification variables and
   delayed substitutions are an error.  A lazy term is written unfolded, and
   the documents of a [Meta_labeled] are rendered to text. *)

open FStarC.Effect
open FStarC.Range.Type
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.Serialize

instance val serializable_rng    : serializable rng
instance val serializable_range  : serializable range
instance val serializable_ident  : serializable ident
instance val serializable_lident : serializable lident
instance val serializable_universe : serializable universe
instance val serializable_term   : serializable term
instance val serializable_qualifier : serializable qualifier
instance val serializable_open_kind : serializable open_kind
instance val serializable_restriction : serializable restriction
instance val serializable_sigelt : serializable sigelt
instance val serializable_modul  : serializable modul
