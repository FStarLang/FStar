(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or impliedmk_
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStarC.Syntax.Hash

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

module H = FStarC.Hash
open FStarC.Class.Hashable

(* The hash code of a term, computed eagerly when it was built. It is purely
   syntactic: it does not look through delayed substitutions, solved uvars or
   lazy terms. *)
val ext_hash_term (t:term) : H.hash_code
(* Syntactic equality, consistent with ext_hash_term: equal terms have equal
   hash codes. Like the hash code, it does not look through delayed
   substitutions, solved uvars or lazy terms, so it is only complete on deeply
   compressed terms. Uvars are compared by their unique id, and names by their
   index (ignoring their sorts). *)
val equal_term (t0 t1:term) : ML bool

(* Like equal_term, but compressing every subterm first: equality up to
   delayed substitutions and solved uvars. This is NOT consistent with
   ext_hash_term, so do not use it as the equality of a hash map. *)
val equal_term_upto_compress (t0 t1:term) : ML bool

(* uses ext_hash_term *)
instance val hashable_term : hashable term

instance val hashable_lident     : hashable Ident.lident
instance val hashable_ident      : hashable Ident.ident
instance val hashable_binding    : hashable binding
instance val hashable_bv         : hashable bv
instance val hashable_fv         : hashable fv
instance val hashable_binder     : hashable binder
instance val hashable_letbinding : hashable letbinding
instance val hashable_pragma     : hashable pragma
instance val hashable_sigelt     : hashable sigelt

(* uses equal_term *)
instance val deq_term : FStarC.Class.Deq.deq term

val term_map (a:Type) : Type0
val term_map_empty  : #a:Type -> ML (term_map a)
val term_map_add    : #a:Type -> t:term -> v:a -> term_map a -> ML (term_map a)
val term_map_lookup : #a:Type -> t:term -> m:term_map a -> ML (option a)
val term_map_mem    : #a:Type -> t:term -> m:term_map a -> ML bool
val term_map_fold   : #a:Type -> #b:Type -> (term -> a -> b -> ML b) -> term_map a -> b -> ML b