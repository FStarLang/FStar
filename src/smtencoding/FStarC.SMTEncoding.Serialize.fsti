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
module FStarC.SMTEncoding.Serialize

(* Serializers for the SMT encoding stored in .checked files. *)

open FStarC.Effect
open FStarC.Serialize
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Pruning
open FStarC.SMTEncoding.Env

instance val serializable_sort : serializable sort
(* Terms are hash-consed: equal subterms are written once. *)
instance val serializable_smt_term : serializable term
instance val serializable_decl : serializable decl
instance val serializable_decls_elt : serializable decls_elt
instance val serializable_elt_summary : serializable elt_summary
instance val serializable_fvar_binding : serializable fvar_binding
