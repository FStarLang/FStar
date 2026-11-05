(*
   Copyright Microsoft Research

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
module FStarC.TypeChecker.Core.Cache

(* The caches of the core typechecker (see FStarC.TypeChecker.Core and its
   header comment).

   - The typing of every term checked, with its context, is cached ([insert],
     [lookup]); so is every guard emitted ([insert_guard],
     [raw_lookup_guard]): a guard is not emitted again in an extension of the
     context in which it was.

   - A computation adds its entries to the functional cache it threads
     ([Core.Monad.cache_t]), which is valid only if its guard is. Once the
     caller has proven the guard, the entries are committed to the global
     cache ([table]), with a token ([mk_token], [commit_guard_core]); the
     global cache is cleared by [clear_memo_table].

   - Failures to decide a relation without a guard are remembered for the
     rest of a top-level check ([with_relation_failure_memo]). *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Core.Base
open FStarC.TypeChecker.Core.Monad
module HashTable = FStarC.HashTable

(*** The global cache *)

(* The global cache, whose entries are valid: their guards have been
   proven. [counter] is incremented whenever it is cleared, which
   invalidates the tokens issued before. *)
type tc_table = {
  table:HashTable.t term hash_entry;
  guard_table:HashTable.t term guard_entry;
  counter:ref int //version counter
}

type cache_stats_t = { hits : int; misses : int }

val table : tc_table

val reset_cache_stats (_:unit) : ML unit

val report_cache_stats (_:unit) : ML cache_stats_t

val clear_memo_table (_:unit) : ML unit

(* A token to commit a functional cache to the global cache, once the
   guard it is valid under has been proven. *)
val guard_commit_token : Type0

val mk_token (cache:cache_t) : ML guard_commit_token

(* Commit the cache of the token to the global cache, unless the global
   cache has been cleared since the token was issued, or it was already
   committed. *)
val commit_guard_core (g:guard_commit_token) : ML unit

(* The empty functional cache. *)
val initial_cache : cache_t

(*** Keys *)

(* The key of a term in the caches: the term, with its delayed
   substitutions and solved uvars compressed, sharing all of the term that
   already is. *)
val cache_key (t:term) : ML term

(* Whether the context [g0] is included in [g1], so that what holds in
   [g0] holds in [g1]. *)
val context_included (g0 g1: list binding) : ML bool

(*** Lookup and insertion *)

(* The cached guard [e], if any (whose context must then be compared to
   the current one). *)
val raw_lookup_guard (e:term) : result (option guard_entry)

(* Record that [guard] was emitted in [g]. *)
val insert_guard (g:env) (guard:typ) : result unit

(* Record the typing of [e] in [g]. *)
val insert (g:env) (e:term) (res:success (eff & typ & facts)) : result unit

(* The typing of [e], if cached in a context included in [g]; fails
   otherwise. The use ranges of the type are those of [e]. *)
val lookup (g:env) (e:term) : result (eff & typ & facts)

(*** Failures *)

val clear_relation_failures (_:unit) : ML unit

(* Run [f], which decides [rel] on [t0] and [t1], unless it is known to
   fail; and remember whether it fails, if it must not emit a guard. *)
val with_relation_failure_memo (g:env) (rel:relation) (t0 t1:typ) (f:result unit)
  : result unit
