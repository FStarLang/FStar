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
module FStarC.TypeChecker.Core.Monad

(* The monad of the core typechecker (see FStarC.TypeChecker.Core).

   A computation of type [result a] runs in a [context] (see
   [Core.Base.context]) and threads a functional cache (see
   [Core.Cache]); it either fails with an [error], or succeeds with a
   value of type [a] and a guard (a [precondition]): the value is valid
   provided the guard is proven. Sequencing ([let!]) conjoins the guards;
   [with_guard] gives a computation access to the guard (or error) of
   another, e.g. to close it over binders (see [Core.Guard]).

   The combinators used on every check are defined here, so that they are
   inlined in the extracted code. *)

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Class.Show
open FStarC.TypeChecker.Core.Base

(*** The functional cache *)

(* The typing of a term [he_term] in the context [he_gamma]: its effect,
   type and facts. *)
type hash_entry = {
   he_term:term;
   he_gamma:list binding;
   he_eff: eff;
   he_typ: typ;
   he_facts: facts
}

(* A guard emitted in the context [ge_gamma]. *)
type guard_entry = {
  ge_gamma: list binding
}

(* The cache threaded through a computation, which the caller promotes to
   the global cache (see [Core.Cache]) once the guard of the computation
   is proven: every entry is valid provided that guard is. *)
type cache_t = {
  term_map : FStarC.Syntax.Hash.term_map hash_entry;
  guard_map : FStarC.Syntax.Hash.term_map guard_entry;
}

(*** The monad *)

type __result a =
  | Success of a & cache_t
  | Error of error

instance val showable_result (#a:Type) (_ : showable a) : Tot (showable (__result a))

let result a = context -> cache_t -> ML (__result (success a))

inline_for_extraction
let return (#a:Type) (x:a) : result a = fun _ cache -> Success ((x, None), cache)

inline_for_extraction
let return_with_guard (#a:Type) (x:a) (g:precondition) : result a = fun _ cache -> Success ((x, g), cache)

(* The conjunction of two guards. *)
val and_pre (p1 p2:precondition) : ML precondition

(* Sequencing: the guard of the result is the conjunction of the guards of
   [x] and [y x]. *)
inline_for_extraction
let (let!) (#a:Type) (#b:Type) (x:result a) (y:a -> ML (result b))
  : result b
  = fun ctx0 cache0 ->
      match x ctx0 cache0 with
      | Success ((x, g1), cache1) ->
        (match y x ctx0 cache1 with
         | Success ((y, g2), cache2) -> Success ((y, and_pre g1 g2), cache2)
         | err -> err)
      | Error err -> Error err

inline_for_extraction
let (and!) (#a:Type) (#b:Type) (x:result a) (y:result b)
  : result (a & b)
  = let! v = x in
    let! u = y in
    return (v, u)

(* Continue with [f] applied to the value and guard of [x], or to its error,
   rather than propagating them: [f] is responsible for the guard of [x],
   e.g. to emit it transformed. On an error, the cache is that before [x]. *)
inline_for_extraction
let with_guard (#a #b:Type) (x:result a) (f: either (success a) error -> ML (result b))
: result b
= fun ctx cache ->
    match x ctx cache with
    | Success (r, cache') -> f (Inl r) ctx cache'
    | Error err -> f (Inr err) ctx cache

(*** Failure *)

val fail_str (#a:Type) (msg:string) : result a

val fail (#a:Type) (msg:Errors.error_message) : result a

(* Fail with the code with which TcTerm reports the same failure. *)
val fail_code (#a:Type) (code:Errors.error_code) (msg:Errors.error_message) : result a

(* Fail with an error of another computation. *)
val fail_propagate (#a:Type) (err:error) : result a

(* Run [h] if [x] fails. *)
inline_for_extraction
let handle_with (#a:Type) (x:result a) (h: unit -> ML (result a))
  : result a
  = fun ctx cache ->
      match x ctx cache with
      | Error _ -> h () ctx cache
      | res -> res

(* Run [x] with [(msg, t)] pushed on the error context. *)
inline_for_extraction
let with_context (#a:Type) (msg:string) (t:option context_term) (x:unit -> ML (result a))
  : result a
  = fun ctx cache ->
     let ctx = { ctx with error_context=((msg,t)::ctx.error_context) } in
     x () ctx cache

(*** Accessing the cache and the context *)

val get_cache (_:unit) : result cache_t

val put_cache (cache:cache_t) : result unit

(* Whether the computation must succeed without a guard. *)
val guard_not_allowed : result bool

(* Whether the computation may unfold definitions. *)
val unfolding_ok : result bool

(* Run [g], failing if it has a guard. *)
val no_guard (#a:Type) (g:result a) : result a

(* Run [f], dropping its guard: for computations whose guards have already
   been emitted. The cache is kept only when there was no guard: its
   entries claim their guards have been emitted. *)
val quietly (#a:Type) (f:result a) : result a

(*** Lists *)

val map (#a #b:Type) (f:a -> ML (result b)) (l:list a) : ML (result (list b))

val mapi (#a #b:Type) (f:int -> a -> ML (result b)) (l:list a) : ML (result (list b))

val map2 (#a #b #c:Type) (f:a -> b -> ML (result c)) (l1:list a) (l2:list b) : ML (result (list c))

val fold (#a #b:Type) (f:a -> b -> ML (result a)) (x:a) (l:list b) : ML (result a)

val fold2 (#a #b #c:Type) (f:a -> b -> c -> ML (result a)) (x:a) (l1:list b) (l2:list c) : ML (result a)

(* Fails if the lists have different lengths. *)
val iter2 (xs ys:list 'a) (f: 'a -> 'a -> 'b -> ML (result 'b)) (b:'b) : ML (result 'b)
