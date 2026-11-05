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

(* See the interface. *)

open FStarC.TypeChecker.CommonBase
open FStarC
open FStar.List.Tot
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Errors.Msg { fquotes }
module Env = FStarC.TypeChecker.Env
module S = FStarC.Syntax.Syntax
module R = FStarC.Range
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module PC = FStarC.Parser.Const
module I = FStarC.Ident
module BU = FStarC.Util
module VCUtil = FStarC.TypeChecker.VCUtil
module UnivEq = FStarC.TypeChecker.UnivEq
module UniverseOf = FStarC.TypeChecker.UniverseOf
module Termination = FStarC.TypeChecker.Termination
module Err = FStarC.TypeChecker.Err
module Hash = FStarC.Syntax.Hash
module Subst = FStarC.Syntax.Subst
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Visit = FStarC.Syntax.Visit

open FStarC.Class.Show
open FStarC.Class.Setlike
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Syntax.Print {}

open FStarC.Pprint
open FStarC.Errors.Msg { text }
open FStarC.TypeChecker.Core.Base

instance showable_result #a (_ : showable a) : Tot (showable (__result a)) = {
  show = (function
          | Success (a, _) -> "Success " ^ show a
          | Error e ->   "Error " ^ print_error_short e);
}

let and_pre (p1 p2:precondition) =
  match p1, p2 with
  | None, None -> None
  | Some p, None
    | None, Some p -> Some p
  | Some p1, Some p2 -> Some (U.mk_conj p1 p2)

let fail_str #a msg : result a = fun ctx cache -> Error (ctx, Errors.mkmsg msg, None)

let fail #a msg : result a = fun ctx cache -> Error (ctx, msg, None)

let fail_code #a (code:Errors.error_code) msg : result a = fun ctx cache -> Error (ctx, msg, Some code)

let fail_propagate #a (err:error) : result a = fun _ cache -> Error err

let get_cache () : result cache_t = fun _ cache -> Success ((cache,None), cache)

let put_cache (cache:cache_t) : result unit = fun _ _ -> Success (((), None), cache)

let guard_not_allowed
  : result bool
  = fun ctx cache -> Success ((ctx.no_guard, None), cache)

let unfolding_ok
  : result bool
  = fun ctx cache -> Success ((ctx.unfolding_ok, None), cache)

let no_guard (g:result 'a)
  : result 'a
  = fun ctx cache ->
      match g ({ ctx with no_guard = true}) cache with
      | Success ((x, None), cache) -> Success ((x, None), cache)
      | Success ((x, Some g), cache) -> fail_str (Format.fmt1 "Unexpected guard: %s" (show g)) ctx cache
      | err -> err

(* Run [f], dropping its guard: for computations whose guards have already
   been emitted. The cache is kept only when there was no guard: its entries
   claim their guards have been emitted. *)
let quietly (#a:Type) (f:result a)
  : result a
  = fun ctx cache ->
      match f ctx cache with
      | Success ((x, None), cache') -> Success ((x, None), cache')
      | Success ((x, Some _), _) -> Success ((x, None), cache)
      | Error e -> Error e

let rec map (#a #b:Type) (f:a -> ML (result b)) (l:list a) : ML (result (list b)) =
  match l with
  | [] -> return []
  | hd::tl ->
    let! hd = f hd in
    let! tl = map f tl in
    return (hd::tl)

let mapi (#a #b:Type) (f:int -> a -> ML (result b)) (l:list a) : ML (result (list b)) =
  let rec aux i l : ML _ =
    match l with
    | [] -> return []
    | hd::tl ->
      let! hd = f i hd in
      let! tl = aux (i + 1) tl in
      return (hd::tl)
  in
  aux 0 l

let rec map2 (#a #b #c:Type) (f:a -> b -> ML (result c)) (l1:list a) (l2:list b) : ML (result (list c)) =
  match l1, l2 with
  | [], [] -> return []
  | hd1::tl1, hd2::tl2 ->
    let! hd = f hd1 hd2 in
    let! tl = map2 f tl1 tl2 in
    return (hd::tl)

let rec fold (#a #b:Type) (f:a -> b -> ML (result a)) (x:a) (l:list b) : ML (result a) =
  match l with
  | [] -> return x
  | hd::tl ->
    let! x = f x hd in
    fold f x tl

let rec fold2 (#a #b #c:Type) (f:a -> b -> c -> ML (result a)) (x:a) (l1:list b) (l2:list c) : ML (result a) =
  match l1, l2 with
  | [], [] -> return x
  | hd1::tl1, hd2::tl2 ->
    let! x = f x hd1 hd2 in
    fold2 f x tl1 tl2

let rec iter2 (xs ys:list 'a) (f: 'a -> 'a -> 'b -> ML (result 'b)) (b:'b)
  : ML (result 'b)
  = match xs, ys with
    | [], [] -> return b
    | x::xs, y::ys ->
      let! b = f x y b in
      iter2 xs ys f b
    | _ -> fail_str "Lists of differing length"
