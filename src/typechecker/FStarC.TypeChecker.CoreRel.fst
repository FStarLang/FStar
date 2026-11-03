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
module FStarC.TypeChecker.CoreRel

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Class.Show
open FStarC.Syntax.Print {}

module Rel = FStarC.TypeChecker.Rel
module Core = FStarC.TypeChecker.Core
module UF = FStarC.Syntax.Unionfind
module VCUtil = FStarC.TypeChecker.VCUtil

let dbg = Debug.get_toggle "CoreRel"

(* Core's decision on [t1] and [t2], whose unification variables Rel has
   solved, with the guard [g]. *)
let decide (guard_ok:bool) (subtyping:bool) (env:env) (t1 t2:typ) (g:guard_t)
  : ML (option guard_t)
  = if env.admit then Some g else
    (* Core is always allowed a guard: when the caller is not, the guard
       must simplify to [True] (e.g. [hide (reveal x) == x], which Rel
       decides with a primitive step, and Core only by its guard). *)
    let r =
      if subtyping
      then Core.check_term_subtyping true true env t1 t2
      else Core.check_term_equality true true env t1 t2
    in
    let reject (why:string) : ML (option guard_t) =
      if !dbg then
        Format.print4 "CoreRel: Core rejects %s %s %s: %s\n"
          (show t1) (if subtyping then "<:" else "=") (show t2) why;
      None
    in
    match r with
    | Inl None -> Some g
    | Inl (Some (f, tok)) ->
      if guard_ok
      then Some { g with guard_f = NonTrivial f }
      else if Trivial? (check_trivial (VCUtil.simplify_vc true env f))
      then (Core.commit_guard tok; Some g)
      else reject ("it needs a proof of " ^ show f)
    | Inr err -> reject (Core.print_error err)

(* Run [f] in a transaction, rolled back unless it returns [Some _]. *)
let in_transaction (f:unit -> ML (option 'a)) : ML (option 'a) =
  let tx = UF.new_transaction () in
  let r = try f () with e -> UF.rollback tx; raise e in
  match r with
  | None -> UF.rollback tx; None
  | r -> UF.commit tx; r

let try_rel (subtyping:bool) (guard_ok:bool) (env:env) (t1 t2:typ) : ML (option guard_t) =
  in_transaction (fun () ->
    let r =
      match subtyping, guard_ok with
      | false, true -> Rel.try_teq true env t1 t2
      | false, false -> Rel.teq_nosmt env t1 t2
      | true, true -> Rel.try_subtype env t1 t2
      | true, false -> Rel.subtype_nosmt env t1 t2
    in
    match r with
    | None -> None
    | Some g -> decide guard_ok subtyping env t1 t2 g)

let try_teq guard_ok env t1 t2 = try_rel false guard_ok env t1 t2
let try_subtype guard_ok env t1 t2 = try_rel true guard_ok env t1 t2

let rel_nosmt_force (subtyping:bool) (env:env) (t1 t2:typ) : ML bool =
  Some? (in_transaction (fun () ->
    let r =
      if subtyping
      then Rel.subtype_nosmt env t1 t2
      else Rel.teq_nosmt env t1 t2
    in
    match r with
    | None -> None
    | Some g ->
      Rel.force_trivial_guard env g;
      decide false subtyping env t1 t2 trivial_guard))

let teq_nosmt_force env t1 t2 = rel_nosmt_force false env t1 t2
let subtype_nosmt_force env t1 t2 = rel_nosmt_force true env t1 t2
