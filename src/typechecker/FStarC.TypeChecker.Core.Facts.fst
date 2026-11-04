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
module FStarC.TypeChecker.Core.Facts

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
open FStarC.TypeChecker.Core.Monad
open FStarC.TypeChecker.Core.Effects
open FStarC.TypeChecker.Core.Util

(* Facts gathered from the types of subterms repeat themselves, e.g. the
   refinement of a variable used several times; stating each once keeps the
   VC small. *)
let dedup_facts (fs:list term) : ML (list term) =
  List.fold_left
    (fun (acc:list term) (f:term) ->
      if BU.for_some (fun (g:term) -> U.term_eq f g) acc then acc else acc @ [f])
    [] fs

let no_facts_l () : ML (Thunk.t (list term)) = Thunk.mkv []

let no_facts () : ML facts =
  let none = no_facts_l () in
  { f_sub = none; f_term = none; f_tail = none }

let facts_concat (fs:list (Thunk.t (list term))) : ML (Thunk.t (list term)) =
  Thunk.mk (fun () -> List.flatten (List.map Thunk.force fs))

let facts_subst (s:subst_t) (fs:Thunk.t (list term)) : ML (Thunk.t (list term)) =
  Thunk.map (List.map (Subst.subst s)) fs

(* The facts [fs] with the variables [xs], of universes [us], going out of
   scope, e.g. the variable of a [let] that cannot be substituted by its
   (effectful) definition. Rather than drop the facts that mention them,
   they are stated together under an existential over [xs], which the
   variables themselves witness: as in [TcUtil.close_escaping], what the
   facts say about other variables through [xs] then survives. *)
let facts_exists (xs:list bv) (us:list universe) (fs:Thunk.t (list term)) : ML (Thunk.t (list term)) =
  Thunk.map
    (fun (fs:list term) ->
      let mentions_xs (f:term) : ML bool =
        let fvs = FStarC.Syntax.Free.names f in
        BU.for_some (fun (x:bv) -> mem x fvs) xs
      in
      let bound, free = List.partition mentions_xs fs in
      match bound with
      | [] -> free
      | _ -> List.fold_right2 U.mk_exists us xs (U.mk_conj_l bound) :: free)
    fs

(* What the type [t_a] of the pure term [a] says about it. *)
let type_facts (g:env) (unfold_ok:bool) (a:term) (t_a:typ)
  : ML (list term)
  = let refinement (t:typ) : ML (option term) =
      match (Subst.compress (U.flatten_refinement t)).n with
      | Tm_refine {b=x; phi} ->
        let bs, phi = Subst.open_term [S.mk_binder x] phi in
        Some (Subst.subst [NT((List.hd bs).binder_bv, a)] phi)
      | _ -> None
    in
    match refinement t_a with
    | Some f -> [f]
    | None ->
      match U.un_squash t_a with
      | Some p -> [p]
      | None ->
        if not unfold_ok then [] else
        match refinement (N.normalize_refinement N.whnf_steps g.tcenv t_a) with
        | Some f -> [f]
        | None -> []

(* The [f_term] of [a], of effect [eff] and type [t_a], whose subterms have
   the facts [sub]. *)
let term_facts (g:env) (a:term) (eff:eff) (t_a:typ) (sub:Thunk.t (list term))
  : ML (Thunk.t (list term))
  = Thunk.mk (fun () ->
    (* What the type of a variable or a constant says about it is already
       in scope: the SMT encoding assumes it where the variable is bound, or
       with the constant's declaration. Restating it at every use only
       swells the VC. *)
    match (Subst.compress (U.unmeta a)).n with
    | Tm_name _ | Tm_constant _ -> []
    | Tm_fvar _ | Tm_uinst _ ->
      (* Except for a top-level proof, e.g. [let _ = lift_emp in e] where
         [lift_emp : squash p], as TcTerm's [bind] adds [p]. *)
      (match U.un_squash t_a with
       | Some p -> [p]
       | None -> [])
    | _ ->
    if not (is_tot_or_ghost_eff eff) then []
    (* [a] is a type or a proposition, e.g. the [p] of [assert p]: what the
       types of its subterms say is a specification-level fact that the SMT
       encoding already derives from their typing, and TcTerm never states
       it. Stating it anyway can derail the solver (everparse's
       [LowParse.BitFields.uint_set_bitfield_set_bitfield_same_gen]). *)
    else if is_type_or_prop t_a then []
    else
      (* The result type of a top-level function is stated as a fact only
         when it is a refinement, e.g. [c:U64.t{v a >= v b ==> v c = ...}]
         for [U64.gte_mask a b], not when it is a name that unfolds to one,
         e.g. [pos] for [pow2 n]. The SMT solver gets the latter through
         the function's typing axiom, as with TcTerm. Stating it at every
         use only adds hypotheses to the VC, which, being about nonlinear
         terms, can derail the solver
         ([FStar.Math.Lemmas.pow2_multiplication_modulo_lemma_1]). *)
      let top_level_head =
        match (U.un_uinst (U.head_of (U.unmeta a))).n with
        | Tm_fvar _ -> true
        | _ -> false
      in
      type_facts g (not top_level_head) a t_a @ Thunk.force sub)

let no_sub_facts () : ML sub_facts = { s_sub = no_facts_l (); s_tail = None }

(* For a term with no [let]s to end with, e.g. a function or a [match]. *)
let no_tail_facts () : ML sub_facts =
  let none = no_facts_l () in
  { s_sub = none; s_tail = Some none }

(* Those of the term wrapped (e.g. ascribed) in another, of the same value. *)
let inner_facts (f:facts) : sub_facts = { s_sub = f.f_sub; s_tail = Some f.f_tail }

let mk_facts (g:env) (e:term) (eff:eff) (t:typ) (s:sub_facts) : ML facts =
  let tf = term_facts g e eff t s.s_sub in
  { f_sub = s.s_sub;
    f_term = tf;
    f_tail = (match s.s_tail with Some tl -> tl | None -> tf) }

(* Those of [let x = def in body], from those of [def] and [body]: a pure
   [def] is substituted for [x], whose facts are those of [def]; otherwise,
   those of [body] are closed over [x], of universe [u]. *)
let let_facts (pure_def:bool) (def:term) (x:bv) (u:universe) (fdef fbody:facts) : ML sub_facts =
  if pure_def
  then
    let s = [NT(x, def)] in
    { s_sub = facts_concat [fdef.f_term; facts_subst s fbody.f_sub];
      s_tail = Some (facts_subst s fbody.f_tail) }
  else
    { s_sub = facts_exists [x] [u] fbody.f_sub;
      s_tail = Some (facts_exists [x] [u] fbody.f_tail) }

(* Those of [let rec xs = ... in body], of universes [us]: the recursive
   names are not definitions that could be substituted, so the facts of the
   body are closed over them. *)
let letrec_facts (xs:binders) (us:list universe) (fbody:facts) : ML sub_facts =
  let xs = List.map (fun (b:binder) -> b.binder_bv) xs in
  { s_sub = facts_exists xs us fbody.f_sub;
    s_tail = Some (facts_exists xs us fbody.f_tail) }

(* For a term none of whose subterms has facts. *)
let no_sub (r:result (eff & typ))
  : ML (result (eff & typ & sub_facts))
  = let! eff, t = r in
    return (eff, t, no_sub_facts ())
