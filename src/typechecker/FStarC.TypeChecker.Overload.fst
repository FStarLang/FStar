(*
   Copyright 2008-2025 Microsoft Research

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

module FStarC.TypeChecker.Overload

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Pprint
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.Class.Show
open FStarC.Class.PP

module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module Env = FStarC.TypeChecker.Env
module PC = FStarC.Parser.Const
module Print = FStarC.Syntax.Print

let dbg = Debug.get_toggle "Overload"

instance showable_base_typ : showable base_typ = {
  show = (function
          | Base_rigid fv -> "Base_rigid " ^ show fv
          | Base_type -> "Base_type"
          | Base_unknown -> "Base_unknown");
}

(* The normalization steps that define what "the base type" means: strip
   ascriptions, strip metadata, and strip refinements, so that x:nat{x > 17}
   and int agree. This is the same normalization the projector resolution path
   has always used. *)
let base_steps : list Env.step = [Unascribe; Unmeta; Unrefine]

let base_of_typ env t =
  let t = N.unfold_whnf' base_steps env t in
  let hd, _ = U.head_and_args_full t in
  let r =
    match (SS.compress (U.un_uinst hd)).n with
    | Tm_fvar fv -> Base_rigid fv
    | Tm_type _ -> Base_type
    | _ -> Base_unknown
  in
  if !dbg then
    Format.print2 "(Overload) base_of_typ %s = %s\n" (show t) (show r);
  r

let base_head_fv env t =
  match base_of_typ env t with
  | Base_rigid fv -> Some fv
  | _ -> None

(* Two base types are compatible when a term of the first could be passed
   where the second is expected. This is deliberately *not* just equality:
   the typechecker inserts implicit coercions (Util.find_coercion), so a
   [bool] is acceptable where a [prop] or a [Type] is expected and vice
   versa, an [erased t] where a [t] is, and any [@@coercion]-annotated
   function defines further pairs. Modelling every one of those here would
   be a losing game, so we model the built-in families, which are the ones
   that arise in practice -- [b2t] especially.

   Anything this relation calls incompatible is eliminated for good, so an
   unmodelled coercion is a way to answer with the wrong candidate. If that
   ever bites, the fix is to derive these cases from [Util.find_coercion]
   itself rather than to widen the list here by hand. *)
let coerces_to_anything fv =
  (* [reveal]/[hide] are inserted silently in both directions. *)
  fv_eq_lid fv PC.erased_lid

(* [b2t], [squash] and [t2b] relate bool, prop and Type0 in every direction. *)
let prop_like fv = fv_eq_lid fv PC.bool_lid || fv_eq_lid fv PC.prop_lid

let compatible b1 b2 =
  match b1, b2 with
  | Base_unknown, _
  | _, Base_unknown -> true
  | Base_type, Base_type -> true
  | Base_rigid fv1, Base_rigid fv2 ->
    fv_eq fv1 fv2
    || (prop_like fv1 && prop_like fv2)
    || coerces_to_anything fv1 || coerces_to_anything fv2
  | Base_type, Base_rigid fv
  | Base_rigid fv, Base_type ->
    prop_like fv || coerces_to_anything fv
  | _ -> false

let formals_of_typ env t =
  (* unfold_whnf sees through type abbreviations, so a candidate declared as
     [val f : my_abbrev] still exposes its binders. *)
  U.arrow_formals_comp (N.unfold_whnf env t)

let nth_explicit_formal_base env t i =
  let bs, _ = formals_of_typ env t in
  let explicit = bs |> List.filter (fun b -> not (is_bqual_implicit_or_meta b.binder_qual)) in
  if i < 0 || i >= List.length explicit
  then Base_unknown
  else base_of_typ env (List.nth explicit i).binder_bv.sort

let arity_compatible env t n =
  let bs, c = formals_of_typ env t in
  let n_explicit = bs |> List.filter (fun b -> not (is_bqual_implicit_or_meta b.binder_qual)) |> List.length in
  if n <= n_explicit
  then true
  else
    (* Not enough binders at the top, but the result may still be a function:
       a type abbreviation we have not unfolded, or something whose type is not
       yet known. [base_of_typ] normalizes, so a rigid head at this point really
       cannot be applied any further; anything else might. *)
    match base_of_typ env (U.comp_result c) with
    | Base_rigid _
    | Base_type -> false
    | Base_unknown -> true

let candidates_doc env cands =
  cands |> List.map (fun fv ->
    let l = lid_of_fv fv in
    let ty =
      match Env.try_lookup_lid env l with
      | Some ((_, t), _) -> pp t
      | None -> doc_of_string "<unknown type>"
    in
    group (pp l ^^ doc_of_string " :" ^/^ align ty))

(* Classification must never be able to break a program: a candidate whose
   type we cannot even look at is simply never eliminated. Binder sorts come
   from an opened arrow and so mention free names that are not in [env];
   normalizing those is fine in practice but we do not want to bet the whole
   feature on it. *)
let base_of_typ_safe env t : ML base_typ =
  try base_of_typ env t with _ -> Base_unknown

let type_of_fv env fv : ML (option typ) =
  match Env.try_lookup_lid env (lid_of_fv fv) with
  | Some ((_, t), _) -> Some t
  | None -> None

(* The types of the explicit formals of [t] after [n] explicit arguments have
   been consumed, together with its result type. Implicit and meta binders are
   skipped: at an application site the elaborator inserts them, so they line up
   with nothing the user wrote. *)
let explicit_shape env t n : ML (list typ & typ) =
  let bs, c = formals_of_typ env t in
  let rec go bs n : ML (list typ & typ) =
    match bs with
    | [] -> [], U.comp_result c
    | b :: bs ->
      if is_bqual_implicit_or_meta b.binder_qual
      then go bs n
      else if n > 0
      then go bs (n - 1)
      else
        let rest, r = go bs 0 in
        b.binder_bv.sort :: rest, r
  in
  go bs n

(* Could a candidate of type [t], applied to [n] explicit arguments, have the
   expected type [te]? Compares the remaining explicit formals pairwise and
   then the results, always by rigid head only.

   When the two shapes have a different number of explicit formals we conclude
   nothing: that can be currying, or a type abbreviation we did not unfold, and
   guessing there would be exactly the kind of false elimination that could
   break a working program. *)
let expected_compatible env t n te : ML bool =
  let ts, rt = explicit_shape env t n in
  let es, re = explicit_shape env te 0 in
  let rec cmp ts es : ML bool =
    match ts, es with
    | t1 :: ts, e1 :: es ->
      compatible (base_of_typ_safe env t1) (base_of_typ_safe env e1) && cmp ts es
    | [], [] -> compatible (base_of_typ_safe env rt) (base_of_typ_safe env re)
    | _ -> true
  in
  cmp ts es

(* Apply a filter, but never let it empty the candidate set. Dropping every
   candidate would mean reporting an unresolvable name, where keeping them
   yields an ordinary type error on the scope-order candidate. The latter is
   both the more useful message and the one the user gets with overloading
   disabled. *)
let narrow_at (stage : string) (p : (fv & option typ) -> ML bool) (cs : list (fv & option typ))
  : ML (list (fv & option typ))
  = match List.filter p cs with
    | [] ->
      if !dbg && List.length cs > 1 then
        Format.print1 "(Overload)   [%s] eliminated everything, keeping all\n" stage;
      cs
    | cs' ->
      if !dbg && List.length cs' < List.length cs then
        Format.print2 "(Overload)   [%s] dropped %s\n" stage
          (show (cs |> List.filter (fun (fv, _) -> not (cs' |> List.existsb (fun (fv', _) -> fv_eq fv fv')))
                    |> List.map (fun (fv, _) -> lid_of_fv fv)));
      cs'

(* A candidate whose type we do not know is never eliminated. *)
let keep_if (f : typ -> ML bool) : (fv & option typ) -> ML bool =
  fun (_, ot) ->
    match ot with
    | None -> true
    | Some t -> f t

let resolve env speculate primary alts args expected =
  let cands = (primary :: alts) |> List.map (fun fv -> fv, type_of_fv env fv) in
  let nargs = List.length args in

  if !dbg then
    Format.print2 "(Overload) resolving %s among %s\n"
      (show (lid_of_fv primary))
      (show (List.map (fun fv -> lid_of_fv fv) (primary :: alts)));

  let cands = narrow_at "arity" (keep_if (fun t -> arity_compatible env t nargs)) cands in

  let rec by_args i cands : ML (list (fv & option typ)) =
    if i >= nargs || List.length cands <= 1
    then cands
    else
      let b_arg = speculate (List.nth args i) in
      let cands =
        match b_arg with
        | Base_unknown -> cands
        | _ ->
          narrow_at (Format.fmt1 "arg%s" (show i)) (keep_if (fun t -> compatible b_arg (nth_explicit_formal_base env t i))) cands
      in
      by_args (i + 1) cands
  in
  let cands = by_args 0 cands in

  let cands =
    if List.length cands <= 1 then cands
    else
      match expected with
      | None -> cands
      | Some te -> narrow_at "expected" (keep_if (fun t -> expected_compatible env t nargs te)) cands
  in

  match cands with
  | [(fv, _)] ->
    if !dbg then Format.print1 "(Overload) resolved to %s\n" (show (lid_of_fv fv));
    fv
  | (fv, _) :: _ ->
    if Options.Overload_strict? (Options.overload_mode ())
    then (
      // Reported (not raised) so that a single file reports all its
      // ambiguities, and so that `--warn_error -362` can demote this to a
      // warning and recover the scope-order answer.
      Errors.log_issue (lid_of_fv primary) Errors.Error_AmbiguousName (
           [Errors.Msg.text (Format.fmt1 "The name %s is ambiguous; candidates are:"
                               (show (lid_of_fv primary)))]
           @ candidates_doc env (List.map fst cands));
      fv
    )
    else (
      if !dbg then Format.print1 "(Overload) ambiguous, defaulting to %s\n" (show (lid_of_fv fv));
      fv
    )
  | [] -> primary
