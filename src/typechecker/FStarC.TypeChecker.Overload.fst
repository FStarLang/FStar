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

let is_base_lid l b =
  match b with
  | Base_rigid fv -> fv_eq_lid fv l
  | _ -> false

(* The source and target of a [@@coercion]-annotated function, classified.

   [Util.find_coercion] accepts a candidate of type [b1 -> ... -> bN -> TB ->
   M TC] as a way of turning a [TB] into a [TC], and selects it by comparing
   the head symbol of [TB] with that of the term's type and the head symbol of
   [TC] with that of the expected type -- taking those heads under exactly the
   normalization [base_of_typ] performs. That comparison is this function, and
   [find_coercion] calls it too, so the pairs overload resolution allows for
   and the pairs the typechecker will actually insert are computed by one piece
   of code and cannot drift apart.

   A candidate that is not an arrow, or whose last argument or result does not
   have a rigid head, relates nothing: [find_coercion] cannot use it either. *)
let coercion_source_and_target env f_typ : ML (option (fv & fv)) =
  let f_bs, f_c = U.arrow_formals_comp f_typ in
  if Nil? f_bs then None
  else
    let src = base_head_fv (Env.push_binders env (List.init f_bs))
                           (List.last f_bs).binder_bv.sort in
    let tgt = base_head_fv (Env.push_binders env f_bs) (U.comp_result f_c) in
    match src, tgt with
    | Some src, Some tgt -> Some (src, tgt)
    | _ -> None

(* Every [@@coercion] function in scope, as a relation on head symbols. *)
let user_coercions env : ML (list (fv & fv)) =
  Env.lookup_attr env (Ident.string_of_lid PC.coercion_lid) |> List.collect (fun se ->
    let typ =
      match se.sigel with
      | Sig_let {lbs=(_, [lb])} -> Some (lb.lbunivs, lb.lbtyp)
      | Sig_declare_typ {us; t} -> Some (us, t)
      | _ -> None
    in
    match typ with
    | None -> []
    | Some (us, t) ->
      let _, t = SS.open_univ_vars us t in
      match coercion_source_and_target env t with
      | Some p -> [p]
      | None -> [])

(* The coercions [Util.find_coercion] has built in, transcribed as a relation
   on base types. Each line is one of its cases, in order. *)
let builtin_coercion b1 b2 =
  let is_bool = is_base_lid PC.bool_lid in
  let is_prop = is_base_lid PC.prop_lid in
     (is_bool b1 && is_prop b2)     (* b2t *)
  || (is_prop b1 && Base_type? b2)  (* squash *)
  || (is_bool b1 && Base_type? b2)  (* squash of b2t *)
  || (is_prop b1 && is_bool b2)     (* t2b *)

(* A term whose type classifies as [src] can be passed where a [tgt] is
   expected when the two agree, or when a coercion bridges them. This is
   deliberately *not* equality, because the typechecker inserts coercions: it
   is equality up to every coercion that [Util.maybe_coerce_lc] can apply, in
   the direction it applies it. *)
let coercible env src tgt : ML bool =
  (* [maybe_coerce_lc] inserts [hide] and [reveal] around any type at all, so
     [erased] is not one end of a pair but a base compatible with everything. *)
  let is_erased = is_base_lid PC.erased_lid in
  match src, tgt with
  | Base_unknown, _
  | _, Base_unknown -> true
  | Base_type, Base_type -> true
  | Base_rigid fv1, Base_rigid fv2 when fv_eq fv1 fv2 -> true
  | _ ->
    (* The heads differ, so the candidate is about to be eliminated unless some
       coercion relates them. Only here do we pay for consulting the
       environment, which keeps the cost off the common path. *)
    is_erased src || is_erased tgt
    || builtin_coercion src tgt
    || (user_coercions env |> List.existsb (fun (s, t) ->
          is_base_lid (lid_of_fv s) src && is_base_lid (lid_of_fv t) tgt))

(* [coercible] with the direction forgotten, for the positions where this
   module cannot tell which of the pair the elaborator would coerce; being
   symmetric only ever keeps more candidates, which is the safe direction
   (see [resolve]). *)
let compatible env b1 b2 : ML bool =
  coercible env b1 b2 || coercible env b2 b1

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
   then the results, always by rigid head only. The results are compared with
   the direction the elaborator would coerce in; the leftover formals occur in
   contravariant position and are compared symmetrically.

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
      compatible env (base_of_typ_safe env t1) (base_of_typ_safe env e1) && cmp ts es
    | [], [] -> coercible env (base_of_typ_safe env rt) (base_of_typ_safe env re)
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

(* Ambiguities already reported, keyed by the range of the occurrence and the
   candidates in play. Elaboration duplicates terms, so one occurrence reaches
   [resolve] several times; see [reset_ambiguity_reports] in the interface. *)
let reported : ref (list (string & list string)) = mk_ref []

let reset_ambiguity_reports () = reported := []

let already_reported (l : Ident.lident) (cands : list fv) : ML bool =
  let key = (Range.string_of_range (Ident.range_of_lid l),
             List.map (fun fv -> Ident.string_of_lid (lid_of_fv fv)) cands) in
  if List.mem key !reported
  then true
  else (reported := key :: !reported; false)

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
          narrow_at (Format.fmt1 "arg%s" (show i)) (keep_if (fun t -> coercible env b_arg (nth_explicit_formal_base env t i))) cands
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
      if not (already_reported (lid_of_fv primary) (List.map fst cands)) then
        Errors.log_issue (lid_of_fv primary) Errors.Error_AmbiguousName (
             [group (Errors.Msg.text "The name"
                     ^/^ Errors.Msg.fquotes (pp (Ident.ident_of_lid (lid_of_fv primary)))
                     ^/^ Errors.Msg.text "is ambiguous; candidates are:")]
             @ candidates_doc env (List.map fst cands));
      fv
    )
    else (
      if !dbg then Format.print1 "(Overload) ambiguous, defaulting to %s\n" (show (lid_of_fv fv));
      fv
    )
  | [] -> primary
