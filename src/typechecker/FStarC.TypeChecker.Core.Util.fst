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
module FStarC.TypeChecker.Core.Util

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
open FStarC.TypeChecker.Core.Binders
open FStarC.TypeChecker.Core.Effects

(* A fast path for relating terms, so up to delayed substitutions and solved
   uvars: unlike the cache keys, these terms are not deeply compressed. *)
let equal_term t1 t2 =
  FStarC.Profiling.profile (fun _ -> Hash.equal_term_upto_compress t1 t2) None "FStarC.TypeChecker.Core.equal_term"

let mk_type (u:universe) = S.mk (Tm_type u) R.dummyRange

let mk_exists_unrefined = U.mk_exists_unrefined

(* Whether [d] occurs as a subterm of [t]. *)
let occurs_in (d:term) (t:term) : ML bool =
  let found = mk_ref false in
  let _ = FStarC.Syntax.Visit.visit_term false
            (fun (t:term) -> if not !found && U.term_eq t d then found := true; t) t in
  !found

let equatable g t = t |> U.leftmost_head |> VCUtil.may_relate_by_smt g.tcenv true

(* Whether an argument of an application, or of an application in an argument
   and so on, binds a variable, e.g. [p ** (exists* x. q x)], or [reveal #(a ->
   nat) f]. The SMT encoding of such a term names it after its free variables
   (e.g., as [Tm_abs_<hash> q] or [Tm_arrow_<hash> a]), so an equation between
   two of them that differ under the binder is beyond the SMT solver, unless
   they are related argument-wise, under the binder. *)
let rec args_contain_binders (t:term) : ML bool =
  let _, args = U.head_and_args_full t in
  BU.for_some (fun (a, _) ->
    match (Subst.compress a).n with
    | Tm_abs _ | Tm_arrow _ | Tm_refine _ -> true
    | Tm_app _ -> args_contain_binders a
    | _ -> false) args

(* Whether a formula is first-order: no quantifier, abstraction, arrow,
   refinement, match or let anywhere in it. *)
let rec quantifier_free (t:term) : ML bool =
  match (Subst.compress t).n with
  | Tm_abs _ | Tm_arrow _ | Tm_refine _ | Tm_match _ | Tm_let _ -> false
  | Tm_app {hd; arg=(a, _)} -> quantifier_free hd && quantifier_free a
  | Tm_meta {tm} | Tm_ascribed {tm} -> quantifier_free tm
  | _ -> true

(* Whether [t], the type of some term, syntactically says that the term is a
   type or a proposition. *)
let is_type_or_prop (t:typ) : ML bool =
  match (Subst.compress (U.unrefine t)).n with
  | Tm_type _ -> true
  | _ -> (
    match (U.un_uinst (Subst.compress (U.unrefine t))).n with
    | Tm_fvar fv -> S.fv_eq_lid fv PC.prop_lid || S.fv_eq_lid fv PC.eqtype_lid
    | _ -> false
  )

let is_type (g:env) (t:term)
  : result universe
  = let aux t =
        match (Subst.compress t).n with
        | Tm_type u ->
          return u

        | _ ->
          fail [
            text "Expected a type, got" ^/^ fquotes (pp t)
          ]
    in
    (* Unfold until a [Type] appears, e.g. through [type p (x:t) =
       a:u0{...}] with [u0 = Type0]: the [Unrefine] step has the normalizer
       continue with the sort of every refinement it reaches in head
       position. An ascription it leaves (e.g. the [Type0 <: Type] of [kf 0]
       in tests/custard/KindAbbrev) is stripped and the rest unfolded in
       turn, until nothing changes. No bound is needed: [t] is the type of
       a well-typed term, so it normalizes. *)
    let rec go (t:term) : ML (result universe) =
      handle_with
        (aux t)
        (fun _ ->
          let t' = U.unascribe (N.unfold_whnf' [Env.Unrefine] g.tcenv t) in
          if U.term_eq t t' then aux t' else go t')
    in
    with_context "is_type" (Some (CtxTerm t)) (fun _ -> go t)

let rec is_arrow (g:env) (t:term)
  : result (binder & eff & typ)
  = let rec aux t : ML _ =
        match (Subst.compress t).n with
        | Tm_arrow {b=x; comp=c} ->
          (* A [Pure]/[Ghost] arrow carries no specification any more -- its
             precondition is an implicit binder and its postcondition is part
             of the result type -- and an effect name is always a root effect,
             so the comp's effect is all there is to read off. *)
          let g, x, c = open_comp g x c in
          return (x, comp_eff c, U.comp_result c)

        | Tm_refine {b=x} ->
          is_arrow g x.sort

        | Tm_meta {tm=t}
        | Tm_ascribed {tm=t} ->
          aux t

        | _ ->
          fail [
            text "Expected an arrow, got a" ^/^ doc_of_string (tag_of t) ^^ colon ^/^ fquotes (pp t);
          ]
    in
    with_context "is_arrow" None (fun _ ->
      handle_with
        (aux t)
        (fun _ -> aux (N.unfold_whnf g.tcenv t)))

let check_arg_qual (a:aqual) (b:bqual)
  : result unit
  = match b with
    | Some (Implicit _)
    | Some (Meta _) ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        return ()
      | _ ->
        fail_str "missing arg qualifier implicit"
      end

    | _ ->
      begin
      match a with
      | Some ({aqual_implicit=true}) ->
        fail_str "extra arg qualifier implicit"
      | _ -> return ()
      end

let check_bqual (b0 b1:bqual)
  : ML (result unit)
  = if U.bqual_compat b0 b1
    then return ()
    else fail_str (Format.fmt2 "Binder qualifier mismatch, %s vs %s" (show b0) (show b1))

let check_aqual (a0 a1:aqual)
  : ML (result unit)
  = match a0, a1 with
    | None, None -> return ()
    | Some ({aqual_implicit=b0}), Some ({aqual_implicit=b1}) ->
      if b0 = b1
      then return ()
      else
        fail [
          text "Unequal arg qualifiers: lhs implicit="
          ^^ pp b0 ^/^ text "and rhs implicit=" ^^ pp b1
        ]
    | None, Some { aqual_implicit=false }
    | Some { aqual_implicit=false }, None ->
      return ()
    | _ ->
      fail [
        text "Unequal arg qualifiers: lhs" ^/^ fquotes (pp a0)
        ^^ text "and rhs" ^/^ fquotes (pp a1)
      ]

let check_positivity_qual (rel:relation) (p0 p1:option positivity_qualifier)
  : result unit
  = if CommonBase.check_positivity_qual (SUBTYPING? rel) p0 p1
    then return ()
    else fail_str "Unequal positivity qualifiers"

let check_no_escape (bs:binders) t =
    let xs = FStarC.Syntax.Free.names t in
    if BU.for_all (fun b -> not (mem b.binder_bv xs)) bs
    then return ()
    else fail_str "Name escapes its scope"

(* The type at which a [let]'s body sees its variable: its annotation
   [lbtyp], as the user wrote it (it may well be the only form of it that
   exposes, say, an arrow), further refined by what the type [tdef]
   synthesized for the definition says about it. The annotation may be one
   that elaboration inferred, which lacks the refinements that carry the
   definition's postcondition (a lemma's, say). The definition has both
   types, so the variable may be assumed to have both. *)
let let_binder_sort (g:env) (lbtyp:typ) (tdef:option typ)
  : ML typ
  = match tdef with
    | None -> lbtyp
    | Some tdef ->
      if U.term_eq lbtyp tdef then tdef
      else
        let refinement (t:typ) : ML (option (bv & term)) =
          match (Subst.compress (U.flatten_refinement t)).n with
          | Tm_refine {b=y; phi} ->
            let bs, phi = Subst.open_term [S.mk_binder y] phi in
            Some ((List.hd bs).binder_bv, phi)
          | _ -> None
        in
        let r =
          match refinement tdef with
          | Some r -> Some r
          | None ->
            match U.un_squash tdef with
            | Some p -> Some (S.new_bv None lbtyp, p)
            | None -> refinement (N.normalize_refinement N.whnf_steps g.tcenv tdef)
        in
        match r with
        | Some (y, phi) -> U.refine { y with sort = lbtyp } phi
        | None -> lbtyp

(* For [e = fun xs -> body] (one group of binders) and [t] an arrow with at
   least as many binders, looking through abbreviations but not through
   refinements (which would drop their predicates): [xs], [body], the first
   [|xs|] binders of [t] and the computation type they abstract. *)
let abs_against_arrow (g:env) (e:term) (t:typ)
  : ML (option (binders & term & binders & comp))
  = let xs, body, _ = U.abs_one_group_ln e in
    let n = List.length xs in
    let t =
      let t = Subst.compress t in
      if Tm_arrow? t.n then t else U.unascribe (N.unfold_whnf g.tcenv t)
    in
    let formals, c = U.arrow_formals_comp_strict t in
    let len = List.length formals in
    if len = 0 then None
    else if len < n then
      (* E.g. [fun frame s0 -> e] against [frame:slprop -> act frame], where
         [act frame] is an abbreviation for an arrow: the first [len]
         binders are checked against [t], and the function of the rest (a
         spine of unary abstractions, so still locally nameless) against
         [c]. *)
      let rec peel (k:int) (e:term) : ML term =
        if k = 0 then e
        else match (Subst.compress e).n with
             | Tm_abs {body} -> peel (k - 1) body
             | _ -> failwith "impossible: abs_against_arrow"
      in
      Some (fst (List.splitAt len xs), peel len e, formals, c)
    else if len = n then Some (xs, body, formals, c)
    else
      let formals, rest = List.splitAt n formals in
      Some (xs, body, formals, S.mk_Total (U.arrow rest c))

(* A match is syntactically exhaustive, so that its residual path condition
   needs no SMT query, when it has no when clauses and either some branch is a
   variable pattern, or the scrutinee's type is (up to refinement) [bool] and
   both [true] and [false] are covered, or it is an inductive type each of
   whose constructors is covered by a pattern whose arguments are all variables
   (or dot patterns). Pulse's elaborated [if]s produce many of these. *)
let match_is_syntactically_exhaustive (g:env) (t_sc:typ) (brs:list branch) : ML bool =
  let pats = List.map (fun (p, _, _) -> p) brs in
  let is_var_pat (p:pat) = match p.v with | Pat_var _ -> true | _ -> false in
  let simple_args (args:list (pat & bool)) =
    List.for_all (fun (p, _) -> match p.v with | Pat_var _ | Pat_dot_term _ -> true | _ -> false) args
  in
  let has_bool b =
    List.existsb (fun p -> match p.v with
                          | Pat_constant (FStarC.Const.Const_bool b') -> b = b'
                          | _ -> false) pats
  in
  let covers_datacon (d:I.lident) =
    List.existsb (fun p -> match p.v with
                          | Pat_cons (fv, _, args) -> S.fv_eq_lid fv d && simple_args args
                          | _ -> false) pats
  in
  List.for_all (fun (_, w, _) -> None? w) brs &&
  (List.existsb is_var_pat pats ||
   (let t = t_sc |> N.normalize_refinement N.whnf_steps g.tcenv |> U.unrefine in
    let head = U.leftmost_head t |> U.un_uinst in
    match (Subst.compress head).n with
    | Tm_fvar fv ->
      if S.fv_eq_lid fv PC.bool_lid
      then has_bool true && has_bool false
      else (
        let is_induc, ds = Env.datacons_of_typ g.tcenv (S.lid_of_fv fv) in
        is_induc && List.for_all covers_datacon ds
      )
    | _ -> false))

let pat_field_projection (g:env) (scrutinee:term) (pat_p:Range.t) (fv:fv) (us_opt:option universes)
                         (type_args:option (option universes & list term))
                         (sub_pats:list (pat & bool)) (i:int)
  : ML term
  = let wild_pat pos = S.withinfo (Pat_var (wild_bv S.tun pos)) pos in
      (* The [i]th field of the scrutinee, as an application of its
         projector, as [TcTerm] builds branch conditions: unlike a [match],
         the SMT encoding of a projector carries the field's type. The
         projector's type arguments are the constructor's parameters, which
         the elaborated pattern records as dot patterns. *)
      let ith_projector_app (i:int) : ML (option term) =
        (* The projector's implicit arguments are the parameters and the
           indices of the scrutinee's type; failing to find the latter,
           e.g. for a type with no indices, the parameters are those the
           elaborated pattern records as dot patterns. *)
        let us_opt, params =
          match type_args with
          | Some (us, args) -> (match us with | Some _ -> us | None -> us_opt), Some args
          | None ->
          (us_opt, (match Env.num_inductive_ty_params g.tcenv (Env.typ_of_datacon g.tcenv fv.fv_name) with
          | None -> None
          | Some n ->
            if n > List.length sub_pats then None else
            let ps, _ = List.splitAt n sub_pats in
            let rec aux (ps:list (S.pat & bool)) : option (list term) =
              match ps with
              | [] -> Some []
              | ({v=Pat_dot_term (Some t)}, _) :: ps ->
                (match aux ps with None -> None | Some ts -> Some (t :: ts))
              | _ -> None
            in
            aux ps))
        in
        match params with
        | None -> None
        | Some params ->
          let proj = Env.lookup_projector g.tcenv fv.fv_name i in
          match Env.try_lookup_lid g.tcenv proj with
          | None -> None //e.g., we are typechecking the projector itself
          | Some _ ->
            let head = S.fvar (I.set_lid_range proj scrutinee.pos) None in
            let head = match us_opt with | Some us -> S.mk_Tm_uinst head us | None -> head in
            Some (S.mk_Tm_app head (List.map S.iarg params @ [S.as_arg scrutinee]) scrutinee.pos)
      in
      let mk_ith_projector i =
        match ith_projector_app i with
        | Some t -> t
        | None ->
        let ith_pat_var, ith_pat =
            // NOTE: This variable must have an ID distinct from all the other
            // wildcards below (constantly 0). Otherwise, the close_branch call
            // below will wrongly turn this bv in the branch expression to @0,
            // the 0th DB index.
            let bv = { wild_bv S.tun scrutinee.pos with index = 1 } in
            bv, S.withinfo (Pat_var bv) scrutinee.pos
        in
        let sub_pats = List.mapi (fun j (s,b) -> if i <> j then wild_pat s.p,b else ith_pat,b) sub_pats in
        let pat = S.withinfo (Pat_cons(fv, us_opt, sub_pats)) pat_p in
        let branch = S.bv_to_name ith_pat_var in
        let eqn = Subst.close_branch (pat, None, branch) in
        S.mk (Tm_match {scrutinee; ret_opt=None; brs=[eqn]; rc_opt=None}) scrutinee.pos
      in
      mk_ith_projector i
