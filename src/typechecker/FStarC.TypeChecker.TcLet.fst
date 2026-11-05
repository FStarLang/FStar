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
module FStarC.TypeChecker.TcLet

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors
open FStarC.Errors.Msg
open FStarC.TypeChecker
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Ident
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Class.Setlike

module S  = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module N  = FStarC.TypeChecker.Normalize
module TcUtil = FStarC.TypeChecker.Util
module TcTerm = FStarC.TypeChecker.TcTerm
module BU = FStarC.Util
module U  = FStarC.Syntax.Util
module PC = FStarC.Parser.Const
module Free = FStarC.Syntax.Free
module Rel = FStarC.TypeChecker.Rel
module Core = FStarC.TypeChecker.Core
module CoreCheck = FStarC.TypeChecker.CoreCheck
module VCUtil = FStarC.TypeChecker.VCUtil

let dbg_Elab = Debug.get_toggle "Elab"

(* Whether to log the types of the definitions (--log_types). *)
let log env = Options.log_types () && not (lid_equals PC.prims_lid (Env.current_module env))

let profile (env:env) (phase:string) (f:unit -> ML 'a) : ML 'a =
  Profiling.profile f (Some (Ident.string_of_lid (Env.current_module env)))
                      ("FStarC.TypeChecker.Tc.tc_sig_let-" ^ phase)

(****************************************************************************)
(* Pre- and postprocessing tactics                                          *)
(****************************************************************************)

let read_postprocess_with_attr (for_extraction : bool) (env:Env.env) (ats:list attribute)
    : ML (list attribute & option term & bool)
      (* returns:
         - remaining attrs
         - postprocess tactic
         - whether postprocess_type is set. *)
= (* Extract the postprocess_with *)
  let get1 ats lid =
    match U.extract_attr' lid ats with
    | None -> ats, None
    | Some (ats, [tau, None]) ->
      ats, Some tau
    | Some (ats, args) ->
      Errors.log_issue env Errors.Warning_UnrecognizedAttribute [
        text <| Format.fmt1 "Ill-formed application of ‘%s’" (show lid);
      ];
      ats, None
  in
  let lid = if for_extraction then PC.postprocess_extr_with else PC.postprocess_with in
  let ats, pt = get1 ats lid in
  let on_type =
    (* NOTE: retain the attribute even if we find it. So postprocess_type can work
    with a postprocess_with and postprocess_for_extraction_with simultaneously 
    on a single definition. *)
    Some? (U.extract_attr' PC.postprocess_type ats)
  in
  ats, pt, on_type

let run_postprocess (for_extraction : bool) env (se : sigelt) : ML sigelt =
  let attrs, pt, on_type = read_postprocess_with_attr for_extraction env se.sigattrs in

  (* remove the postprocess_with, if any *)
  let se = { se with sigattrs = attrs } in

  let postprocess_lb (tau:term) (on_type : bool) (lb:letbinding) : ML letbinding =
      let s, univnames = SS.univ_var_opening lb.lbunivs in
      let lbdef = SS.subst s lb.lbdef in
      let lbtyp = SS.subst s lb.lbtyp in
      let env = Env.push_univ_vars env univnames in

      let lbdef = Env.postprocess env tau lbtyp lbdef in
      let lbdef = SS.close_univ_vars univnames lbdef in

      let lbtyp =
        if on_type then
          let u = env.universe_of env lbtyp in
          let lbtyp = Env.postprocess env tau lbtyp lbtyp in
          SS.close_univ_vars univnames lbtyp
        else lbtyp
      in

      { lb with lbdef = lbdef; lbtyp = lbtyp }
  in
  let se =
    match pt, se.sigel with
    | Some tac, Sig_let {lbs; lids} ->
        // Postprocess the letbindings with the tactic, if any
        let lbs = (fst lbs, List.map (postprocess_lb tac on_type) (snd lbs)) in
        { se with sigel = Sig_let {lbs; lids} }
    | _ -> se
  in
  se

(****************************************************************************)
(* Qualifiers                                                               *)
(****************************************************************************)

(* qopt: qualifiers in the definition for l
   val_q: qualifiers in the val decl for l.
   This returns a new list of qualifiers from combining both, but they must match. *)
let check_quals_eq (r:Range.t) (l:lident) (qopt : list qualifier) (val_q : list qualifier) : ML (list qualifier) =
  match qopt with
  | [] -> val_q
  | q' ->
    //logic is now a deprecated qualifier, so discard it from the checking
    //AR: 05/19: drop irreducible also
    //           irreducible is not allowed on val, but one could add it on let
    let drop_logic_and_irreducible = List.filter (fun x -> not (Logic? x || Irreducible? x)) in
    let val_q = drop_logic_and_irreducible val_q in
    //but we retain it in the returned list of qualifiers, some code may still add type annotations of Type0, which will hinder `logical` inference
    let q'0 = q' in
    let q' = drop_logic_and_irreducible q' in
    match Class.Ord.ord_list_diff val_q q' with
    | [], [] -> q'0
    | d1, d2 ->
      let open FStarC.Pprint in
      raise_error r Errors.Fatal_InconsistentQualifierAnnotation [
          text "Inconsistent qualifier annotations on" ^/^ pp l;
          prefix 4 1 (text "Expected") (fquotes (pp val_q)) ^/^
          prefix 4 1 (text "got") (fquotes (pp q'));

          if Cons? d1 then
            prefix 2 1 (text "Only in declaration: ") (fquotes (pp d1))
          else empty;
          if Cons? d2 then
            prefix 2 1 (text "Only in definition: ") (fquotes (pp d2))
          else empty;
        ]

(****************************************************************************)
(* Synthesized proofs                                                       *)
(****************************************************************************)

(* A [synth_by_tactic] at a proof goal, once Core has run its tactic (see
   [TcTerm.tc_synth]), is a proof, which we record as [()]. *)
let erase_synthesized_proofs (env:Env.env) (e:term) : ML term =
  e |> FStarC.Syntax.Visit.visit_term false (fun t ->
    match t.n with
    | Tm_app _ ->
      (match U.head_and_args_full t with
       | hd, [(typ, Some ({ aqual_implicit = true })); (_, None)]
           when U.is_synth_by_tactic hd
             && Some? (VCUtil.synth_proof_goal env typ) ->
         { U.exp_unit with pos = t.pos }
       | _ -> t)
    | _ -> t)

(****************************************************************************)
(* 1. Annotation                                                            *)
(****************************************************************************)

(* The names of the definitions for which the user wrote no type at all,
   neither an ascription here nor a separate [val] declaration (see
   [drop_inferred_postconditions]). *)
let unannotated_lbnames (env:env) (lbs:list letbinding) : ML (list lident) =
  lbs |> List.collect (fun lb ->
    let lbname = Inr?.v lb.lbname in
    if Tm_unknown? lb.lbtyp.n && None? (Env.try_lookup_val_decl env lbname.fv_name)
    then [lbname.fv_name]
    else [])

(* Annotate each definition that has a [val] declaration with its type and
   universes, checking that their qualifiers agree. A definition that is
   also annotated here is ascribed that annotation, so that the two are
   checked to be compatible. Returns whether the definitions may be
   generalized (if none has a [val] declaration), the annotated
   definitions, and their qualifiers, with the default visibility. *)
let annotate_with_val_decls (env:env) (r:Range.t) (quals:list qualifier) (lbs:list letbinding)
  : ML (bool & list letbinding & list qualifier)
  = let should_generalize, lbs, quals =
      lbs |> List.fold_left (fun (gen, lbs, quals) lb ->
        let lbname = Inr?.v lb.lbname in //this is definitely not a local let binding
        let gen, lb, quals =
          match Env.try_lookup_val_decl env lbname.fv_name with
          | None ->
            gen, lb, quals
          | Some ((uvs, tval), vquals) ->
            let quals = check_quals_eq r lbname.fv_name quals vquals in
            let def =
              match lb.lbtyp.n with
              | Tm_unknown -> lb.lbdef
              | _ ->
                mk (Tm_ascribed {tm=lb.lbdef; asc=(Inl lb.lbtyp, None, false); eff_opt=None}) lb.lbdef.pos
            in
            if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
            then raise_error r Errors.Fatal_IncoherentInlineUniverse "Inline universes are incoherent with annotation from val declaration";
            false, //explicit annotation provided; do not generalize
            mk_lb (Inr lbname, uvs, PC.effect_Tot_lid, tval, def, lb.lbattrs, lb.lbpos),
            quals
        in
        gen, lb::lbs, quals)
        (true, [], quals)
    in
    (* All the mutually recursive definitions must mention the same universes *)
    U.check_mutual_universes lbs;
    let quals =
      if quals |> BU.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
      then quals
      else Visible_default :: quals //the default visibility for a let binding is Unfoldable
    in
    should_generalize, List.rev lbs, quals

(* Run the [preprocess_with] tactic of [se], if any, on its definitions;
   the attribute is removed from [se]. *)
let preprocess (env:env) (r:Range.t) (se:sigelt) (lbs:list letbinding) : ML (sigelt & list letbinding) =
  let attrs, pre_tau =
    match U.extract_attr' PC.preprocess_with se.sigattrs with
    | None -> se.sigattrs, None
    | Some (ats, [tau, None]) -> ats, Some tau
    | Some (ats, args) ->
      Errors.log_issue r Errors.Warning_UnrecognizedAttribute "Ill-formed application of `preprocess_with`";
      se.sigattrs, None
  in
  let se = { se with sigattrs = attrs } in
  let preprocess_lb (tau:term) (lb:letbinding) : ML letbinding =
    let lbdef = Env.preprocess env tau lb.lbdef in
    if Debug.medium () || !dbg_Elab then
      Format.print1 "lb preprocessed into: %s\n" (show lbdef);
    { lb with lbdef = lbdef }
  in
  match pre_tau with
  | Some tau -> se, List.map (preprocess_lb tau) lbs
  | None -> se, lbs

(****************************************************************************)
(* 2. Elaboration                                                           *)
(****************************************************************************)

(* Erase the type TcTerm inferred for [e], the elaboration of a
   non-recursive definition [e_src] with no type annotation, so that
   elaborating [e] again infers it again. *)
let erase_inferred_type (e_src:term) (e:term) : ML term =
  match (SS.compress e_src).n, (SS.compress e).n with
  | Tm_let {lbs=(false, [lb_src])}, Tm_let {lbs=(false, [lb]); body}
      when Tm_unknown? (SS.compress lb_src.lbtyp).n ->
    { e with n = Tm_let {lbs=(false, [{ lb with lbtyp = S.tun }]); body} }
  | _ -> e

(* Elaborate [e_src], a [let] with a unit body, with TcTerm, without proving
   anything. *)
let elaborate (env:env) (e_src:term) : ML term =
  CoreCheck.elaborating (fun () ->
    let tc (e:term) () = TcTerm.tc_maybe_toplevel_term ({ env with admit = true }) e in
    let e, _, _ =
      profile env "elaborate" (fun () ->
        (* A goal of a [synth_by_tactic] may mention unification variables
           that are only solved after the tactic would have run (e.g. the
           implicits of [f h (_ by tac)] when [h]'s subtyping is deferred).
           So we first elaborate without synthesis, and then synthesize over
           that elaboration, where the goals are fully resolved. *)
        if mem PC.synth_lid (Free.fvars e_src)
        then
          let e1, _, _ = tc e_src () in
          let e1 = N.remove_uvar_solutions env e1 in
          let e1 = if env.admit then e1 else erase_inferred_type e_src e1 in
          TcUtil.with_synth env.admit (tc e1)
        else tc e_src ())
    in
    if Debug.medium () || !dbg_Elab then
      Format.print1 "Let binding after elaboration, before removing uvars: %s\n" (show e);
    let e = N.remove_uvar_solutions env e in
    if Debug.medium () || !dbg_Elab then
      Format.print1 "Let binding after elaboration, uvars removed: %s\n" (show e);
    e)

(****************************************************************************)
(* 3. Checking                                                              *)
(****************************************************************************)

(* TcTerm discharges the guard of the body of a top-level function with the
   function's binders in the environment (see [TcTerm.tc_abs]). Core's guard
   quantifies over them instead. Its leading quantifiers are opened into the
   environment, so that the goal, the context shown when it fails, and what
   tactics handling it (e.g. with [handle_smt_goals]) see are as with TcTerm.
   Quantifiers further in, e.g. over the thunks of a [calc], are kept, as by
   TcTerm. The quantifiers over the variables [drop] holds of are dropped. *)
let rec open_foralls (drop:bv -> typ -> ML bool) (env:env) (g:typ) : ML (Env.env & typ) =
  let hd, args = U.head_and_args_full g in
  match (U.un_uinst hd).n, args with
  | Tm_fvar fv, [_; (f, _)] when S.fv_eq_lid fv PC.forall_lid ->
    begin match (SS.compress f).n with
    | Tm_abs {b; body} ->
      let bs, body = SS.open_term [b] body in
      let env = if drop (List.hd bs).binder_bv body then env else Env.push_binders env bs in
      open_foralls drop env body
    | _ -> env, g
    end
  | _ -> env, g

(* Discharge Core's guard for a definition, whose body is [abs_body] if it
   is a function. TcTerm simplifies guards as it builds them (without full
   normalization, see [TcUtil]); so is Core's guard before it is discharged.
   This matters for normalization requests, e.g. [norm [nbe; primops] ("a" ^
   "b") == "ab"]: the simplifier reduces the primitive application in the
   argument first, whereas processing the request directly with only
   [primops] does not unfold [(^)]. TcTerm discharges the guard of a
   function body when checking the abstraction; that of any other definition
   later, in [TcUtil.check_top_level]: errors are reported in the same
   context. *)
let discharge (drop:bv -> typ -> ML bool)
              (abs_body:option term) (env:env) (g:option Core.guard_and_tok_t) : ML unit =
  match g with
  | None -> ()
  | Some (g, tok) ->
    let go () =
      (* E.g. goals produced by tactics are located at the range of the
         environment: that of the body of a function, as with TcTerm. *)
      let env = match abs_body with
                | Some body -> Env.set_range env body.pos
                | None -> env in
      let env, g = open_foralls drop env g in
      if !dbg_Elab then Format.print2 "core: discharging %s (at %s)\n" (show g) (Range.string_of_range g.pos);
      Rel.force_trivial_guard env
        (Rel.simplify_guard env (Env.guard_of_guard_formula (NonTrivial g)))
    in
    if Some? abs_body then go ()
    else Errors.with_ctx "While checking for top-level effects" go;
    Core.commit_guard tok

(* The declared types of a definition are checked on their own, and their
   guard discharged as a separate query, as TcTerm does. Core caches what it
   proves, so checking the definition against them does not re-emit their
   guards. Were the two guards conjoined, that of the types, quantified over
   their binders, would be a hypothesis of every goal of the definition (the
   SMT encoding assumes each conjunct of a guard while proving the next),
   which can derail the SMT solver, e.g. with nonlinear terms like [pow2 (hi
   - lo)]. *)
let check_declared_types (env:env) (ts:list typ) : ML unit =
  ts |> List.iter (fun t ->
    if not (Tm_unknown? (SS.compress t).n)
    then (
      if !dbg_Elab then Format.print1 "core: checking the declared type %s\n" (show t);
      ignore (CoreCheck.universe_of env "the type of this definition" t)
    ))

(* Whether the result of a definition is ascribed, as in [let f x : t = e]. *)
let rec result_ascribed (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_abs {body} -> result_ascribed body
  | Tm_meta {tm} -> result_ascribed tm
  | Tm_ascribed _ -> true
  | _ -> false

(* Check [let lb in body], the elaboration of a non-recursive definition,
   with Core, against the type of [lb]: the one [annotated] by the user, or
   else the one inferred by the elaboration, which is then recorded, as
   clients of the module see it.

   The type is checked, and its guard discharged, before the definition, as
   by TcTerm (see [check_declared_types]), if it is annotated, or if the
   result of the definition is (as the inferred type then comes from it):
   Core would otherwise only check it as part of the definition, e.g. the
   precondition of a lemma as the type of one of its binders. Any other
   inferred type is not checked: it may only be well-formed in the context
   the definition sets up, e.g. [x:U32.t{v x = f b}] for [let n = f b in lem
   b; U32.uint_to_t n], where [=] is taken at [uint_t 32]; TcTerm does not
   check it either. *)
let check_let (env:env) (annotated:bool) (result_annotated:bool)
              (lb:letbinding) (body:term) (pos:Range.t)
  : ML (either term Core.error)
  = let usubst, univ_names = SS.univ_var_opening lb.lbunivs in
    let lbdef = SS.subst usubst lb.lbdef in
    let lbtyp = SS.subst usubst lb.lbtyp in
    let env_u = Env.push_univ_vars env univ_names in
    if !dbg_Elab then
      Format.print3 "core: expected type %s (annotated: %s, result annotated: %s)\n"
        (show lbtyp) (show annotated) (show result_annotated);
    if annotated || result_annotated then check_declared_types env_u [lbtyp];
    match Core.compute_term_comp env_u lbdef (Some lbtyp) false with
    | Inl (c, g) ->
      let abs_body =
        match (SS.compress (U.unascribe lbdef)).n with
        | Tm_abs {body} -> Some body
        | _ -> None
      in
      discharge (fun _ _ -> false) abs_body env_u g;
      CoreCheck.check_smt_patterns env_u lbdef;
      let topt = if annotated then Some lbtyp else None in
      Inl (TcTerm.finish_top_level_let true env lb lbdef univ_names c Env.trivial_guard topt annotated body pos)
    | Inr err -> Inr err

(* Check [e], the elaboration of the recursive definitions [lbs], with Core,
   against their types. *)
let check_let_rec (env:env) (e:term) (lbs:list letbinding) (body:term) : ML (either term Core.error) =
  let lbs', _ = SS.open_let_rec lbs body in
  let univ_names = (List.hd lbs').lbunivs in
  let env_u = Env.push_univ_vars env univ_names in
  check_declared_types env_u (List.map (fun (lb:letbinding) -> lb.lbtyp) lbs');
  match Core.check_top_level_letrec env_u lbs' with
  | Inl g ->
    (* The guard mentions the names of the nest (see
       [Core.check_top_level_letrec]), bound here, before the binders of the
       function: the SMT encoding closes a query over the variables at the
       end of the environment only ([Encode.encode_query]), and encodes the
       others as constants. Were the binders followed by the names of the
       nest, a refinement mentioning them, e.g. the [x:a{p x}] in
       [list_refb #a #p tl : list (x:a{p x})], would be encoded as a
       constant unrelated to its encoding in the typing axiom of the
       function, from which the SMT solver gets the type of the recursive
       call. The quantifiers over the local names of the nest, which the
       guard no longer mentions, are dropped. *)
    let is_nest_name (x:bv) (body:typ) : ML bool =
      not (Free.names body |> mem x)
      && lbs' |> List.existsb (fun (lb:letbinding) ->
           match lb.lbname with
           | Inr fv -> Ident.string_of_id (Ident.ident_of_lid fv.fv_name) = Ident.string_of_id x.ppname
           | Inl y -> Ident.string_of_id y.ppname = Ident.string_of_id x.ppname)
    in
    let env_nest =
      List.fold_left (fun env (lb:letbinding) ->
        Env.push_let_binding env lb.lbname (lb.lbunivs, lb.lbtyp)) env_u lbs' in
    let _, fun_body, _ = U.abs_formals (List.hd lbs').lbdef in
    discharge is_nest_name (Some fun_body) env_nest g;
    List.iter (fun (lb:letbinding) -> CoreCheck.check_smt_patterns env_nest lb.lbdef) lbs';
    Inl e
  | Inr err -> Inr err

(* Check [e], the elaboration of [e_src], with Core, discharging its guard.
   Core decides whether the definition is accepted, and reports why when it
   is not: an unprovable guard is reported by the SMT solver, with the
   labels Core put on it, and a structural failure with Core's error.
   Returns the checked term. *)
let check_with_core (env:env) (e_src:term) (e:term) : ML term =
  (* The elaboration of a closed definition must be closed: Core checks it
     as is. A free name in it is a bug in elaboration (see
     doc/ref/core_typechecking.md, "Ill-scoped elaborations"). *)
  if Cons? (elems (Free.names e)) then
    raise_error (Env.get_range env) Errors.Error_IllScopedTerm [
      text "Internal error: the elaboration of this definition has free names:";
      text (show (Free.names e))
    ];
  let r =
    profile env "core" (fun () ->
      match (SS.compress e_src).n, (SS.compress e).n with
      | Tm_let {lbs=(false, [lb_src])}, Tm_let {lbs=(false, [lb]); body} ->
        let annotated = not (Tm_unknown? (SS.compress lb_src.lbtyp).n) in
        check_let env annotated (result_ascribed lb_src.lbdef) lb body e.pos
      | _, Tm_let {lbs=(true, lbs); body} ->
        U.check_mutual_universes lbs;
        check_let_rec env e lbs body
      | _ -> failwith "check_with_core: not a let")
  in
  match r with
  | Inl e -> e
  | Inr err -> CoreCheck.raise_core_error env "this definition" err

(* In [admit] mode, only the SMT patterns of the elaboration are checked. *)
let check_smt_patterns_lax (env:env) (e:term) : ML unit =
  match (SS.compress e).n with
  | Tm_let {lbs=(_, lbs)} ->
    lbs |> List.iter (fun (lb:letbinding) ->
      let usubst, univ_names = SS.univ_var_opening lb.lbunivs in
      let env_u = Env.push_univ_vars env univ_names in
      CoreCheck.check_smt_patterns env_u (SS.subst usubst lb.lbtyp);
      CoreCheck.check_smt_patterns env_u (SS.subst usubst lb.lbdef))
  | _ -> ()

(****************************************************************************)
(* 4. Recording                                                             *)
(****************************************************************************)

(* Name the binders of the type of [lb] after the corresponding binders of
   its definition, where the type's are generated. *)
let rename_parameters (lb:letbinding) : ML letbinding =
  let rename_in_typ def typ =
    let typ = SS.compress typ in
    let def_bs = match (SS.compress def).n with
                 | Tm_abs _ ->
                   let binders, _, _ = U.abs_formals_ln def in
                   binders
                 | _ -> [] in
    match typ with
    | { n = Tm_arrow _; pos = r } -> begin
      let val_bs, c = U.arrow_formals_comp_ln_strict typ in
      let has_auto_name bv =
        BU.starts_with (string_of_id bv.ppname) Ident.reserved_prefix in
      let rec rename_binders def_bs val_bs =
        match def_bs, val_bs with
        | [], _ | _, [] -> val_bs
        | ({binder_bv=body_bv}) :: bt, val_b :: vt ->
          (match has_auto_name body_bv, has_auto_name val_b.binder_bv with
           | true, _ -> val_b
           | false, true -> { val_b with
                             binder_bv={val_b.binder_bv with
                               ppname = mk_ident (string_of_id body_bv.ppname, range_of_id val_b.binder_bv.ppname)} }
           | false, false -> val_b) :: rename_binders bt vt in
      S.mk_Tm_arrow (rename_binders def_bs val_bs) c r end
    | _ -> typ in
  { lb with lbtyp = rename_in_typ lb.lbdef lb.lbtyp }

(* The declaration [se] for the checked definitions [e], with their
   parameters named, and with the qualifier [HasMaskedEffect] if their
   effect is masked. *)
let to_sigelt (se:sigelt) (lids:list lident) (quals:list qualifier) (e:term) : ML (sigelt & letbindings) =
  match e.n with
  | Tm_let {lbs; body} ->
    U.check_mutual_universes (snd lbs);
    let lbs = (fst lbs, List.map rename_parameters (snd lbs)) in
    let quals = match body.n with
                | Tm_meta {meta=Meta_desugared Masked_effect} -> HasMaskedEffect::quals
                | _ -> quals
    in
    { se with sigel = Sig_let {lbs; lids}; sigquals = quals }, lbs
  | _ -> failwith "impossible (typechecking should preserve Tm_let)"

(* An unannotated top-level [let _ = lem ()] (or [let _ = assert_norm p])
   gets the inferred type [squash p], since the postcondition of a Pure
   computation is now part of its result type. Recording that as the type
   of the binding would publish [p] to the SMT solver as an ambient fact for
   the rest of the module, which can badly degrade (or even break) later
   queries.

   The user asked for no particular type here, so we record the plain
   [unit] instead. Writing [let _ : squash p = ...] (or any other
   annotation, e.g. the [let _ : nonempty t = nonempty_intro w] idiom)
   still publishes the fact, as intended. *)
let drop_inferred_postconditions (unannotated:list lident) (se:sigelt) : ML sigelt =
  let is_squashed_unit t =
    let head, _ = U.head_and_args_full t in
    match (U.un_uinst head).n with
    | Tm_fvar fv -> S.fv_eq_lid fv PC.squash_lid
    | Tm_refine {b={sort={n=Tm_fvar fv}}} -> S.fv_eq_lid fv PC.unit_lid
    | _ -> false
  in
  let drop_inferred_postcondition lb =
    let lbname = Inr?.v lb.lbname in
    if Nil? lb.lbunivs
    && List.existsb (lid_equals lbname.fv_name) unannotated
    && is_squashed_unit lb.lbtyp
    then { lb with lbtyp = S.t_unit }
    else lb
  in
  match se.sigel with
  | Sig_let {lbs=(is_rec, lbs); lids} ->
    { se with sigel = Sig_let {lbs=(is_rec, List.map drop_inferred_postcondition lbs); lids} }
  | _ -> se

(* With the [no_subtyping] attribute, the types of the definitions, which
   must be lemmas mentioning only symbols of Prims, are checked with
   [use_eq_strict]. *)
let check_no_subtyping (env:env) (se:sigelt) (lbs:letbindings) : ML unit =
  if U.has_attribute se.sigattrs PC.no_subtping_attr_lid
  then begin
    let env = {env with use_eq_strict=true} in
    let err s pos = raise_error pos Errors.Fatal_InconsistentQualifierAnnotation s in
    snd lbs |> List.iter (fun lb ->
      if not (U.is_lemma lb.lbtyp)
      then err ("no_subtype annotation on a non-lemma") lb.lbpos
      else let lid_opt =
                 Free.fvars lb.lbtyp
                 |> elems
                 |> List.tryFind (fun lid ->
                                 not (lid |> Ident.path_of_lid |> List.hd = "Prims" ||
                                      lid_equals lid PC.pattern_lid)) in
           if lid_opt |> Some?
           then err (Format.fmt1 "%s is not allowed in no_subtyping lemmas (only prims symbols)"
                       (lid_opt |> Option.must |> string_of_lid)) lb.lbpos
           else let uvs, lbtyp = SS.open_univ_vars lb.lbunivs lb.lbtyp in
                let env_u = Env.push_univ_vars env uvs in
                if CoreCheck.enabled env_u then (
                  (* Core's memo table must not answer with the result of
                     checking the definition, where subtyping was allowed. *)
                  Core.clear_memo_table ();
                  ignore (CoreCheck.universe_of env_u "the no_subtyping annotation" lbtyp);
                  Core.clear_memo_table ()
                ))
  end

(* Record the types of the definitions for the IDE, and log them if
   requested. *)
let record_types (env:env) (lbs:letbindings) : ML unit =
  snd lbs |> List.iter (fun lb ->
    let fv = Inr?.v lb.lbname in
    Env.insert_fv_info env fv lb.lbtyp);
  if log env
  then Format.print1 "%s\n" (snd lbs |> List.map (fun lb ->
        let should_log = match Env.try_lookup_val_decl env (Inr?.v lb.lbname).fv_name with
            | None -> true
            | _ -> false in
        if should_log
        then Format.fmt2 "let %s : %s" (show lb.lbname) (show lb.lbtyp)
        else "") |> String.concat "\n")

(****************************************************************************)
(* The rule for Sig_let                                                     *)
(****************************************************************************)

let tc_sig_let env r se lbs lids =
  let env0 = env in
  let env = Env.set_range env r in

  (* 1. Annotation *)
  let unannotated = unannotated_lbnames env (snd lbs) in
  let should_generalize, lbs', quals = annotate_with_val_decls env r se.sigquals (snd lbs) in
  let se, lbs' = preprocess env r se lbs' in

  (* 2. Elaboration, as a [let] with a unit body *)
  let e_src = mk (Tm_let {lbs=(fst lbs, lbs'); body=mk (Tm_constant FStarC.Const.Const_unit) r}) r in
  let env' = { env with top_level = true; generalize = should_generalize } in
  let e = elaborate env' e_src in
  let env' =
    match (SS.compress e).n with
    | Tm_let {lbs} -> Env.set_hint_correlator env' { se with sigel = Sig_let {lbs; lids} }
    | _ -> failwith "no way, not a let?"
  in
  Errors.stop_if_err ();

  (* 3. Checking *)
  let e =
    if env'.admit
    then (check_smt_patterns_lax env' e; e)
    else check_with_core env' e_src e
  in
  let e = if mem PC.synth_lid (Free.fvars e_src) then erase_synthesized_proofs env' e else e in

  (* 4. Recording *)
  let se, lbs = to_sigelt se lids quals e in
  let se = run_postprocess false env' se in
  let se = drop_inferred_postconditions unannotated se in
  check_no_subtyping env' se lbs;
  record_types env lbs;
  [se], [], env0
