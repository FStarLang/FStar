(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.TypeChecker.Tc

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Errors
open FStarC.TypeChecker
open FStarC.TypeChecker.Common
open FStarC.TypeChecker.Env
open FStarC.Ident
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Syntax.Util
open FStarC.Const
open FStarC.TypeChecker.TcTerm

open FStarC.Class.Show
open FStarC.Class.Tagged
open FStarC.Class.PP
open FStarC.Class.Setlike
open FStarC.Class.Ord

module S  = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module UF = FStarC.Syntax.Unionfind
module N  = FStarC.TypeChecker.Normalize
module TcUtil = FStarC.TypeChecker.Util
module BU = FStarC.Util //basic util
module U  = FStarC.Syntax.Util
module Gen = FStarC.TypeChecker.Generalize
module TcInductive = FStarC.TypeChecker.TcInductive
module TcEff = FStarC.TypeChecker.TcEffect
module PC = FStarC.Parser.Const
module EMB = FStarC.Syntax.Embeddings
module Print = FStarC.Syntax.Print

let dbg_TwoPhases = Debug.get_toggle "TwoPhases"
let dbg_IdInfoOn  = Debug.get_toggle "IdInfoOn"
let dbg_Normalize = Debug.get_toggle "Normalize"
let dbg_UF        = Debug.get_toggle "UF"
let dbg_LogTypes  = Debug.get_toggle "LogTypes"

let sigelt_typ (se:sigelt) : option typ =
  match se.sigel with
  | Sig_inductive_typ {t}
  | Sig_datacon {t}
  | Sig_declare_typ {t} -> Some t

  | Sig_let {lbs=(_, lb::_)} ->
    Some lb.lbtyp

  | _ ->
    None

//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    //if the tbl has a counter for lid, we use that, else we start from 0
    //this is useful when we verify the extracted interface alongside
    let tbl = env.qtbl_name_and_index |> snd in
    let get_n lid =
      let n_opt = SMap.try_find tbl (show lid) in
      if Some? n_opt then n_opt |> Option.must else 0
    in

    let typ = match sigelt_typ se with | Some t -> t | _ -> S.tun in

    let lids = U.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (GenSym.next_id () |> show) // GM: Should we really touch the gensym?
            | l::_ -> l in
      {env with qtbl_name_and_index=Some (lid, typ, get_n lid), tbl}

let log env = (Options.log_types()) &&  not(lid_equals PC.prims_lid (Env.current_module env))


(*****************Type-checking the signature of a module*****************************)

let tc_type_common (env:env) (ts:tscheme) (expected_typ:typ) (r:Range.t) : ML tscheme =
  let (uvs, t) = ts in
  let uvs, t = SS.open_univ_vars uvs t in
  let env = Env.push_univ_vars env uvs in
  let t = tc_check_trivial_guard env t expected_typ in
  if uvs = [] then
    let uvs, t = Gen.generalize_universes env t in
    //AR: generalize_universes only calls N.reduce_uvar_solutions, so make sure there are no uvars left
    TcUtil.check_uvars r t;
    uvs, t
  else uvs, t |> N.remove_uvar_solutions env |> SS.close_univ_vars uvs

let tc_declare_typ (env:env) (ts:tscheme) (r:Range.t) : ML tscheme =
  tc_type_common env ts (U.type_u () |> fst) r

let tc_assume (env:env) (ts:tscheme) (r:Range.t) : ML tscheme =
  tc_type_common env ts t_prop r

let tc_decl_attributes env se =
  // [Substitute] (defined in Pervasives), is added as attribute by
  // TcInductive when a type has no projector, and this happens for
  // some types (see TcInductive.early_prims_inductives) that are
  // defined before [Substitute] even exists.
  // Thus the partition of attributes below.
  let blacklisted_attrs, other_attrs =
    if lid_exists env PC.attr_substitute_lid
    then ([], se.sigattrs)
    else partition ((=) attr_substitute) se.sigattrs
  in
  let g, other_attrs = tc_attributes env other_attrs in
  Rel.force_trivial_guard env g;
  {se with sigattrs = blacklisted_attrs @ other_attrs }

let tc_inductive' env ses quals attrs lids =
    if Debug.low () then
        Format.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" (show ses);

    let ses = List.map (tc_decl_attributes env) ses in

    let sig_bndle, tcs, datas = TcInductive.check_inductive_well_typedness env ses quals lids in
    (* we have a well-typed inductive;
            we still need to check whether or not it supports equality
            and whether it is strictly positive
       *)
    let sig_bndle = Positivity.mark_uniform_type_parameters env sig_bndle in

    (* Once the datacons are generalized we can construct the projectors with the right types *)
    let attrs' = U.remove_attr PC.erasable_attr attrs in
    let data_ops_ses = List.map (TcInductive.mk_data_operations quals attrs' env tcs) datas |> List.flatten in

    //strict positivity check
    if Options.no_positivity () || (not (Env.should_verify env)) then ()  //skipping positivity check if lax mode
    else begin
       (*
        * AR: call add_sigelt_to_env here? We should maintain the invariant that push_sigelt is only called from there
        *     but then this is temporary, just to check positivity, later we actually do go through add_sigelt_to_env
        *)
       let env2 = Env.push_sigelt env sig_bndle in
       (* Check positivity of the inductives within the Sig_bundle *)
       List.iter (fun ty ->
         let b = Positivity.check_strict_positivity env2 lids ty in
         if not b then
           let lid, r =
             match ty.sigel with
             | Sig_inductive_typ {lid} -> lid, ty.sigrng
             | _                                         -> failwith "Impossible!"
           in
           Errors.log_issue r Errors.Error_InductiveTypeNotSatisfyPositivityCondition ("Inductive type " ^ (string_of_lid lid) ^ " does not satisfy the strict positivity condition")
         else ()
       ) tcs;

       (* Separately, if any of the data constructors in the Sig_bundle are
        * exceptions, check their positivity separately. See issue #1535 *)
       List.iter (fun d ->
         let data_lid, ty_lid =
            match d.sigel with
            | Sig_datacon {lid=data_lid; ty_lid} -> data_lid, ty_lid
            | _ -> failwith "Impossible"
         in
         if lid_equals ty_lid PC.exn_lid &&
            not (Positivity.check_exn_strict_positivity env2 data_lid)
         then
            Errors.log_issue d
              Errors.Error_InductiveTypeNotSatisfyPositivityCondition
               ("Exception " ^ (string_of_lid data_lid) ^ " does not satisfy the positivity condition")
       ) datas
    end;

    //generate hasEq predicate for this inductive

    let skip_haseq =
      //skip logical connectives types in prims, tcs is bound to the inductive type, caller ensures its length is > 0
      let skip_prims_type (_:unit) : ML bool =
        let lid =
          let ty = List.hd tcs in
          match ty.sigel with
          | Sig_inductive_typ {lid} -> lid
          | _                                         -> failwith "Impossible"
        in
        //these are the prims type we are skipping
        List.existsb (fun s -> s = (string_of_id (ident_of_lid lid))) TcInductive.early_prims_inductives in

      let is_noeq = List.existsb (fun q -> q = Noeq) quals in

      //caller ensures tcs length is > 0
      //assuming that we have already propagated attrs from the bundle to its elements
      let is_erasable () = U.has_attribute (List.hd tcs).sigattrs FStarC.Parser.Const.erasable_attr in

      Nil? tcs ||
      (lid_equals env.curmodule PC.prims_lid && skip_prims_type ()) ||
      is_noeq ||
      is_erasable () in

    
    let res =
        if skip_haseq
        then sig_bndle, data_ops_ses
        else
            let is_unopteq = List.existsb (fun q -> q = Unopteq) quals in
            let ses =
              if is_unopteq then TcInductive.unoptimized_haseq_scheme sig_bndle tcs datas env
              else TcInductive.optimized_haseq_scheme sig_bndle tcs datas env
            in
            sig_bndle, ses@data_ops_ses in  //append hasEq axiom lids and data projectors and discriminators lids
    res

let tc_inductive env ses quals attrs lids =
  let env = Env.push env "tc_inductive" in
  let pop () = ignore (Env.pop env "tc_inductive") in  //OK to ignore: caller will reuse original env

  if Options.trace_error () then
    let r = tc_inductive' env ses quals attrs lids in
    pop ();
    r
  else
    try tc_inductive' env ses quals attrs lids |> (fun r -> pop (); r)
    with e -> pop (); raise e

let proc_check_with (attrs:list attribute) (kont : unit -> ML 'a) : ML 'a =
  match U.get_attribute PC.check_with_lid attrs with
  | None -> kont ()
  | Some [(a, None)] ->
    match EMB.unembed a EMB.id_norm_cb with
    | None -> failwith "nah"
    | Some vcfg ->
    Options.with_saved_options (fun () ->
      Options.set_vconfig vcfg;
      kont ())
  | _ -> failwith "ill-formed `check_with`"

let store_sigopts (se:sigelt) : ML sigelt =
  { se with sigopts = Some (Options.get_vconfig ()) }

(* Alternative to making a huge let rec... knot is set below in this file *)
let tc_decls_knot : ref (option (Env.env -> list sigelt -> ML (list sigelt & Env.env))) =
  mk_ref None

let do_two_phases env : ML bool = true
let run_phase1 (f:unit -> ML 'a) : ML 'a =
  FStarC.TypeChecker.Core.clear_memo_table();
  let r = f () in
  FStarC.TypeChecker.Core.clear_memo_table();
  r

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

(* The type checking rule for Sig_let (lbs, lids) *)
let tc_sig_let env r se lbs lids : ML (list sigelt & list sigelt & Env.env) =
    let env0 = env in
    let env = Env.set_range env r in
    let rename_parameters lb =
      let rename_in_typ def typ =
        let typ = Subst.compress typ in
        let def_bs = match (Subst.compress def).n with
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
               | false, false ->
                 // if (string_of_id body_bv.ppname) <> (string_of_id val_bv.ppname) then
                 //   Errors.warn (range_of_id body_bv.ppname)
                 //     (Format.fmt2 "Parameter name %s doesn't match name %s used in val declaration"
                 //                  (string_of_id body_bv.ppname) (string_of_id val_bv.ppname));
                 val_b) :: rename_binders bt vt in
          S.mk_Tm_arrow (rename_binders def_bs val_bs) c r end
        | _ -> typ in
      { lb with lbtyp = rename_in_typ lb.lbdef lb.lbtyp } in

    (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
          (b) Generalize the type of lb only if none of the lbs have val decls nor explicit universes
      *)
    let should_generalize, lbs', quals =
       snd lbs |> List.fold_left (fun (gen, lbs, quals) lb ->
          let lbname = Inr?.v lb.lbname in //this is definitely not a local let binding
          let gen, lb, quals = match Env.try_lookup_val_decl env lbname.fv_name with
            | None ->
                gen, lb, quals

            | Some ((uvs,tval), vquals) ->
              let quals = check_quals_eq r lbname.fv_name quals vquals in
              let def = match lb.lbtyp.n with
                | Tm_unknown -> lb.lbdef
                | _ ->
                  (* If there are two type ascriptions we check that they are compatible *)
                  mk (Tm_ascribed {tm=lb.lbdef; asc=(Inl lb.lbtyp, None, false); eff_opt=None}) lb.lbdef.pos
              in
              if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
              then raise_error r Errors.Fatal_IncoherentInlineUniverse "Inline universes are incoherent with annotation from val declaration";
              false, //explicit annotation provided; do not generalize
              mk_lb (Inr lbname, uvs, PC.effect_Tot_lid, tval, def, lb.lbattrs, lb.lbpos),
              quals
          in
          gen, lb::lbs, quals)
          (true, [], se.sigquals)
    in

    (* Check that all the mutually recursive bindings mention the same universes *)
    U.check_mutual_universes lbs';

    let quals =
        if quals |> BU.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
        then quals
        else Visible_default :: quals //the default visibility for a let binding is Unfoldable
    in

    let lbs' = List.rev lbs' in

    (* preprocess_with *)
    let attrs, pre_tau =
        match U.extract_attr' PC.preprocess_with se.sigattrs with
        | None -> se.sigattrs, None
        | Some (ats, [tau, None]) -> ats, Some tau
        | Some (ats, args) ->
            Errors.log_issue r Errors.Warning_UnrecognizedAttribute "Ill-formed application of `preprocess_with`";
            se.sigattrs, None
    in
    let se = { se with sigattrs = attrs } in (* to remove the preprocess_with *)

    let preprocess_lb (tau:term) (lb:letbinding) : ML letbinding =
        let lbdef = Env.preprocess env tau lb.lbdef in
        if Debug.medium () || !dbg_TwoPhases then
          Format.print1 "lb preprocessed into: %s\n" (show lbdef);
        { lb with lbdef = lbdef }
    in
    // Preprocess the letbindings with the tactic, if any
    let lbs' = match pre_tau with
               | Some tau -> List.map (preprocess_lb tau) lbs'
               | None -> lbs'
    in
    (* / preprocess_with *)

    (* 2. Turn the top-level lb into a Tm_let with a unit body *)
    let e = mk (Tm_let {lbs=(fst lbs, lbs'); body=mk (Tm_constant (Const_unit)) r}) r in

    (* 3. Type-check the Tm_let and convert it back to Sig_let *)
    let env' = { env with top_level = true; generalize = should_generalize } in
    let e =
      if do_two_phases env' then run_phase1 (fun _ ->
        let drop_lbtyp (e_lax:term) : ML term =
          match (SS.compress e_lax).n with
          | Tm_let {lbs=(false, [ lb ]); body=e2} ->
            let lb_unannotated, ropt =
              match (SS.compress e).n with  //checking type annotation on e, the lb before phase 1, capturing e from above
              | Tm_let {lbs=(_, [ lb ])} ->
                (match (SS.compress lb.lbtyp).n with
                 | Tm_unknown -> true, Some (pos lb.lbtyp)
                 | _ -> false, None)
              | _                       -> failwith "Impossible: first phase lb and second phase lb differ in structure!"
            in
            if lb_unannotated then { e_lax with n = Tm_let {lbs=(false, [ { lb with lbtyp = setPos (Some?.v ropt) S.tun } ]);
                                                            body=e2}}  //erase the type annotation
            else e_lax
          | Tm_let {lbs=(true, lbs)} ->
            U.check_mutual_universes lbs;
            //leave recursive lets as is; since the decreases clause from the ascription (if any)
            //is propagated to the lbtyp by TcUtil.extract_let_rec_annotation
            //if we drop the lbtyp here, we'll lose the decreases clause
            e_lax
        in
        let e =
          Profiling.profile (fun () ->
              let (e, _, _) = tc_maybe_toplevel_term ({ env' with phase1 = true; admit = true }) e in
              e)
              (Some (Ident.string_of_lid (Env.current_module env)))
              "FStarC.TypeChecker.Tc.tc_sig_let-tc-phase1"
        in

        if Debug.medium () || !dbg_TwoPhases then
          Format.print1 "Let binding after phase 1, before removing uvars: %s\n" (show e);

        let e = N.remove_uvar_solutions env' e |> drop_lbtyp in

        if Debug.medium () || !dbg_TwoPhases then
          Format.print1 "Let binding after phase 1, uvars removed: %s\n" (show e);
        e)
      else e
    in

    let env' =
        match (SS.compress e).n with
        | Tm_let {lbs} ->
          let se = { se with sigel = Sig_let {lbs; lids} } in
          set_hint_correlator env' se
        | _ ->
          failwith "no way, not a let?"
    in
    Errors.stop_if_err ();
    let r =
        //We already generalized phase1; don't need to generalize again
      let should_generalize = not (do_two_phases env') in
      Profiling.profile (fun () -> tc_maybe_toplevel_term { env' with generalize = should_generalize } e)
                        (Some (Ident.string_of_lid (Env.current_module env)))
                        "FStarC.TypeChecker.Tc.tc_sig_let-tc-phase2"
    in
    let se, lbs = match r with
      | {n=Tm_let {lbs; body=e}}, _, g when Env.is_trivial g ->
        U.check_mutual_universes (snd lbs);

        // Propagate binder names into signature
        let lbs = (fst lbs, (snd lbs) |> List.map rename_parameters) in

        //propagate the MaskedEffect tag to the qualifiers
        let quals = match e.n with
            | Tm_meta {meta=Meta_desugared Masked_effect} -> HasMaskedEffect::quals
            | _ -> quals
        in
        { se with sigel = Sig_let {lbs; lids};
                  sigquals =  quals },
        lbs
      | _ -> failwith "impossible (typechecking should preserve Tm_let)"
    in
    let se = run_postprocess false env' se in

    //
    // if no_subtyping attribute is present, typecheck the signatures with use_eq_strict
    //
    if U.has_attribute se.sigattrs PC.no_subtping_attr_lid
    then begin
      let env' = {env' with use_eq_strict=true} in
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
             else let t, _ = U.type_u () in
                  let uvs, lbtyp = SS.open_univ_vars lb.lbunivs lb.lbtyp in
                  let _, _, g = TcTerm.tc_check_tot_or_gtot_term
                    (Env.push_univ_vars env' uvs)
                    lbtyp
                    t
                    (Some "checking no_subtype annotation") in
                    Rel.force_trivial_guard env' g)
    end;

    (* 4. Record the type of top-level lets, and log if requested *)
    snd lbs |> List.iter (fun lb ->
        let fv = Inr?.v lb.lbname in
        Env.insert_fv_info env fv lb.lbtyp);

    if log env
    then Format.print1 "%s\n" (snd lbs |> List.map (fun lb ->
          let should_log = match Env.try_lookup_val_decl env (Inr?.v lb.lbname).fv_name with
              | None -> true
              | _ -> false in
          if should_log
          then Format.fmt2 "let %s : %s" (show lb.lbname) (show (*env*) lb.lbtyp)
          else "") |> String.concat "\n");

    [se], [], env0

let snapshot_context env msg = BU.atomically (fun () ->
    TypeChecker.Env.snapshot env msg)

let rollback_context solver msg depth : ML env = BU.atomically (fun () ->
    let env = TypeChecker.Env.rollback solver msg depth in
    env)

let push_context env msg = snd (snapshot_context env msg)
let pop_context env msg = rollback_context env.solver msg None

(* Wrapper around U.process_pragma that also handles
   pragmas with typechecker side effects (Check, Eval, etc.) *)
let process_pragma (env:Env.env) (p:pragma) (r:Range.range) : ML unit =
  U.process_pragma p r;
  match p with
  | ShowOptions ->
    Errors.info r [
      text "Option state:";
      Pprint.arbitrary_string (Options.show_options ());
    ]

  | PrintEffectsGraph ->
    BU.write_file "effects.graph" (Env.print_effects_graph env)

  | Check t0 ->
    let env' = push_context env "#check" in
    let tx = UF.new_transaction () in
    BU.finally (fun () -> ignore (pop_context env' "#check"); UF.rollback tx) (fun () ->
      let t, lc, g = tc_term { env with instantiate_imp = false } t0 in
      let c, g' = lcomp_comp lc in
      let g = Class.Monoid.mplus g g' in
      let open FStarC.Pprint in
      Options.with_saved_options (fun () ->
        ignore (Options.set_options "--print_effect_args");
        Errors.info r [
          text "Term" ^/^ pp t ^/^ text "has type" ^/^ pp c;
          if not (is_trivial g) then
            text "With guard: " ^/^ pp g
          else
            empty
        ]
      )
    )

  | Eval t0 ->
    let env' = push_context env "#eval" in
    let tx = UF.new_transaction () in
    BU.finally (fun () -> ignore (pop_context env' "#eval"); UF.rollback tx) (fun () ->
      let t_elab, _, g1 = tc_term { env' with instantiate_imp = false; phase1 = true; admit=true } t0 in
      Format.print1 "Guard = %s\n" (Rel.guard_to_string env' g1);
      Rel.force_trivial_guard env' g1;
      let t, lc, g = tc_term { env' with instantiate_imp = false } t_elab in
      let t = N.normalize [Env.Beta; Env.Iota; Env.Zeta; Env.Primops;
                            Env.UnfoldUntil S.delta_constant;
                            Env.Eager_unfolding; Env.Inlining;
                            Env.Unmeta; Env.Unascribe] env' t in
      let open FStarC.Pprint in
      Errors.info r [
        text "#eval" ^/^ pp t0 ^/^ text "==>" ^/^ pp t
      ]
    )

  | _ -> ()

let tc_decl' env0 se: ML (list sigelt & list sigelt & Env.env) =
  let env = env0 in
  let se = match se.sigel with
         // Disable typechecking attributes for [Sig_fail] bundles, so
         // that typechecking is wrapped in [Errors.catch_errors]
         // below, thus allowing using [expect_failure] to mark that
         // an attribute will fail typechecking.
         | Sig_fail _ -> se
         | _ -> tc_decl_attributes env se
  in
  Quals.check_sigelt_quals_pre env se;
  proc_check_with se.sigattrs (fun () ->
  let r = se.sigrng in
  let se =
    if Options.record_options ()
    then store_sigopts se
    else se
  in
  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    failwith "Impossible bare data-constructor"

  (* If we're --laxing, and this is not an `expect_lax_failure`, then just ignore the definition *)
  | Sig_fail {fail_in_lax=false} when env.admit ->
    if Debug.any () then
      Format.print1 "Skipping %s since env.admit=true and this is not an expect_lax_failure\n"
        (Print.sigelt_to_string_short se);
    [], [], env

  | Sig_fail {rng=fail_rng; errs=expected_errors; fail_in_lax=lax; ses} ->
    let env' = if lax then { env with admit = true } else env in
    let env' = Env.push env' "expect_failure" in
    (* We need to call push since tc_decls will encode the sigelts that
     * succeed to SMT, which may be relevant in checking the ones that
     * follow it. See #1956 for an example of what goes wrong if we
     * don't pop the context (spoiler: we prove false). *)

    if Debug.low () then
        Format.print1 ">> Expecting errors: [%s]\n" (String.concat "; " <| List.map show expected_errors);

    let errs, _ = Errors.catch_errors (fun () ->
                    Options.with_saved_options (fun () ->
                      Some?.v (!tc_decls_knot) env' ses)) in

    if Options.print_expected_failures () || Debug.low () then
      Errors.print_expected_failures errs;

    (* Pop environment, reset SMT context *)
    let _ = Env.pop env' "expect_failure" in

    let actual_errors = List.concatMap (fun i -> FStarC.Common.list_of_option i.issue_number) errs in

    begin match errs with
    | [] ->
        List.iter Errors.print_issue errs;
        Errors.log_issue se Errors.Error_DidNotFail [
            text "This top-level definition was expected to fail, but it succeeded.";
          ]
    | _ ->
        if expected_errors <> [] then
          match Errors.find_multiset_discrepancy expected_errors actual_errors with
          | None -> ()
          | Some (e, n1, n2) ->
            let open FStarC.Pprint in
            let open FStarC.Errors.Msg in
            List.iter Errors.print_issue errs;
            Errors.log_issue fail_rng Errors.Error_DidNotFail [
                prefix 2 1
                  (text "This top-level definition was expected to raise error codes")
                  (pp (sort expected_errors)) ^/^
                prefix 2 1 (text "but it raised")
                  (pp (sort actual_errors)) ^^
                dot;
                text (Format.fmt3 "Error #%s was raised %s times, instead of %s."
                                      (show e) (show n2) (show n1));
              ]
    end;
    [], [], env

  | Sig_bundle {ses; lids} ->
    let env = Env.set_range env r in
    let ses =
      if do_two_phases env then run_phase1 (fun _ ->
        //we generate extra sigelts even in the first phase and then throw them away
        //would be nice to not generate them at all
        let ses =
          tc_inductive ({ env with phase1 = true; admit = true }) ses se.sigquals se.sigattrs lids
          |> fst
          |> N.elim_uvars env
          |> U.ses_of_sigbundle in
        if Debug.medium () || !dbg_TwoPhases
        then Format.print1 "Inductive after phase 1: %s\n" (show ({ se with sigel = Sig_bundle {ses; lids} }));
        ses)
      else ses
    in
    let sigbndle, projectors_ses = tc_inductive env ses se.sigquals se.sigattrs lids in
    let sigbndle = { sigbndle with sigattrs = se.sigattrs } in (* keep the attributes *)
    [ sigbndle ], projectors_ses, env0

  | Sig_pragma p ->  //no need for two-phase here
    process_pragma env p r;
    (* Some pragmas are immediately dropped and do not
    make it into the checked file. *)
    let keep_pragma =
      match p with
      | ShowOptions
      | PrintEffectsGraph
      | Eval _
      | Check _ -> false
      | _ -> true
    in
    (if keep_pragma then [se] else []), [], env0

  | Sig_new_effect ne ->
      let ne =
        if do_two_phases env then run_phase1 (fun _ ->
          let ne =
            TcEff.tc_eff_decl ({ env with phase1 = true; admit = true }) ne se.sigquals se.sigattrs
            |> (fun ne -> { se with sigel = Sig_new_effect ne })
            |> N.elim_uvars env |> U.eff_decl_of_new_effect in
          if Debug.medium () || !dbg_TwoPhases
          then Format.print1 "Effect decl after phase 1: %s\n"
                 (show ({ se with sigel = Sig_new_effect ne }));
          ne)
        else ne in
      let ne = TcEff.tc_eff_decl env ne se.sigquals se.sigattrs in
      let se = { se with sigel = Sig_new_effect(ne) } in
      [se], [], env0

  | Sig_sub_effect(sub) ->  //no need to two-phase here, since lifts are already lax checked
    let sub = TcEff.tc_lift env sub r in
    let se = { se with sigel = Sig_sub_effect sub } in
    [se], [], env

  | Sig_effect_abbrev {lid; us=uvs; bs=tps; comp=c; cflags=flags} ->
    let lid, uvs, tps, c =
      if do_two_phases env
      then run_phase1 (fun _ ->
        TcEff.tc_effect_abbrev ({ env with phase1 = true; admit = true }) (lid, uvs, tps, c) r
        |> (fun (lid, uvs, tps, c) -> { se with sigel = Sig_effect_abbrev {lid;
                                                                           us=uvs;
                                                                           bs=tps;
                                                                           comp=c;
                                                                           cflags=flags} })
        |> N.elim_uvars env |>
        (fun se -> match se.sigel with
                | Sig_effect_abbrev {lid; us=uvs; bs=tps; comp=c} -> lid, uvs, tps, c
                | _ -> failwith "Did not expect Sig_effect_abbrev to not be one after phase 1"))
      else lid, uvs, tps, c in

    let lid, uvs, tps, c = TcEff.tc_effect_abbrev env (lid, uvs, tps, c) r in
    let se = { se with sigel = Sig_effect_abbrev {lid;
                                                  us=uvs;
                                                  bs=tps;
                                                  comp=c;
                                                  cflags=flags} } in
    [se], [], env0

  | Sig_declare_typ _
  | Sig_let _
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      (* Dummy declaration which must be erased since it has been elaborated somewhere else *)
      [], [], env0

  | Sig_declare_typ {lid; us=uvs; t} -> //NS: No checks on the qualifiers?

    if lid_exists env lid then
      raise_error r Errors.Fatal_AlreadyDefinedTopLevelDeclaration [
        text (Format.fmt1 "Top-level declaration %s for a name that is already used in this module." (show lid));
        text "Top-level declarations must be unique in their module."
      ];

    let env = Env.set_range env r in
    let uvs, t =
      if do_two_phases env then run_phase1 (fun _ ->
        let uvs, t = tc_declare_typ ({ env with phase1 = true; admit = true }) (uvs, t) se.sigrng in //|> N.normalize [Env.NoFullNorm; Env.Beta; Env.DoNotUnfoldPureLets] env in
        if Debug.medium () || !dbg_TwoPhases then Format.print2 "Val declaration after phase 1: %s and uvs: %s\n" (show t) (show uvs);
        uvs, t)
      else uvs, t
    in

    let uvs, t = tc_declare_typ env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_declare_typ {lid; us=uvs; t} }], [], env0

  | Sig_assume {lid; us=uvs; phi=t} ->
    if not (List.contains S.InternalAssumption se.sigquals) then
      FStarC.Errors.log_issue r Warning_WarnOnUse 
        (Format.fmt1 "Admitting a top-level assumption %s" (show lid));
    let env = Env.set_range env r in

    let uvs, t =
      if do_two_phases env then run_phase1 (fun _ ->
        let uvs, t = tc_assume ({ env with phase1 = true; admit = true }) (uvs, t) se.sigrng in
        if Debug.medium () || !dbg_TwoPhases then Format.print2 "Assume after phase 1: %s and uvs: %s\n" (show t) (show uvs);
        uvs, t)
      else uvs, t
    in

    let uvs, t = tc_assume env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_assume {lid; us=uvs; phi=t} }], [], env0

  | Sig_splice {is_typed; lids; tac=t} ->
    if Debug.any () then
      Format.print3 "%s: Found splice of (%s) with is_typed: %s\n"
        (show env.curmodule)
        (show t)
        (show is_typed);

    // env.splice will check the tactic

    let ses = env.splice env se.sigquals se.sigattrs is_typed lids t se.sigrng in

    if Debug.low () then
      Format.print1 "Will splice decls:\n%s\n" (show ses);

    let ses = 
      (* For non-typed splices, they choose their own attributes and qualifiers.
      The tactics can access them via the cur_attrs and cur_quals primitives, and add
      them to the generated sigelts, possibly filtering some out.

      Typed splices should probably do the same, though we would need to have
      a typing judgment for them (e.g. stating what is allowed). *)
      if is_typed then
        let sigquals =
              match se.sigquals with
              | [] -> [ S.Visible_default ]
              | qs -> qs
           in
           let ses = ses |> List.map (fun sp ->
                             { sp with sigquals = sigquals@sp.sigquals; sigattrs = se.sigattrs@sp.sigattrs}) in
           let ses = ses |> List.map (Compress.deep_compress_se false false) in
           ses
      else ses
    in
    let ses = ses |> List.map (fun se ->
      if env.is_iface && Sig_declare_typ? se.sigel
      then { se with sigquals = Assumption :: (List.filter (fun q -> q <> Irreducible) se.sigquals) }
      else se)
    in
    let ses = ses |> List.map (fun sp -> { sp with sigmeta = { sp.sigmeta with
                                            sigmeta_spliced = true;
                                            (* the splice stands for a declaration of a language
                                               extension (e.g. a Pulse `fn`); keep that marker on
                                               the declarations it produces *)
                                            sigmeta_extension_decl = se.sigmeta.sigmeta_extension_decl } }) in

    let dsenv = List.fold_left DsEnv.push_sigelt_force env.dsenv ses in
    let env = { env with dsenv = dsenv } in

    if Debug.low () then
      Format.print1 "Splice returned sigelts {\n%s\n}\n"
        (String.concat "\n" <| List.map show ses);

    (* sigelts returned by splice_t can be marked with sigmeta
    already_checked, and those will be skipped on the next run. But they do
    run through the pipeline again. This also allows a splice tactic
    to return any mixture of checked and unchecked sigelts. *)
    [], ses, env

  | Sig_let {lbs; lids} ->
    Profiling.profile
      (fun () -> tc_sig_let env r se lbs lids)
      (Some (Ident.string_of_lid (Env.current_module env)))
      "FStarC.TypeChecker.Tc.tc_sig_let"
  )


(* [tc_decl env se] typechecks [se] in environment [env] and returns
 * the list of typechecked sig_elts, and a list of new sig_elts elaborated
 * during typechecking but not yet typechecked. This may also be called
 * on ALREADY CHECKED declarations coming out of a splice_t. See the
 * check for sigmeta_already_checked below. *)
let tc_decl env se: ML (list sigelt & list sigelt & Env.env) =
  FStarC.GenSym.reset_gensym();
  let env0 = env in
  let env = set_hint_correlator env se in
  let env =
    (* This is one point where we read admit_smt_queries
    and pass it through into the .admit field.
    This makes it so that if `--admit_smt_queries true` is
    set at the top-level, then it cannot be overridden in a local scope.
    Meanwhile, in Pulse it's useful to write #set-options "--admit_smt_queries true" { }
    for a particular scope. So, there is a second point where we
    read admit_smt_queries: in SMTEncoding.Solver.fst *)
    if Options.admit_smt_queries ()
    then { env with admit = true }
    else env
  in
  if Debug.any () then
    Format.print1 "Processing %s\n" (Print.sigelt_to_string_short se);
  if Debug.medium () then
    Format.print2 ">>>>>>>>>>>>>>tc_decl admit=%s %s\n" (show env.admit) (show se);
  let result =
    if se.sigmeta.sigmeta_already_checked then
      [se], [], env
    else if se.sigmeta.sigmeta_admit then (
      let result = tc_decl' { env with admit = true } se in
      result
    ) else
      tc_decl' env se
  in
  let () =
    (* Do the post-tc attribute/qualifier check. *)
    let (ses, _, _) = result in
    List.iter (Quals.check_sigelt_quals_post env) ses
  in
  (* Restore admit *)
  let result =
    let ses, ses_e, env = result in
    ses, ses_e, { env with admit = env0.admit }
  in
  result

(* adds the typechecked sigelt to the env, also performs any processing required in the env (such as reset options) *)
(* AR: we now call this function when loading checked modules as well to be more consistent *)
let add_sigelt_to_env (env:Env.env) (se:sigelt) (from_cache:bool) : ML Env.env =
  if Debug.low ()
  then Format.print2
    ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
    (Print.sigelt_to_string_short se) (show from_cache);

  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    raise_error se Errors.Fatal_UnexpectedInductiveType
      (Format.fmt1 "add_sigelt_to_env: unexpected bare type/data constructor: %s" (show se))

  | Sig_declare_typ _
  | Sig_let _ when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) -> env

  | _ ->
    (* When loading an already checked module, its declarations may include
       copies of the declarations of its interface, which was loaded before
       it; do not complain about those. *)
    let env = Env.push_sigelt env se in
    //match again to perform postprocessing
    match se.sigel with
    | Sig_pragma (PushOptions _)
    | Sig_pragma PopOptions
    | Sig_pragma (SetOptions _)
    | Sig_pragma (ResetOptions _) ->
      if from_cache then env
      else
        (* we keep --using_facts_from reflected in the environment, so update it here *)
        ({ env with proof_ns = Options.using_facts_from () })

    | Sig_pragma RestartSolver ->
      (* `flychecking` marks when an interactive F* is peeking via flycheck,
       * we shouldn't reset the solver at that point, only when the user
       * advances over the pragma. *)
      if from_cache || env.flychecking then env
      else begin
        env.solver.refresh (Some env.proof_ns);
        env
      end

    | Sig_pragma _ ->
      (* Others were already handled. *)
      env

    | Sig_new_effect ne ->
      Env.push_new_effect env (ne, se.sigquals)

    | Sig_sub_effect sub -> TcUtil.update_env_sub_eff env sub se.sigrng

    | _ -> env

(* This function is called when promoting entries in the id info table.
   If t has no dangling uvars, it is normalized and promoted,
   otherwise discarded *)
let compress_and_norm env t = 
    match Compress.deep_compress_if_no_uvars t with
    | None -> None //if dangling uvars, then just drop this entry
    | Some t ->  //otherwise, normalize and promote
      Some (
        N.normalize
               [Env.AllowUnboundUniverses; //this is allowed, since we're reducing types that appear deep within some arbitrary context
                Env.CheckNoUvars;
                Env.Beta; Env.DoNotUnfoldPureLets; Env.CompressUvars;
                Env.Exclude Env.Zeta; Env.Exclude Env.Iota; Env.NoFullNorm]
              env
              t
      )

(***********************************************************************)
(* Checking an implementation against its interface                    *)
(*                                                                     *)
(* When A.fst is checked and A.fsti exists, the *already checked*      *)
(* sigelts of A.fsti are held in [env.iface_todo] as an ordered to-do  *)
(* list. Nothing from the interface is ever rechecked: a `val` is      *)
(* discharged by checking that the implementation subsumes it, and any *)
(* other interface sigelt (a `let`, an inductive, ...) is copied over  *)
(* verbatim.                                                           *)
(*                                                                     *)
(* The to-do list doubles as a scope: as long as an entry sits on it,  *)
(* the names it defines are *not* visible to the implementation (see   *)
(* [Env.is_iface_hidden]). This reproduces the ordering discipline of  *)
(* the old syntactic interleaving and is what makes the whole scheme   *)
(* sound: were the interface visible in full from the start, A.fst     *)
(* could discharge `val one` using a definition of A.fsti that is      *)
(* itself justified by `one` --- a circular proof of anything.         *)
(***********************************************************************)

(* The `val`s of an interface carry the Assumption qualifier, since on their own
they are indeed assumptions. Once implemented they are not, so drop it when
copying the declaration into the implementation. *)
let unassume_iface_val (se:sigelt) : ML sigelt =
  match se.sigel with
  | Sig_declare_typ _ ->
    { se with sigquals = se.sigquals |> List.filter (fun q -> q <> Assumption) }
  | _ -> se

(* Is [se] a `val` of the interface, i.e. a declaration that the
implementation is expected to define? Auto-generated projectors and
discriminators are declarations too, but they come with their type and are
simply copied over. *)
let is_iface_val (se:sigelt) : ML bool =
  match se.sigel with
  | Sig_declare_typ _ ->
    not (se.sigquals |> BU.for_some (function
         | Projector _ | Discriminator _ -> true
         | _ -> false))
  | _ -> false

(* Check that the implementation of [l], whose checked sigelt is [impl],
subsumes the interface's `val l : us. t_iface`. We require the same number of
universe parameters and that the implementation's type is a subtype of the
declared one. *)
let check_subsumes_iface_val (env:Env.env) (iface_se:sigelt) (impl:sigelt) : ML unit =
  let open FStarC.Pprint in
  match iface_se.sigel with
  | Sig_declare_typ {lid=l; us=iface_us; t=iface_t} -> (
    let impl_scheme =
      match impl.sigel with
      | Sig_let {lbs=(_, lbs)} ->
        BU.find_map lbs (fun lb ->
                 if lid_equals (Inr?.v lb.lbname).fv_name l
                 then Some (lb.lbunivs, lb.lbtyp)
                 else None)
      | Sig_inductive_typ {us; t}
      | Sig_datacon {us; t}
      | Sig_declare_typ {us; t} -> Some (us, t)
      | _ -> None
    in
    match impl_scheme with
    | None ->
      (* Nothing to compare against: e.g. a splice or an effect definition.
         Those are accepted as-is, as they were before. *)
      ()
    | Some (impl_us, impl_t) ->
      if List.length impl_us <> List.length iface_us
      then raise_error impl Errors.Fatal_IncoherentInlineUniverse [
             prefix 2 1 (text "The implementation of") (pp l)
               ^/^ text "has a different number of universe parameters than its interface.";
             text (Format.fmt2 "The interface declares %s, the implementation has %s."
                     (show (List.length iface_us)) (show (List.length impl_us)))
           ];
      (* Relate the two types under a common set of universe binders. *)
      let us, iface_t = SS.open_univ_vars iface_us iface_t in
      let _, impl_t = Env.inst_tscheme_with (impl_us, impl_t) (us |> List.map U_name) in
      let env = Env.push_univ_vars env us in
      let env = Env.set_range env (range_of_sigelt impl) in
      match Rel.get_subtyping_predicate env impl_t iface_t with
      | None ->
        raise_error impl Errors.Fatal_InterfaceNotImplementedByModule [
          prefix 2 1 (text "The implementation of") (pp l)
            ^/^ text "does not match its declaration in the interface.";
          prefix 2 1 (text "Interface type:") (pp iface_t);
          prefix 2 1 (text "Implementation type:") (pp impl_t)
        ]
      | Some g ->
        Rel.force_trivial_guard env (Env.apply_guard g (S.fvar l None))
  )
  | _ -> ()

(* Split the interface to-do list against an implementation sigelt defining
[defs]. This follows the ordering discipline that the old syntactic
interleaving implemented:

  - leading interface sigelts that are not `val`s (definitions, inductives,
    projectors, ...) are copied verbatim into the implementation;
  - a `val` that [defs] discharges is consumed, together with the `val`s of the
    other members of its mutually recursive group;
  - a `val` that [defs] does not discharge stops the walk: the implementation
    declaration is simply a private definition of its own. It is however an
    error for [defs] to be declared *later* in the interface, since the
    definitions must appear in the order of their declarations.

This is what rules out circular proofs: an interface definition is justified by
the `val`s that precede it, so it must not come into scope until they have all
been implemented, or it could be used to discharge one of them. Declarations
introduced by a language extension (a Pulse `fn`, say) are no different from
plain `val`s in this respect.

Returns (copied, matched, remaining). *)
let split_iface_todo (se:sigelt) (defs:list lident) (todo:list sigelt)
  : ML (list sigelt & list sigelt & list sigelt) =
  let defines se' =
    U.lids_of_sigelt se' |> BU.for_some (fun l -> defs |> BU.for_some (lid_equals l))
  in
  let rec take_mutuals acc todo : ML (list sigelt & list sigelt) =
    match todo with
    | hd :: tl when is_iface_val hd && defines hd -> take_mutuals (hd::acc) tl
    | _ -> List.rev acc, todo
  in
  let rec go copied todo
    : ML (list sigelt & list sigelt & list sigelt) =
    match todo with
    | [] -> List.rev copied, [], []
    | hd :: tl ->
      if not (is_iface_val hd)
      then go (hd::copied) tl
      else if defines hd
      then let mutuals, rest = take_mutuals [] tl in
           List.rev copied, hd::mutuals, rest
      else (
        (* [hd] is not implemented here. Make sure we are not implementing
           something the interface only declares later on. *)
        (match tl |> List.tryFind (fun i -> is_iface_val i && defines i) with
         | Some out_of_order ->
           let open FStarC.Pprint in
           let l = List.hd (U.lids_of_sigelt out_of_order) in
           raise_error se Errors.Fatal_WrongDefinitionOrder [
             prefix 2 1 (text "Expected the definition of")
               (pp (List.hd (U.lids_of_sigelt hd)) ^/^ text "to precede" ^/^ pp l)
           ]
         | None -> ());
        List.rev copied, [], todo
      )
  in
  go [] todo

(* Discharge the head of the interface to-do list against the implementation
sigelt [se], which is about to be checked.

Returns the interface sigelts to be emitted verbatim ahead of [se] (which the
tick-off just brought into scope) and the interface `val`s that [se] is
expected to subsume. *)
let tick_off_iface_todo (env:Env.env) (se:sigelt)
  : ML (list sigelt & list sigelt & Env.env)
  = match Env.iface_todo env with
    | [] -> [], [], env
    | todo ->
      (* An `[@@expect_failure]` block defines nothing --- its declarations are
         checked with errors trapped and then thrown away --- so it must not
         discharge anything of the interface. Were it to do so, writing
             [@@expect_failure] let f = ...
         in A.fst would silently *admit* `val f` of A.fsti: the declaration
         would be ticked off the to-do list, and hence neither reported as
         unimplemented nor ever checked, while remaining an assumption for the
         rest of the module and for A.fst.checked. Interface definitions that
         precede the next unimplemented `val` are still copied over, so that the
         block is checked in the scope it would have had. *)
      let defs =
        match se.sigel with
        | Sig_fail _ -> []
        | _ -> U.lids_of_sigelt se
      in
      let copied, matched, remaining = split_iface_todo se defs todo in
      (* The entries we just walked past come into scope now; whatever is left
         of the to-do list stays hidden, so that [se] cannot be justified by an
         interface definition that the implementation has not reached yet. *)
      let env = Env.consume_iface_todo env (copied @ matched) remaining in
      (* An interface `val` that is being implemented is no longer an assumption. *)
      let matched_vals = List.map unassume_iface_val matched in
      (* Nothing needs to be added to the environment: the interface has
         already been checked and loaded in full; ticking the entries off the
         to-do list is what brings them into scope. *)
      copied @ matched_vals, matched_vals, env

(* Flush the remaining to-do list at the end of the module: any leftover `val`
is an unimplemented declaration, everything else is copied verbatim. *)
let finish_iface_todo (env:Env.env)
  : ML (list sigelt & Env.env)
  = let open FStarC.Pprint in
    let todo = Env.iface_todo env in
    let missing = todo |> List.filter is_iface_val in
    if Cons? missing
    then (
      let names = missing |> List.collect U.lids_of_sigelt in
      log_issue (range_of_sigelt (List.hd missing)) Errors.Fatal_InterfaceNotImplementedByModule [
        prefix 2 1
          (text (Format.fmt1 "Module %s fails to implement some declarations of its interface:"
                   (show (Env.current_module env))))
          (names |> List.map pp |> separate hardline)
      ]
    );
    let copied = todo |> List.filter (fun se -> not (is_iface_val se)) in
    copied, Env.set_iface_todo env []

(* When a module has an interface, its definitions that the interface does not
declare are private to the module. Extraction (in particular to C, via Karamel)
needs to know this, so tag them with the internal `KrmlPrivate` attribute; see
[FStarC.Extraction.ML.Modul.extract_meta]. This reproduces what the old
syntactic interleaving used to do. *)
let mark_karamel_private (env:Env.env) (se:sigelt) : ML sigelt =
  let lids = U.lids_of_sigelt se in
  if Options.Ext.get "no_krml_private" <> ""
  || not (Env.has_iface env)
  || Nil? lids
  || lids |> BU.for_some (Env.declared_in_iface env)
  then se
  else
    let rng = range_of_sigelt se in
    let attr = S.mk (Tm_constant (Const_string ("KrmlPrivate", rng))) rng in
    { se with sigattrs = attr :: se.sigattrs }

let tc_decls env ses : ML (list sigelt & Env.env) =
  let rec process_one_decl ses_env se : ML _ =
    let (ses, env) = ses_env in
    Errors.fallback_range := Some se.sigrng;

    (* If emacs is peeking, and debugging is on, don't do anything,
     * otherwise the user will see a bunch of output from typechecking
     * definitions that were not yet advanced over. *)
    if env.flychecking && Debug.any ()
    then (ses, env), []
    else begin
    if Debug.low ()
    then Format.print2 ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                        (tag_of se)
                        (Print.sigelt_to_string_short se);

    if Options.ide_id_info_off() then Env.toggle_id_info env false;
    if !dbg_IdInfoOn then Env.toggle_id_info env true;
    if Options.Ext.enabled "freshen" then
      env.solver.refresh (Some env.proof_ns);

    (* Tick off the entries of the interface's to-do list that this declaration
       discharges. Copied interface sigelts and the declarations being
       implemented are added to the environment and emitted before [se]. *)
    let iface_prefix, iface_matched, env =
      (* Sigelts produced by a splice are fed back through this loop; the splice
         itself has already discharged the interface declarations they define. *)
      if se.sigmeta.sigmeta_spliced
      then [], [], env
      else tick_off_iface_todo env se
    in

    (* The interface is not encoded to the solver while checking the
       implementation (its abstract view of the module would clash with the
       implementation's own encoding), so the sigelts we copy verbatim from the
       interface must be encoded here, before checking [se]. *)
    List.iter (fun se -> env.solver.encode_sig env se) iface_prefix;

    let ses', ses_elaborated, env =
            Errors.with_ctx (Format.fmt2 "While typechecking the %stop-level declaration ‘%s’"
                                  (if se.sigmeta.sigmeta_spliced then "(spliced) " else "")
                                  (Print.sigelt_to_string_short se))
                    (fun () -> tc_decl env se)
    in

    let ses' = ses' |> List.map (fun se ->
        if !dbg_UF
        then Format.print1 "About to elim vars from %s\n" (show se);
        N.elim_uvars env se) in
    let ses_elaborated = ses_elaborated |> List.map (fun se ->
        if !dbg_UF
        then Format.print1 "About to elim vars from (elaborated) %s\n" (show se);
        N.elim_uvars env se) in

    Env.promote_id_info env (compress_and_norm env);
          
    // Compress all checked sigelts. Uvars and names are not OK after a full typecheck
    let ses' = ses' |> List.map (Compress.deep_compress_se false false) in

    // Make sure to update all the delta_depths of the definitions we will add to the
    // environment. These can change if the body of the letbinding is transformed by any means,
    // such as by resolving an `_ by ...`, or a pre/post process hook.
    // let fixup_dd_lb (lb:letbinding) : letbinding =
    //   (* The delta depth of the fv is 1 + the dd of its body *)
    //   let Inr fv = lb.lbname in
    //   // Format.print2_error "Checking depth of %s = %s\n" (show lb.lbname) (show fv.fv_delta);
    //   // let dd = incr_delta_depth <| delta_qualifier lb.lbdef in
    //   let dd = incr_delta_depth <| delta_depth_of_term env lb.lbdef in
    //   // if Some dd <> fv.fv_delta then (
    //   //   Format.print3_error "Fixing up delta depth of %s from %s to %s\n" (show lb.lbname) (show fv.fv_delta) (show dd)
    //   // );
    //   // Format.print1_error "Definition = (%s)\n\n" (show lb.lbdef);
    //   let fv = { fv with fv_delta = Some dd } in
    //   { lb with lbname = Inr fv }
    // in
    // let fixup_delta_depth (se:sigelt) : sigelt =
    //   match se.sigel with
    //   | Sig_let {lbs; lids} ->
    //     let lbs = fst lbs, List.map fixup_dd_lb (snd lbs) in
    //     { se with sigel = Sig_let {lbs; lids} }
    //   | _ -> se
    // in
    // let ses' = ses' |> List.map fixup_delta_depth in

    let ses' = ses' |> List.map (mark_karamel_private env) in

    // Add to the environment
    let env = ses' |> List.fold_left (fun env se -> add_sigelt_to_env env se false) env in
    UF.reset();

    if Options.log_types () || Debug.medium () || !dbg_LogTypes
    then Format.print1 "Checked: %s\n" (show ses');

    (* The interface is not encoded to the solver while checking the
       implementation (its abstract view of the module would clash with the
       implementation's own encoding), so the sigelts we copy verbatim from the
       interface must be encoded here, right before the declaration that
       triggered them. *)
    Profiling.profile 
      (fun () -> List.iter (fun se -> env.solver.encode_sig env se) ses')
      (Some (Ident.string_of_lid (Env.current_module env)))      
      "FStarC.TypeChecker.Tc.encode_sig";


    (* Now that the implementation has been checked, verify that it really does
       subsume what the interface declared. *)
    iface_matched |> List.iter (fun iface_se ->
      let lids = U.lids_of_sigelt iface_se in
      ses' |> List.iter (fun impl ->
        if U.lids_of_sigelt impl |> BU.for_some (fun l -> lids |> BU.for_some (lid_equals l))
        then check_subsumes_iface_val env iface_se impl));

    (List.rev_append ses' (List.rev_append iface_prefix ses), env), ses_elaborated
    end
  in
  // A wrapper to (maybe) print the time taken for each sigelt
  let process_one_decl_timed acc se =
    FStarC.TypeChecker.Core.clear_memo_table();
    let (_, env) = acc in
    let r =
      Profiling.profile
                 (fun () -> process_one_decl acc se)
                 (Some (Ident.string_of_lid (Env.current_module env)))
                 "FStarC.TypeChecker.Tc.process_one_decl"
      // ^ See a special case for this phase in FStarC.Options. --timing
      // enables it.
    in
    if Options.profile_group_by_decl()
    || Options.timing () // --timing implies --profile_group_by_decl
    then begin
         let tag =
          match lids_of_sigelt se with
          | hd::_ -> Ident.string_of_lid hd
          | _ -> Range.string_of_range (range_of_sigelt se)
         in
         Profiling.report_and_clear tag
    end;
    r
  in
  let ses, env =
    UF.with_uf_enabled (fun () ->
      BU.fold_flatten process_one_decl_timed ([], env) ses) in
  List.rev_append ses [], env

let _ =
    tc_decls_knot := Some tc_decls

let tc_partial_modul env modul =
  let verify = Options.should_verify (string_of_lid modul.name) in
  let action = if verify then "verifying" else "lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Debug.any () then
    Format.print3 "Now %s %s of %s\n" action label (string_of_lid modul.name);

  let dsnap = Debug.snapshot () in
  if not (Options.should_check (string_of_lid modul.name)) && not (Options.debug_all_modules ())
  then Debug.disable_all ();

  let name = Format.fmt2 "%s %s" (if modul.is_interface then "interface" else "module") (string_of_lid modul.name) in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  let env = Env.set_current_module env modul.name in
  (* If this is the implementation of an interface we have already checked,
     seed the interface's checked sigelts as a to-do list. Nothing of the
     interface is rechecked: entries are ticked off as the implementation
     discharges them. See [tick_off_iface_todo]. *)
  let env =
    if modul.is_interface then env
    else
      match env.modules |> List.tryFind (fun m -> m.is_interface && lid_equals m.name modul.name) with
      | None -> env
      | Some iface ->
        let env = Env.set_iface_todo env iface.declarations in
        let env =
          Env.set_iface_lids env
            (iface.declarations |> List.collect U.lids_of_sigelt)
            (iface.declarations |> List.filter is_iface_val |> List.collect U.lids_of_sigelt)
        in
        let missing_decl0 = env.missing_decl in
        (* The interface's `val`s carry the Assumption qualifier (they are
           assumptions on their own). Within the implementation they are
           ordinary declarations, so shadow them with unassumed copies. *)
        let env =
          iface.declarations |> List.fold_left (fun env se ->
            if is_iface_val se
            then Env.push_sigelt_force env (unassume_iface_val se)
            else env) env
        in
        (* The interface's to-do list already tracks these; do not report them
           twice via [missing_definition_list]. *)
        { env with missing_decl = missing_decl0 }
  in
  (* Only set a context for dependencies *)
  Errors.with_ctx_if (not (Options.should_check (string_of_lid modul.name)))
                     (Format.fmt2 "While loading dependency %s%s"
                                    (string_of_lid modul.name)
                                    (if modul.is_interface then " (interface)" else "")) (fun () ->
    let ses, env = tc_decls env modul.declarations in
    Debug.restore dsnap;
    {modul with declarations=ses}, env
  )

let tc_more_partial_modul env modul decls =
  let ses, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, ses, env

let finish_partial_modul should_pop (loading_from_cache:bool) (en:env) (m:modul) : ML (modul & env) =
  //AR: do we ever call finish_partial_modul for current buffer in the interactive mode?
  if Debug.low () then
    Format.print3 "Finishing %s %s -- loading_from_cache=%s\n"
      (if m.is_interface then "interface" else "module")
      (show m.name)
      (show loading_from_cache);
  (* Flush whatever is left of the interface's to-do list, and complain about
     declarations of the interface that the implementation never defined. *)
  let m, en =
    if loading_from_cache then m, en
    else
      let trailing, en = finish_iface_todo en in
      {m with declarations=m.declarations@trailing}, en
  in
  let env = Env.finish_module en m in

  if not loading_from_cache then (
    let missing = missing_definition_list env in
    let mname_ids = ids_of_lid m.name in
    if Cons? missing then
      log_issue env Errors.Error_AdmitWithoutDefinition [
          Pprint.prefix 2 1 (text <| Format.fmt1 "Missing definitions in module %s:" (string_of_lid m.name))
            (Pprint.separate_map Pprint.hardline (fun l -> pp (ident_of_lid l)) missing)
        ]
  );

  //we can clear the lid to query index table
  env.qtbl_name_and_index |> snd |> SMap.clear;

  //pop BUT ignore the old env

  if should_pop then pop_context env ("Ending modul " ^ string_of_lid m.name) |> ignore;

  if Options.depth () > 0 then (
    Errors.log_issue env Error_MissingPopOptions
      ("Some #push-options have not been popped. Current depth is " ^ show (Options.depth()) ^ ".")
  );

  //moved the code for encoding the module to smt to Universal

  m, env

let deep_compress_modul (m:modul) : ML modul =
  { m with declarations = List.map (Compress.deep_compress_se false false) m.declarations }

let tc_modul (env0:env) (m:modul) : ML (modul & env) =
  let msg = "Internals for " ^ string_of_lid m.name in
  //AR: push env, this will also push solver, and then finish_partial_modul will do the pop
  let env0 = push_context env0 msg in
  let modul, env = tc_partial_modul env0 m in
  // Note: all sigelts returned by tc_partial_modul must already be compressed
  // by Syntax.compress.deep_compress, so they are safe to output.
  finish_partial_modul true false env modul

(* A checked implementation contains copies of the declarations of its
   interface. If the interface has already been loaded into [en] --- which is
   the normal case, since it is a dependency of the implementation --- those
   copies must not be pushed again. They are recognized by their name and
   range, as they are copied verbatim. *)
let sigelt_key (se:sigelt) : ML (list string & string) =
  U.lids_of_sigelt se |> List.map string_of_lid,
  Range.string_of_range (range_of_sigelt se)

let already_loaded_iface_decls (en:env) (m:modul) : ML (list (list string & string)) =
  if m.is_interface then []
  else
    match en.modules |> Option.find (fun mm -> lid_equals mm.name m.name && mm.is_interface) with
    | Some i -> i.declarations |> List.map sigelt_key
    | None -> []

(* [push] controls whether the module's sigelts are added under a fresh
   context snapshot.  Callers that go on to [finish_partial_modul true] need it;
   [load_checked_module] does not, since the env it keeps afterwards is the
   pushed one and the popped one is discarded -- so the snapshot only costs 9
   [SMap.copy]s per dependency. *)
let load_checked_module_sigelts (push:bool) (en:env) (m:modul) : ML env =
  //This function tries to very carefully mimic the effect of the environment
  //of having checked the module from scratch, i.e., using tc_module below
  let loaded = already_loaded_iface_decls en m in
  let env = Env.set_current_module en m.name in
  //push context, finish_partial_modul will do the pop
  let env =
    if push
    then push_context env ("Internals for " ^ Ident.string_of_lid m.name)
    else env
  in
  let env = List.fold_left (fun env se ->
             if Cons? loaded && List.mem (sigelt_key se) loaded then env else
             //add every sigelt in the environment
             let env = add_sigelt_to_env env se true in
             //and then query it back immediately to populate the environment's internal cache
             //this is important for extraction to work correctly,
             //in particular, when extracting a module we want the module's internal symbols
             //that may be marked "abstract" externally to be visible internally
             //populating the cache enables this behavior, rather indirectly, sadly : (
             let lids = Util.lids_of_sigelt se in
             lids |> List.iter (fun lid -> ignore (Env.lookup_sigelt env lid));
             env)
             env
             m.declarations in
  env

let load_checked_module (en:env) (m:modul) : ML env =
  (* Reset debug flags *)
  let dsnap = Debug.snapshot () in
  if not (Options.should_check (string_of_lid m.name)) && not (Options.debug_all_modules ())
  then Debug.disable_all ();

  let env = load_checked_module_sigelts false en m in
  //And then call finish_partial_modul, which is the normal workflow of tc_modul below
  //except with the flag `must_check_exports` set to false, since this is already a checked module
  let _, env = finish_partial_modul false true env m in
  Debug.restore dsnap;
  env

let load_partial_checked_module (en:env) (m:modul) : ML env =
  load_checked_module_sigelts true en m

let check_module env0 m : ML _ =
  if Debug.any()
  then Format.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (show m.name);
  if Options.dump_module (string_of_lid m.name)
  then Format.print1 "Module before type checking:\n%s\n" (show m);

  let env = {env0 with admit = not (Options.should_verify (string_of_lid m.name))} in
  let m, env = tc_modul env m in
  (* restore admit *)
  let env = { env with admit = env0.admit } in

  (* Debug information for level Normalize : normalizes all toplevel declarations an dump the current module *)
  if Options.dump_module (string_of_lid m.name)
  then Format.print1 "Module after type checking:\n%s\n" (show m);
  if Options.dump_module (string_of_lid m.name) && !dbg_Normalize
  then begin
    let normalize_toplevel_lets = fun se -> match se.sigel with
        | Sig_let {lbs=(b, lbs); lids=ids} ->
            let n = N.normalize [Env.Beta ; Env.Eager_unfolding; Env.Reify ; Env.Inlining ; Env.Primops ; Env.UnfoldUntil S.delta_constant ; Env.AllowUnboundUniverses ] in
            let update lb =
                let univnames, e = SS.open_univ_vars lb.lbunivs lb.lbdef in
                { lb with lbdef = n (Env.push_univ_vars env univnames) e }
            in
            { se with sigel = Sig_let {lbs=(b, List.map update lbs); lids=ids} }
        | _ -> se
    in
    let normalized_module = { m with declarations = List.map normalize_toplevel_lets m.declarations } in
    Format.print1 "%s\n" (show normalized_module)
  end;

  m, env
