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
#light "off"
module FStar.TypeChecker.Tc
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.TcTerm

module S  = FStar.Syntax.Syntax
module SP  = FStar.Syntax.Print
module SS = FStar.Syntax.Subst
module UF = FStar.Syntax.Unionfind
module N  = FStar.TypeChecker.Normalize
module TcComm = FStar.TypeChecker.Common
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module Gen = FStar.TypeChecker.Generalize
module TcInductive = FStar.TypeChecker.TcInductive
module TcEff = FStar.TypeChecker.TcEffect
module PC = FStar.Parser.Const
module EMB = FStar.Syntax.Embeddings
module ToSyntax = FStar.ToSyntax.ToSyntax
module O = FStar.Options

//set the name of the query so that we can correlate hints to source program fragments
let set_hint_correlator env se =
    //if the tbl has a counter for lid, we use that, else we start from 0
    //this is useful when we verify the extracted interface alongside
    let tbl = env.qtbl_name_and_index |> fst in
    let get_n lid =
      let n_opt = BU.smap_try_find tbl (string_of_lid lid) in
      if is_some n_opt then n_opt |> must else 0
    in

    match Options.reuse_hint_for () with
    | Some l ->
      let lid = Ident.lid_add_suffix (Env.current_module env) l in
      {env with qtbl_name_and_index=tbl, Some (lid, get_n lid)}

    | None ->
      let lids = U.lids_of_sigelt se in
      let lid = match lids with
            | [] -> Ident.lid_add_suffix (Env.current_module env)
                                         (Ident.next_id () |> BU.string_of_int)
            | l::_ -> l in
      {env with qtbl_name_and_index=tbl, Some (lid, get_n lid)}

let log env = (Options.log_types()) &&  not(lid_equals PC.prims_lid (Env.current_module env))


(*****************Type-checking the signature of a module*****************************)

let tc_lex_t env ses quals lids =
    (* We specifically type lex_t as:

          type lex_t<u> : Type(u) =
          datacon LexTop<utop>  : lex_t<utop>
          datacon LexCons<ucons1, ucons2> : #a:Type(ucons1) -> hd:a -> tl:lex_t<ucons2> -> lex_t<max ucons1 ucons2>
    *)
    assert (quals = []);
    let err_range = (List.hd ses).sigrng in
    begin match lids with
        | [lex_t; lex_top; lex_cons] when
            (lid_equals lex_t PC.lex_t_lid
             && lid_equals lex_top PC.lextop_lid
             && lid_equals lex_cons PC.lexcons_lid) -> ()
        | _ -> Errors.raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, ("Invalid (partial) redefinition of lex_t")) err_range
    end;
    begin match ses with
      //AR: we were enforcing the univs to be [], which breaks down when we have two phases
      //    the typechecking of lex_t is anyway hardcoded, so it should be fine to ignore that restriction
      | [{ sigel = Sig_inductive_typ(lex_t, _, [], t, _, _);  sigquals = []; sigrng = r };
         { sigel = Sig_datacon(lex_top, _, _t_top, _lex_t_top, 0, _); sigquals = []; sigrng = r1 };
         { sigel = Sig_datacon(lex_cons, _, _t_cons, _lex_t_cons, 0, _); sigquals = []; sigrng = r2 }]
         when (lid_equals lex_t PC.lex_t_lid
            && lid_equals lex_top PC.lextop_lid
            && lid_equals lex_cons PC.lexcons_lid) ->

        let u = S.new_univ_name (Some r) in
        let t = mk (Tm_type(U_name u)) r in
        let t = Subst.close_univ_vars [u] t in
        let tc = { sigel = Sig_inductive_typ(lex_t, [u], [], t, [], [PC.lextop_lid; PC.lexcons_lid]);
                   sigquals = [];
                   sigrng = r;
                   sigmeta = default_sigmeta;
                   sigattrs = [];
                   sigopts = None; } in

        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r1) delta_constant None, [U_zero])) r1 in
        let dc_lextop = { sigel = Sig_datacon(lex_top, [], lex_top_t, PC.lex_t_lid, 0, []);
                          sigquals = [];
                          sigrng = r1;
                          sigmeta = default_sigmeta;
                          sigattrs = [];
                          sigopts = None; } in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_name ucons2])) r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) r2 in
            U.arrow [(a, Some S.imp_tag); (hd, None); (tl, None)] (S.mk_Total res) in
        let lex_cons_t = Subst.close_univ_vars [ucons1;ucons2]  lex_cons_t in
        let dc_lexcons = { sigel = Sig_datacon(lex_cons, [ucons1;ucons2], lex_cons_t, PC.lex_t_lid, 0, []);
                           sigquals = [];
                           sigrng = r2;
                           sigmeta = default_sigmeta;
                           sigattrs = [];
                           sigopts = None; } in
        { sigel = Sig_bundle([tc; dc_lextop; dc_lexcons], lids);
          sigquals = [];
          sigrng = Env.get_range env;
          sigmeta = default_sigmeta;
          sigattrs = [];
          sigopts = None; }
      | _ ->
        let err_msg =
          BU.format1 "Invalid (re)definition of lex_t: %s\n"
            (Print.sigelt_to_string (mk_sigelt (Sig_bundle(ses, lids))))
        in
        raise_error (Errors.Fatal_InvalidRedefinitionOfLexT, err_msg) err_range
    end

let tc_type_common (env:env) ((uvs, t):tscheme) (expected_typ:typ) (r:Range.range) :tscheme =
  let uvs, t = SS.open_univ_vars uvs t in
  let env = Env.push_univ_vars env uvs in
  let t = tc_check_trivial_guard env t expected_typ in
  if uvs = [] then
    let uvs, t = Gen.generalize_universes env t in
    //AR: generalize_universes only calls N.reduce_uvar_solutions, so make sure there are no uvars left
    TcUtil.check_uvars r t;
    uvs, t
  else uvs, t |> N.remove_uvar_solutions env |> SS.close_univ_vars uvs

let tc_declare_typ (env:env) (ts:tscheme) (r:Range.range) :tscheme =
  tc_type_common env ts (U.type_u () |> fst) r

let tc_assume (env:env) (ts:tscheme) (r:Range.range) :tscheme =
  //AR: this might seem same as tc_declare_typ but come prop, this will change
  tc_type_common env ts (U.type_u () |> fst) r

let tc_inductive' env ses quals attrs lids =
    if Env.debug env Options.Low then
        BU.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" (FStar.Common.string_of_list Print.sigelt_to_string ses);

    let sig_bndle, tcs, datas = TcInductive.check_inductive_well_typedness env ses quals lids in
    (* we have a well-typed inductive;
            we still need to check whether or not it supports equality
            and whether it is strictly positive
       *)

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
       let env = Env.push_sigelt env sig_bndle in
       (* Check positivity of the inductives within the Sig_bundle *)
       List.iter (fun ty ->
         let b = TcInductive.check_positivity ty env in
         if not b then
           let lid, r =
             match ty.sigel with
             | Sig_inductive_typ (lid, _, _, _, _, _) -> lid, ty.sigrng
             | _                                         -> failwith "Impossible!"
           in
           Errors.log_issue r (Errors.Error_InductiveTypeNotSatisfyPositivityCondition, ("Inductive type " ^ (string_of_lid lid) ^ " does not satisfy the positivity condition"))
         else ()
       ) tcs;

       (* Separately, if any of the data constructors in the Sig_bundle are
        * exceptions, check their positivity separately. See issue #1535 *)
       List.iter (fun d ->
         let data_lid, ty_lid =
            match d.sigel with
            | Sig_datacon (data_lid, _, _, ty_lid, _, _) -> data_lid, ty_lid
            | _ -> failwith "Impossible"
         in
         if lid_equals ty_lid PC.exn_lid && not (TcInductive.check_exn_positivity data_lid env) then
            Errors.log_issue d.sigrng
                     (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                        ("Exception " ^ (string_of_lid data_lid) ^ " does not satisfy the positivity condition"))
       ) datas
    end;

    //generate hasEq predicate for this inductive

    let skip_haseq =
      //skip logical connectives types in prims, tcs is bound to the inductive type, caller ensures its length is > 0
      let skip_prims_type (_:unit) :bool =
        let lid =
          let ty = List.hd tcs in
          match ty.sigel with
          | Sig_inductive_typ (lid, _, _, _, _, _) -> lid
          | _                                         -> failwith "Impossible"
        in
        //these are the prims type we are skipping
        List.existsb (fun s -> s = (string_of_id (ident_of_lid lid))) TcInductive.early_prims_inductives in

      let is_noeq = List.existsb (fun q -> q = Noeq) quals in

      //caller ensures tcs length is > 0
      //assuming that we have already propagated attrs from the bundle to its elements
      let is_erasable () = U.has_attribute (List.hd tcs).sigattrs FStar.Parser.Const.erasable_attr in

      List.length tcs = 0 ||
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

(*
 *  Given `val t : Type` in an interface
 *  and   `let t = e`    in the corresponding implementation
 *  The val declaration should contains the `must_erase_for_extraction` attribute
 *  if and only if `e` is a type that's non-informative (e..g., unit, t -> unit, etc.)
 *)
let check_must_erase_attribute env se =
    match se.sigel with
    | Sig_let(lbs, l) ->
        if not (Options.ide())
        then
        begin
          match DsEnv.iface_decls (Env.dsenv env) (Env.current_module env) with
          | None ->
            ()

          | Some iface_decls ->
            snd lbs |> List.iter (fun lb ->
                let lbname = BU.right lb.lbname in
                let has_iface_val =
                    iface_decls |> BU.for_some (FStar.Parser.AST.decl_is_val (ident_of_lid lbname.fv_name.v))
                in
                if has_iface_val
                then
                    let must_erase =
                      TcUtil.must_erase_for_extraction env lb.lbdef in
                    let has_attr =
                      Env.fv_has_attr env
                                      lbname
                                      FStar.Parser.Const.must_erase_for_extraction_attr in
                    if must_erase && not has_attr
                    then
                        FStar.Errors.log_issue
                            (range_of_fv lbname)
                            (FStar.Errors.Error_MustEraseMissing,
                                BU.format2
                                    "Values of type `%s` will be erased during extraction, \
                                    but its interface hides this fact. Add the `must_erase_for_extraction` \
                                    attribute to the `val %s` declaration for this symbol in the interface"
                                    (Print.fv_to_string lbname)
                                    (Print.fv_to_string lbname)
                                    )
                    else if has_attr && not must_erase
                    then FStar.Errors.log_issue
                        (range_of_fv lbname)
                        (FStar.Errors.Error_MustEraseMissing,
                            BU.format1
                                "Values of type `%s` cannot be erased during extraction, \
                                but the `must_erase_for_extraction` attribute claims that it can. \
                                Please remove the attribute."
                                (Print.fv_to_string lbname)
                                ))
    end

    | _ -> ()

let proc_check_with (attrs:list<attribute>) (kont : unit -> 'a) : 'a =
  match U.get_attribute PC.check_with_lid attrs with
  | None -> kont ()
  | Some [(a, None)] ->
    match EMB.unembed EMB.e_vconfig a true EMB.id_norm_cb with
    | None -> failwith "nah"
    | Some vcfg ->
    Options.with_saved_options (fun () ->
      Options.set_vconfig vcfg;
      kont ())
  | _ -> failwith "ill-formed `check_with`"

let handle_postprocess_with_attr (env:Env.env) (ats:list<attribute>)
    : (list<attribute> * option<term>)
=
    (* We find postprocess_for_extraction_with attrs, which we don't
     * have to handle here, but we typecheck the tactic
     * and elaborate it. *)
    let tc_and_elab_tactic (env:Env.env) (tau:term) : term =
        let tau, _, g_tau = tc_tactic t_unit t_unit env tau in
        Rel.force_trivial_guard env g_tau;
        tau
    in
    let ats =
      match U.extract_attr' PC.postprocess_extr_with ats with
      | None -> ats
      | Some (ats, [tau, None]) ->
        let tau = tc_and_elab_tactic env tau in
        (* Further, give it a spin through deep_compress to remove uvar nodes,
         * since this term will be picked up at extraction time when
         * the UF graph is blown away. *)
        let tau = SS.deep_compress tau in
        (U.mk_app (S.tabbrev PC.postprocess_extr_with) [tau, None])
           :: ats
      | Some (ats, [tau, None]) ->
        Errors.log_issue (Env.get_range env)
                         (Errors.Warning_UnrecognizedAttribute,
                            BU.format1 "Ill-formed application of `%s`"
                                       (string_of_lid PC.postprocess_extr_with));
        ats
    in
    (* Now extract the postprocess_with, if any, and also check it *)
    match U.extract_attr' PC.postprocess_with ats with
    | None -> ats, None
    | Some (ats, [tau, None]) ->
        ats, Some (tc_and_elab_tactic env tau)
    | Some (ats, args) ->
        Errors.log_issue (Env.get_range env)
                         (Errors.Warning_UnrecognizedAttribute,
                            BU.format1 "Ill-formed application of `%s`"
                                       (string_of_lid PC.postprocess_with));
        ats, None

let store_sigopts (se:sigelt) : sigelt =
  { se with sigopts = Some (Options.get_vconfig ()) }

(* Alternative to making a huge let rec... knot is set below in this file *)
let tc_decls_knot : ref<option<(Env.env -> list<sigelt> -> list<sigelt> * Env.env)>> =
  BU.mk_ref None

let tc_decl' env0 se: list<sigelt> * list<sigelt> * Env.env =
  let env = env0 in
  TcUtil.check_sigelt_quals env se;
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
  | Sig_fail (_, false, _) when not (Env.should_verify env) || Options.admit_smt_queries () ->
    [], [], env

  | Sig_fail (expected_errors, lax, ses) ->
    let env' = if lax then { env with lax = true } else env in
    let env' = Env.push env' "expect_failure" in
    (* We need to call push since tc_decls will encode the sigelts that
     * succeed to SMT, which may be relevant in checking the ones that
     * follow it. See #1956 for an example of what goes wrong if we
     * don't pop the context (spoiler: we prove false). *)

    if Env.debug env Options.Low then
        BU.print1 ">> Expecting errors: [%s]\n" (String.concat "; " <| List.map string_of_int expected_errors);

    let errs, _ = Errors.catch_errors (fun () ->
                    Options.with_saved_options (fun () ->
                      BU.must (!tc_decls_knot) env' ses)) in

    if Options.print_expected_failures ()
       || Env.debug env Options.Low then
    begin
        BU.print_string ">> Got issues: [\n";
        List.iter Errors.print_issue errs;
        BU.print_string ">>]\n"
    end;

    (* Pop environment, reset SMT context *)
    let _ = Env.pop env' "expect_failure" in

    let actual_errors = List.concatMap (fun i -> FStar.Common.list_of_option i.issue_number) errs in

    begin match errs with
    | [] ->
        List.iter Errors.print_issue errs;
        Errors.log_issue se.sigrng (Errors.Error_DidNotFail, "This top-level definition was expected to fail, but it succeeded")
    | _ ->
        if expected_errors <> [] then
          match Errors.find_multiset_discrepancy expected_errors actual_errors with
          | None -> ()
          | Some (e, n1, n2) ->
            List.iter Errors.print_issue errs;
            Errors.log_issue
                     se.sigrng
                     (Errors.Error_DidNotFail,
                      BU.format5 "This top-level definition was expected to raise error codes %s, \
                                  but it raised %s. Error #%s was raised %s times, instead of %s."
                                    (FStar.Common.string_of_list string_of_int expected_errors)
                                    (FStar.Common.string_of_list string_of_int actual_errors)
                                    (string_of_int e) (string_of_int n2) (string_of_int n1))
    end;
    [], [], env

  | Sig_bundle(ses, lids) when (lids |> BU.for_some (lid_equals PC.lex_t_lid)) ->
    //lex_t is very special; it uses a more expressive form of universe polymorphism than is allowed elsewhere
    //Instead of this special treatment, we could make use of explicit lifts, but LexCons is used pervasively
    (*
        type lex_t<u> =
          | LexTop<u>  : lex_t<u>
          | LexCons<u1, u2> : #a:Type(u1) -> a -> lex_t<u2> -> lex_t<max u1 u2>
    *)
    let env = Env.set_range env r in
    let se = tc_lex_t env ses se.sigquals lids  in
    [se], [], env0

  | Sig_bundle(ses, lids) ->
    let env = Env.set_range env r in
    let ses =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        //we generate extra sigelts even in the first phase, and then throw them away, would be nice to not generate them at all
        let ses =
          tc_inductive ({ env with phase1 = true; lax = true }) ses se.sigquals se.sigattrs lids
          |> fst
          |> N.elim_uvars env
          |> U.ses_of_sigbundle in
        if Env.debug env <| Options.Other "TwoPhases"
        then BU.print1 "Inductive after phase 1: %s\n" (Print.sigelt_to_string ({ se with sigel = Sig_bundle (ses, lids) }));
        ses
      end
      else ses
    in
    let sigbndle, projectors_ses = tc_inductive env ses se.sigquals se.sigattrs lids in
    let sigbndle = { sigbndle with sigattrs = se.sigattrs } in (* keep the attributes *)
    [ sigbndle ], projectors_ses, env0

  | Sig_pragma p ->  //no need for two-phase here
    U.process_pragma p r;
    [se], [], env0

  | Sig_new_effect ne ->
    let is_unelaborated_dm4f =
      match ne.combinators with
      | DM4F_eff combs ->
        (match combs.ret_wp |> snd |> SS.compress with
         | { n = Tm_unknown } -> true
         | _ -> false)
       | _ -> false in

    if is_unelaborated_dm4f then
      let env = Env.set_range env r in
      let ses, ne, lift_from_pure_opt = TcEff.dmff_cps_and_elaborate env ne in
      let effect_and_lift_ses = match lift_from_pure_opt with
        | Some lift -> [ { se with sigel = Sig_new_effect (ne) } ; lift ]
        | None -> [ { se with sigel = Sig_new_effect (ne) } ] in

      //only elaborate, the loop in tc_decls would send these back to us for typechecking
      [], ses @ effect_and_lift_ses, env0
    else       
      let ne =
        if Options.use_two_phase_tc () && Env.should_verify env then begin
          let ne =
            TcEff.tc_eff_decl ({ env with phase1 = true; lax = true }) ne se.sigquals se.sigattrs
            |> (fun ne -> { se with sigel = Sig_new_effect ne })
            |> N.elim_uvars env |> U.eff_decl_of_new_effect in
          if Env.debug env <| Options.Other "TwoPhases"
          then BU.print1 "Effect decl after phase 1: %s\n"
                 (Print.sigelt_to_string ({ se with sigel = Sig_new_effect ne }));
          ne
        end
        else ne in
      let ne = TcEff.tc_eff_decl env ne se.sigquals se.sigattrs in
      let se = { se with sigel = Sig_new_effect(ne) } in
      [se], [], env0

  | Sig_sub_effect(sub) ->  //no need to two-phase here, since lifts are already lax checked
    let sub = TcEff.tc_lift env sub r in
    let se = { se with sigel = Sig_sub_effect sub } in
    [se], [], env

  | Sig_effect_abbrev (lid, uvs, tps, c, flags) ->
    let lid, uvs, tps, c =
      if Options.use_two_phase_tc () && Env.should_verify env
      then
        TcEff.tc_effect_abbrev ({ env with phase1 = true; lax = true }) (lid, uvs, tps, c) r
        |> (fun (lid, uvs, tps, c) -> { se with sigel = Sig_effect_abbrev (lid, uvs, tps, c, flags) })
        |> N.elim_uvars env |>
        (fun se -> match se.sigel with
                | Sig_effect_abbrev (lid, uvs, tps, c, _) -> lid, uvs, tps, c
                | _ -> failwith "Did not expect Sig_effect_abbrev to not be one after phase 1")
      else lid, uvs, tps, c in

    let lid, uvs, tps, c = TcEff.tc_effect_abbrev env (lid, uvs, tps, c) r in
    let se = { se with sigel = Sig_effect_abbrev (lid, uvs, tps, c, flags) } in
    [se], [], env0

  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _)
      when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) ->
      (* Dummy declaration which must be erased since it has been elaborated somewhere else *)
      [], [], env0

  | Sig_declare_typ(lid, uvs, t) -> //NS: No checks on the qualifiers?
    let env = Env.set_range env r in

    if lid_exists env lid
    then raise_error (Errors.Fatal_AlreadyDefinedTopLevelDeclaration, (BU.format1 "Top-level declaration %s for a name that is already used in this module; \
                                   top-level declarations must be unique in their module"
                                   (Ident.string_of_lid lid))) r;

    let uvs, t =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        let uvs, t = tc_declare_typ ({ env with phase1 = true; lax = true }) (uvs, t) se.sigrng in //|> N.normalize [Env.NoFullNorm; Env.Beta; Env.DoNotUnfoldPureLets] env in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print2 "Val declaration after phase 1: %s and uvs: %s\n" (Print.term_to_string t) (Print.univ_names_to_string uvs);
        uvs, t
      end
      else uvs, t
    in

    let uvs, t = tc_declare_typ env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_declare_typ (lid, uvs, t) }], [], env0

  | Sig_assume(lid, uvs, t) ->
    FStar.Errors.log_issue r
                 (Warning_WarnOnUse,
                  BU.format1 "Admitting a top-level assumption %s" (Print.lid_to_string lid));
    let env = Env.set_range env r in

    let uvs, t =
      if Options.use_two_phase_tc () && Env.should_verify env then begin
        let uvs, t = tc_assume ({ env with phase1 = true; lax = true }) (uvs, t) se.sigrng in
        if Env.debug env <| Options.Other "TwoPhases" then BU.print2 "Assume after phase 1: %s and uvs: %s\n" (Print.term_to_string t) (Print.univ_names_to_string uvs);
        uvs, t
      end
      else uvs, t
    in

    let uvs, t = tc_assume env (uvs, t) se.sigrng in
    [ { se with sigel = Sig_assume (lid, uvs, t) }], [], env0

  | Sig_splice (lids, t) ->
    if Options.debug_any () then
        BU.print2 "%s: Found splice of (%s)\n" (string_of_lid env.curmodule) (Print.term_to_string t);

    // Check the tactic
    let t, _, g = tc_tactic t_unit S.t_decls env t in
    Rel.force_trivial_guard env g;

    let ses = env.splice env se.sigrng t in
    let lids' = List.collect U.lids_of_sigelt ses in
    List.iter (fun lid ->
        match List.tryFind (Ident.lid_equals lid) lids' with
        (* If env.nosynth is on, nothing will be generated, so don't raise an error
         * so flycheck does spuriously not mark the line red *)
        | None when not env.nosynth ->
            raise_error (Errors.Fatal_SplicedUndef, BU.format2 "Splice declared the name %s but it was not defined.\nThose defined were: %s" (string_of_lid lid) (String.concat ", " <| List.map string_of_lid lids')) r
        | _ -> ()
    ) lids;
    let dsenv = List.fold_left DsEnv.push_sigelt_force env.dsenv ses in
    let env = { env with dsenv = dsenv } in

    if Env.debug env Options.Low then
        BU.print1 "Splice returned sigelts {\n%s\n}\n" (String.concat "\n" <| List.map Print.sigelt_to_string ses);

    [], ses, env

  | Sig_let(lbs, lids) ->
    let env = Env.set_range env r in
    let check_quals_eq l qopt val_q = match qopt with
      | None -> Some val_q
      | Some q' ->
        //logic is now a deprecated qualifier, so discard it from the checking
        let drop_logic = List.filter (fun x -> not (x = Logic)) in
        if (let val_q, q' = drop_logic val_q, drop_logic q' in
            List.length val_q = List.length q'
            && List.forall2 U.qualifier_equal val_q q')
        then Some q'  //but retain it in the returned list of qualifiers, some code may still add type annotations of Type0, which will hinder `logical` inference
        else raise_error (Errors.Fatal_InconsistentQualifierAnnotation, (BU.format3 "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              (Print.lid_to_string l)
                              (Print.quals_to_string val_q)
                              (Print.quals_to_string q'))) r
    in

    let rename_parameters lb =
      let rename_in_typ def typ =
        let typ = Subst.compress typ in
        let def_bs = match (Subst.compress def).n with
                     | Tm_abs (binders, _, _) -> binders
                     | _ -> [] in
        match typ with
        | { n = Tm_arrow(val_bs, c); pos = r } -> begin
          let has_auto_name bv =
            BU.starts_with (string_of_id bv.ppname) Ident.reserved_prefix in
          let rec rename_binders def_bs val_bs =
            match def_bs, val_bs with
            | [], _ | _, [] -> val_bs
            | (body_bv, _) :: bt, (val_bv, aqual) :: vt ->
              (match has_auto_name body_bv, has_auto_name val_bv with
               | true, _ -> (val_bv, aqual)
               | false, true -> ({ val_bv with
                                   ppname = mk_ident (string_of_id body_bv.ppname, range_of_id val_bv.ppname) }, aqual)
               | false, false ->
                 // if (string_of_id body_bv.ppname) <> (string_of_id val_bv.ppname) then
                 //   Errors.warn (range_of_id body_bv.ppname)
                 //     (BU.format2 "Parameter name %s doesn't match name %s used in val declaration"
                 //                  (string_of_id body_bv.ppname) (string_of_id val_bv.ppname));
                 (val_bv, aqual)) :: rename_binders bt vt in
          Syntax.mk (Tm_arrow(rename_binders def_bs val_bs, c)) r end
        | _ -> typ in
      { lb with lbtyp = rename_in_typ lb.lbdef lb.lbtyp } in

    (* 1. (a) Annotate each lb in lbs with a type from the corresponding val decl, if there is one
          (b) Generalize the type of lb only if none of the lbs have val decls nor explicit universes
      *)
    let should_generalize, lbs', quals_opt =
       snd lbs |> List.fold_left (fun (gen, lbs, quals_opt) lb ->
          let lbname = right lb.lbname in //this is definitely not a local let binding
          let gen, lb, quals_opt = match Env.try_lookup_val_decl env lbname.fv_name.v with
            | None ->
                gen, lb, quals_opt

            | Some ((uvs,tval), quals) ->
              let quals_opt = check_quals_eq lbname.fv_name.v quals_opt quals in
              let def = match lb.lbtyp.n with
                | Tm_unknown -> lb.lbdef
                | _ ->
                  (* If there are two type ascriptions we check that they are compatible *)
                  mk (Tm_ascribed (lb.lbdef, (Inl lb.lbtyp, None), None)) lb.lbdef.pos
              in
              if lb.lbunivs <> [] && List.length lb.lbunivs <> List.length uvs
              then raise_error (Errors.Fatal_IncoherentInlineUniverse, ("Inline universes are incoherent with annotation from val declaration")) r;
              false, //explicit annotation provided; do not generalize
              mk_lb (Inr lbname, uvs, PC.effect_ALL_lid, tval, def, [], lb.lbpos),
              quals_opt
          in
          gen, lb::lbs, quals_opt)
          (true, [], (if se.sigquals=[] then None else Some se.sigquals))
    in

    let quals = match quals_opt with
      | None -> [Visible_default]
      | Some q ->
        if q |> BU.for_some (function Irreducible | Visible_default | Unfold_for_unification_and_vcgen -> true | _ -> false)
        then q
        else Visible_default::q //the default visibility for a let binding is Unfoldable
    in

    let lbs' = List.rev lbs' in

    (* preprocess_with *)
    let attrs, pre_tau =
        match U.extract_attr' PC.preprocess_with se.sigattrs with
        | None -> se.sigattrs, None
        | Some (ats, [tau, None]) -> ats, Some tau
        | Some (ats, args) ->
            Errors.log_issue r (Errors.Warning_UnrecognizedAttribute,
                                   ("Ill-formed application of `preprocess_with`"));
            se.sigattrs, None
    in
    let se = { se with sigattrs = attrs } in (* to remove the preprocess_with *)

    let preprocess_lb (tau:term) (lb:letbinding) : letbinding =
        let lbdef = Env.preprocess env tau lb.lbdef in
        if Env.debug env <| Options.Other "TwoPhases" then
          BU.print1 "lb preprocessed into: %s\n" (Print.term_to_string lbdef);
        { lb with lbdef = lbdef }
    in
    // Preprocess the letbindings with the tactic, if any
    let lbs' = match pre_tau with
               | Some tau -> List.map (preprocess_lb tau) lbs'
               | None -> lbs'
    in
    (* / preprocess_with *)

    (* 2. Turn the top-level lb into a Tm_let with a unit body *)
    let e = mk (Tm_let((fst lbs, lbs'), mk (Tm_constant (Const_unit)) r)) r in

    (* 3. Type-check the Tm_let and convert it back to Sig_let *)
    let env' = { env with top_level = true; generalize = should_generalize } in
    let e =
      if Options.use_two_phase_tc () && Env.should_verify env' then begin
        let drop_lbtyp (e_lax:term) :term =
          match (SS.compress e_lax).n with
          | Tm_let ((false, [ lb ]), e2) ->
            let lb_unannotated =
              match (SS.compress e).n with  //checking type annotation on e, the lb before phase 1, capturing e from above
              | Tm_let ((_, [ lb ]), _) ->
                (match (SS.compress lb.lbtyp).n with
                 | Tm_unknown -> true
                 | _ -> false)
              | _                       -> failwith "Impossible: first phase lb and second phase lb differ in structure!"
            in
            if lb_unannotated then { e_lax with n = Tm_let ((false, [ { lb with lbtyp = S.tun } ]), e2)}  //erase the type annotation
            else e_lax
          | _ -> e_lax  //leave recursive lets as is
        in
        let (e, ms) =
            BU.record_time (fun () ->
              let (e, _, _) = tc_maybe_toplevel_term ({ env' with phase1 = true; lax = true }) e in
              e)
        in
        if Env.debug env <| Options.Other "TCDeclTime" then
          BU.print1 "Let binding elaborated (phase 1) in %s milliseconds, now removing uvars\n"
            (string_of_int ms);

        if Env.debug env <| Options.Other "TwoPhases" then
          BU.print1 "Let binding after phase 1, before removing uvars: %s\n"
            (Print.term_to_string e);

        let e = N.remove_uvar_solutions env' e |> drop_lbtyp in

        if Env.debug env <| Options.Other "TwoPhases" then
          BU.print1 "Let binding after phase 1, uvars removed: %s\n"
            (Print.term_to_string e);
        e
      end
      else e
    in
    let attrs, post_tau = handle_postprocess_with_attr env se.sigattrs in
    (* remove the postprocess_with, if any *)
    let se = { se with sigattrs = attrs } in

    let postprocess_lb (tau:term) (lb:letbinding) : letbinding =
        let s, univnames = SS.univ_var_opening lb.lbunivs in
        let lbdef = SS.subst s lb.lbdef in
        let lbtyp = SS.subst s lb.lbtyp in
        let env = Env.push_univ_vars env univnames in
        let lbdef = Env.postprocess env tau lbtyp lbdef in
        let lbdef = SS.close_univ_vars univnames lbdef in
        { lb with lbdef = lbdef }
    in
    let (r, ms) = BU.record_time (fun () -> tc_maybe_toplevel_term env' e) in
    if Env.debug env <| Options.Other "TCDeclTime" then
      BU.print1 "Let binding typechecked in phase 2 in %s milliseconds\n"
        (string_of_int ms);

    let se, lbs = match r with
      | {n=Tm_let(lbs, e)}, _, g when Env.is_trivial g ->
        // Propagate binder names into signature
        let lbs = (fst lbs, (snd lbs) |> List.map rename_parameters) in

        // Postprocess the letbindings with the tactic, if any
        let lbs = (fst lbs,
                    (match post_tau with
                     | Some tau -> List.map (postprocess_lb tau) (snd lbs)
                     | None -> (snd lbs)))
        in

        //propagate the MaskedEffect tag to the qualifiers
        let quals = match e.n with
            | Tm_meta(_, Meta_desugared Masked_effect) -> HasMaskedEffect::quals
            | _ -> quals
        in
        { se with sigel = Sig_let(lbs, lids);
                  sigquals =  quals },
        lbs
      | _ -> failwith "impossible (typechecking should preserve Tm_let)"
    in

    (* 4. Record the type of top-level lets, and log if requested *)
    snd lbs |> List.iter (fun lb ->
        let fv = right lb.lbname in
        Env.insert_fv_info env fv lb.lbtyp);

    if log env
    then BU.print1 "%s\n" (snd lbs |> List.map (fun lb ->
          let should_log = match Env.try_lookup_val_decl env (right lb.lbname).fv_name.v with
              | None -> true
              | _ -> false in
          if should_log
          then BU.format2 "let %s : %s" (Print.lbname_to_string lb.lbname) (Print.term_to_string (*env*) lb.lbtyp)
          else "") |> String.concat "\n");

    check_must_erase_attribute env0 se;

    [se], [], env0

  | Sig_polymonadic_bind (m, n, p, t, _) ->  //desugaring does not set the last field, tc does
    let t =
      if Options.use_two_phase_tc () && Env.should_verify env then
        let t, ty =
          TcEff.tc_polymonadic_bind ({ env with phase1 = true; lax = true }) m n p t
          |> (fun (t, ty) -> { se with sigel = Sig_polymonadic_bind (m, n, p, t, ty) })
          |> N.elim_uvars env
          |> (fun se ->
             match se.sigel with
             | Sig_polymonadic_bind (_, _, _, t, ty) -> t, ty
             | _ -> failwith "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
        if Env.debug env <| Options.Other "TwoPhases"
          then BU.print1 "Polymonadic bind after phase 1: %s\n"
                 (Print.sigelt_to_string ({ se with sigel = Sig_polymonadic_bind (m, n, p, t, ty) }));
        t
      else t in
    let t, ty = TcEff.tc_polymonadic_bind env m n p t in
    let se = ({ se with sigel = Sig_polymonadic_bind (m, n, p, t, ty) }) in
    [se], [], env0

  | Sig_polymonadic_subcomp (m, n, t, _) ->  //desugaring does not set the last field, tc does
    let t =
      if Options.use_two_phase_tc () && Env.should_verify env then
        let t, ty =
          TcEff.tc_polymonadic_subcomp ({ env with phase1 = true; lax = true }) m n t
          |> (fun (t, ty) -> { se with sigel = Sig_polymonadic_subcomp (m, n, t, ty) })
          |> N.elim_uvars env
          |> (fun se ->
             match se.sigel with
             | Sig_polymonadic_subcomp (_, _, t, ty) -> t, ty
             | _ -> failwith "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
        if Env.debug env <| Options.Other "TwoPhases"
          then BU.print1 "Polymonadic subcomp after phase 1: %s\n"
                 (Print.sigelt_to_string ({ se with sigel = Sig_polymonadic_subcomp (m, n, t, ty) }));
        t
      else t in
    let t, ty = TcEff.tc_polymonadic_subcomp env m n t in
    let se = ({ se with sigel = Sig_polymonadic_subcomp (m, n, t, ty) }) in
    [se], [], env0)


(* [tc_decl env se] typechecks [se] in environment [env] and returns *
 * the list of typechecked sig_elts, and a list of new sig_elts elaborated
 * during typechecking but not yet typechecked *)
let tc_decl env se: list<sigelt> * list<sigelt> * Env.env =
   let env = set_hint_correlator env se in
   if Options.debug_module (string_of_lid env.curmodule) then
     BU.print1 "Processing %s\n" (U.lids_of_sigelt se |> List.map string_of_lid |> String.concat ", ");
   if Env.debug env Options.Low then
     BU.print1 ">>>>>>>>>>>>>>tc_decl %s\n" (Print.sigelt_to_string se);
   if se.sigmeta.sigmeta_admit
   then begin
     let old = Options.admit_smt_queries () in
     Options.set_admit_smt_queries true;  
     let result = tc_decl' env se in
     Options.set_admit_smt_queries old;
     result
   end
   else tc_decl' env se


(* adds the typechecked sigelt to the env, also performs any processing required in the env (such as reset options) *)
(* AR: we now call this function when loading checked modules as well to be more consistent *)
let add_sigelt_to_env (env:Env.env) (se:sigelt) (from_cache:bool) : Env.env =
  if Env.debug env Options.Low
  then BU.print2
    ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
    (Print.sigelt_to_string se) (string_of_bool from_cache);

  match se.sigel with
  | Sig_inductive_typ _
  | Sig_datacon _ ->
    raise_error (Errors.Fatal_UnexpectedInductivetype, BU.format1
      "add_sigelt_to_env: unexpected bare type/data constructor: %s" (Print.sigelt_to_string se)) se.sigrng

  | Sig_declare_typ (_, _, _)
  | Sig_let (_, _) when se.sigquals |> BU.for_some (function OnlyName -> true | _ -> false) -> env

  | _ ->
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
      (* `nosynth` actually marks when fstar-mode is peeking via flycheck,
       * we shouldn't reset the solver at that point, only when the user
       * advances over the pragma. *)
      if from_cache || env.nosynth then env
      else begin
        env.solver.refresh ();
        env
      end

    | Sig_new_effect ne ->
      let env = Env.push_new_effect env (ne, se.sigquals) in
      ne.actions |> List.fold_left (fun env a -> Env.push_sigelt env (U.action_as_lb ne.mname a a.action_defn.pos)) env

    | Sig_sub_effect sub -> TcUtil.update_env_sub_eff env sub se.sigrng

    | Sig_polymonadic_bind (m, n, p, _, ty) -> TcUtil.update_env_polymonadic_bind env m n p ty

    | Sig_polymonadic_subcomp (m, n, _, ty) -> Env.add_polymonadic_subcomp env m n ty

    | _ -> env

let tc_decls env ses =
  let rec process_one_decl (ses, env) se =
    (* If emacs is peeking, and debugging is on, don't do anything,
     * otherwise the user will see a bunch of output from typechecking
     * definitions that were not yet advanced over. *)
    if env.nosynth && Options.debug_any ()
    then (ses, env), []
    else begin
    if Env.debug env Options.Low
    then BU.print2 ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                        (Print.tag_of_sigelt se)
                        (Print.sigelt_to_string se);

    let ses', ses_elaborated, env =
            Errors.with_ctx (BU.format1 "While typechecking the top-level declaration `%s`" (Print.sigelt_to_string_short se))
                    (fun () -> tc_decl env se)
    in

    let ses' = ses' |> List.map (fun se ->
        if Env.debug env (Options.Other "UF")
        then BU.print1 "About to elim vars from %s\n" (Print.sigelt_to_string se);
        N.elim_uvars env se) in
    let ses_elaborated = ses_elaborated |> List.map (fun se ->
        if Env.debug env (Options.Other "UF")
        then BU.print1 "About to elim vars from (elaborated) %s\n" (Print.sigelt_to_string se);
        N.elim_uvars env se) in

    Env.promote_id_info env (fun t ->
        N.normalize
               [Env.AllowUnboundUniverses; //this is allowed, since we're reducing types that appear deep within some arbitrary context
                Env.CheckNoUvars;
                Env.Beta; Env.DoNotUnfoldPureLets; Env.CompressUvars;
                Env.Exclude Env.Zeta; Env.Exclude Env.Iota; Env.NoFullNorm]
              env
              t); //update the id_info table after having removed their uvars
    let env = ses' |> List.fold_left (fun env se -> add_sigelt_to_env env se false) env in
    UF.reset();

    if Options.log_types() || Env.debug env <| Options.Other "LogTypes"
    then begin
      BU.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ Print.sigelt_to_string se ^ "\n") "" ses')
    end;

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    (List.rev_append ses' ses, env), ses_elaborated
    end
  in
  // A wrapper to (maybe) print the time taken for each sigelt
  let process_one_decl_timed acc se =
    let (_, env) = acc in
    let r =
      Profiling.profile
                 (fun () -> process_one_decl acc se)
                 (Some (Ident.string_of_lid (Env.current_module env)))
                 "FStar.TypeChecker.Tc.process_one_decl"
    in
    if Options.profile_group_by_decls()
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

let snapshot_context env msg = BU.atomically (fun () ->
    TypeChecker.Env.snapshot env msg)

let rollback_context solver msg depth : env = BU.atomically (fun () ->
    let env = TypeChecker.Env.rollback solver msg depth in
    env)

let push_context env msg = snd (snapshot_context env msg)
let pop_context env msg = rollback_context env.solver msg None

let tc_partial_modul env modul =
  let verify = Options.should_verify (string_of_lid modul.name) in
  let action = if verify then "verifying" else "lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Options.debug_any () then
    BU.print3 "Now %s %s of %s\n" action label (string_of_lid modul.name);

  let name = BU.format2 "%s %s" (if modul.is_interface then "interface" else "module") (string_of_lid modul.name) in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  let env = Env.set_current_module env modul.name in
  (* Only set a context for dependencies *)
  Errors.with_ctx_if (not (Options.should_check (string_of_lid modul.name)))
                     (BU.format2 "While loading dependency %s%s"
                                    (string_of_lid modul.name)
                                    (if modul.is_interface then " (interface)" else "")) (fun () ->
    let ses, env = tc_decls env modul.declarations in
    {modul with declarations=ses}, env
  )

let tc_more_partial_modul env modul decls =
  let ses, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, ses, env

let finish_partial_modul (loading_from_cache:bool) (iface_exists:bool) (en:env) (m:modul) : (modul * env) =
  //AR: do we ever call finish_partial_modul for current buffer in the interactive mode?
  let env = Env.finish_module en m in

  //we can clear the lid to query index table
  env.qtbl_name_and_index |> fst |> BU.smap_clear;

  //pop BUT ignore the old env
  pop_context env ("Ending modul " ^ string_of_lid m.name) |> ignore;

  //moved the code for encoding the module to smt to Universal

  m, env

let tc_modul (env0:env) (m:modul) (iface_exists:bool) :(modul * env) =
  let msg = "Internals for " ^ string_of_lid m.name in
  //AR: push env, this will also push solver, and then finish_partial_modul will do the pop
  let env0 = push_context env0 msg in
  let modul, env = tc_partial_modul env0 m in
  finish_partial_modul false iface_exists env modul

let load_checked_module (en:env) (m:modul) :env =
  //This function tries to very carefully mimic the effect of the environment
  //of having checked the module from scratch, i.e., using tc_module below
  let env = Env.set_current_module en m.name in
  //push context, finish_partial_modul will do the pop
  let env = push_context env ("Internals for " ^ Ident.string_of_lid m.name) in
  let env = List.fold_left (fun env se ->
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
  //And then call finish_partial_modul, which is the normal workflow of tc_modul below
  //except with the flag `must_check_exports` set to false, since this is already a checked module
  //the second true flag is for iface_exists, used to determine whether should extract interface or not
  let _, env = finish_partial_modul true true env m in
  env

let check_module env m b =
  if Options.debug_any()
  then BU.print2 "Checking %s: %s\n" (if m.is_interface then "i'face" else "module") (Print.lid_to_string m.name);
  if Options.dump_module (string_of_lid m.name)
  then BU.print1 "Module before type checking:\n%s\n" (Print.modul_to_string m);

  let env = {env with lax=not (Options.should_verify (string_of_lid m.name))} in
  let m, env = tc_modul env m b in

  (* Debug information for level Normalize : normalizes all toplevel declarations an dump the current module *)
  if Options.dump_module (string_of_lid m.name)
  then BU.print1 "Module after type checking:\n%s\n" (Print.modul_to_string m);
  if Options.dump_module (string_of_lid m.name) && Options.debug_at_level (string_of_lid m.name) (Options.Other "Normalize")
  then begin
    let normalize_toplevel_lets = fun se -> match se.sigel with
        | Sig_let ((b, lbs), ids) ->
            let n = N.normalize [Env.Beta ; Env.Eager_unfolding; Env.Reify ; Env.Inlining ; Env.Primops ; Env.UnfoldUntil S.delta_constant ; Env.AllowUnboundUniverses ] in
            let update lb =
                let univnames, e = SS.open_univ_vars lb.lbunivs lb.lbdef in
                { lb with lbdef = n (Env.push_univ_vars env univnames) e }
            in
            { se with sigel = Sig_let ((b, List.map update lbs), ids) }
        | _ -> se
    in
    let normalized_module = { m with declarations = List.map normalize_toplevel_lets m.declarations } in
    BU.print1 "%s\n" (Print.modul_to_string normalized_module)
  end;

  m, env
