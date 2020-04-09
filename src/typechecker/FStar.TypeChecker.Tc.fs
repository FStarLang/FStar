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
module N  = FStar.TypeChecker.Normalize
module TcComm = FStar.TypeChecker.Common
module TcUtil = FStar.TypeChecker.Util
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
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
        let t = mk (Tm_type(U_name u)) None r in
        let t = Subst.close_univ_vars [u] t in
        let tc = { sigel = Sig_inductive_typ(lex_t, [u], [], t, [], [PC.lextop_lid; PC.lexcons_lid]);
                   sigquals = [];
                   sigrng = r;
                   sigmeta = default_sigmeta;
                   sigattrs = [];
                   sigopts = None; } in

        let utop = S.new_univ_name (Some r1) in
        let lex_top_t = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r1) delta_constant None, [U_name utop])) None r1 in
        let lex_top_t = Subst.close_univ_vars [utop] lex_top_t in
        let dc_lextop = { sigel = Sig_datacon(lex_top, [utop], lex_top_t, PC.lex_t_lid, 0, []);
                          sigquals = [];
                          sigrng = r1;
                          sigmeta = default_sigmeta;
                          sigattrs = [];
                          sigopts = None; } in

        let ucons1 = S.new_univ_name (Some r2) in
        let ucons2 = S.new_univ_name (Some r2) in
        let lex_cons_t =
            let a = S.new_bv (Some r2) (mk (Tm_type(U_name ucons1)) None r2) in
            let hd = S.new_bv (Some r2) (S.bv_to_name a) in
            let tl = S.new_bv (Some r2) (mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_name ucons2])) None r2) in
            let res = mk (Tm_uinst(S.fvar (Ident.set_lid_range PC.lex_t_lid r2) delta_constant None, [U_max [U_name ucons1; U_name ucons2]])) None r2 in
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
    let uvs, t = TcUtil.generalize_universes env t in
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
        List.existsb (fun s -> s = (text_of_id (ident_of_lid lid))) TcInductive.early_prims_inductives in

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

(* A(nother) hacky knot, set by FStar.Main *)
let unembed_optionstate_knot : ref<option<EMB.embedding<O.optionstate>>> = BU.mk_ref None
let unembed_optionstate (t : term) : option<O.optionstate> =
    EMB.unembed (BU.must (!unembed_optionstate_knot)) t true EMB.id_norm_cb

let proc_check_with (attrs:list<attribute>) (kont : unit -> 'a) : 'a =
  match U.get_attribute PC.check_with_lid attrs with
  | None -> kont ()
  | Some [(a, None)] ->
    Options.with_saved_options (fun () ->
      Options.set (unembed_optionstate a |> BU.must);
      kont ())
  | _ -> failwith "huh?"

(* Alternative to making a huge let rec... knot is set below in this file *)
let tc_decls_knot : ref<option<(Env.env -> list<sigelt> -> list<sigelt> * list<sigelt> * Env.env)>> =
  BU.mk_ref None

let tc_decl' env0 se: list<sigelt> * list<sigelt> * Env.env =
  let env = env0 in
  TcUtil.check_sigelt_quals env se;
  proc_check_with se.sigattrs (fun () ->
  let r = se.sigrng in
  let se =
     if Options.record_options ()
     then { se with sigopts = Some (Options.peek ()) }
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

    if Env.debug env Options.Low then begin
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
            TcEff.tc_eff_decl ({ env with phase1 = true; lax = true }) ne se.sigquals
            |> (fun ne -> { se with sigel = Sig_new_effect ne })
            |> N.elim_uvars env |> U.eff_decl_of_new_effect in
          if Env.debug env <| Options.Other "TwoPhases"
          then BU.print1 "Effect decl after phase 1: %s\n"
                 (Print.sigelt_to_string ({ se with sigel = Sig_new_effect ne }));
          ne
        end
        else ne in
      let ne = TcEff.tc_eff_decl env ne se.sigquals in
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

  | Sig_main(e) ->
    let env = Env.set_range env r in
    let env = Env.set_expected_typ env t_unit in
    let e, c, g1 = tc_term env e in
    let e, _, g =
      let c, g_lc = TcComm.lcomp_comp c in
      let e, _x, g = check_expected_effect env (Some (U.ml_comp t_unit r)) (e, c) in
      e, _x, Env.conj_guard g_lc g in
    Rel.force_trivial_guard env (Env.conj_guard g1 g);
    let se = { se with sigel = Sig_main(e) } in
    [se], [], env0

  | Sig_splice (lids, t) ->
    if Options.debug_any () then
        BU.print2 "%s: Found splice of (%s)\n" (string_of_lid env.curmodule) (Print.term_to_string t);

    // Check the tactic
    let t, _, g = tc_tactic t_unit S.t_decls env t in
    Rel.force_trivial_guard env g;

    let ses = env.splice env t in
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
            BU.starts_with (text_of_id bv.ppname) Ident.reserved_prefix in
          let rec rename_binders def_bs val_bs =
            match def_bs, val_bs with
            | [], _ | _, [] -> val_bs
            | (body_bv, _) :: bt, (val_bv, aqual) :: vt ->
              (match has_auto_name body_bv, has_auto_name val_bv with
               | true, _ -> (val_bv, aqual)
               | false, true -> ({ val_bv with
                                   ppname = mk_ident (text_of_id body_bv.ppname, range_of_id val_bv.ppname) }, aqual)
               | false, false ->
                 // if (text_of_id body_bv.ppname) <> (text_of_id val_bv.ppname) then
                 //   Errors.warn (range_of_id body_bv.ppname)
                 //     (BU.format2 "Parameter name %s doesn't match name %s used in val declaration"
                 //                  (text_of_id body_bv.ppname) (text_of_id val_bv.ppname));
                 (val_bv, aqual)) :: rename_binders bt vt in
          Syntax.mk (Tm_arrow(rename_binders def_bs val_bs, c)) None r end
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
                if lb.lbunivs <> []
                then false, lb, quals_opt // we already have generalized universes (e.g. elaborated term)
                else gen, lb, quals_opt //no annotation found; use whatever was in the let binding

            | Some ((uvs,tval), quals) ->
              let quals_opt = check_quals_eq lbname.fv_name.v quals_opt quals in
              let def = match lb.lbtyp.n with
                | Tm_unknown -> lb.lbdef
                | _ ->
                  (* If there are two type ascriptions we check that they are compatible *)
                  mk (Tm_ascribed (lb.lbdef, (Inl lb.lbtyp, None), None)) None lb.lbdef.pos
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
    let e = mk (Tm_let((fst lbs, lbs'), mk (Tm_constant (Const_unit)) None r)) None r in

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
              tc_maybe_toplevel_term ({ env' with phase1 = true; lax = true }) e |> (fun (e, _, _) -> e) |> N.remove_uvar_solutions env' |> drop_lbtyp
            ) in
        if Env.debug env <| Options.Other "TwoPhases" then
          BU.print1 "Let binding after phase 1: %s\n"
            (Print.term_to_string e);
        if Env.debug env <| Options.Other "TCDeclTime" then
          BU.print1 "Let binding elaborated (phase 1) in %s milliseconds\n"
            (string_of_int ms);
        e
      end
      else e
    in

    let attrs, post_tau =
        match U.extract_attr' PC.postprocess_with se.sigattrs with
        | None -> se.sigattrs, None
        | Some (ats, [tau, None]) -> ats, Some tau
        | Some (ats, args) ->
            Errors.log_issue r (Errors.Warning_UnrecognizedAttribute,
                                   ("Ill-formed application of `postprocess_with`"));
            se.sigattrs, None
    in
    let se = { se with sigattrs = attrs } in (* to remove the postprocess_with *)
    let postprocess_lb (tau:term) (lb:letbinding) : letbinding =
        let lbdef = Env.postprocess env tau lb.lbtyp lb.lbdef in
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
    [se], [], env0)


(* [tc_decl env se] typechecks [se] in environment [env] and returns *
 * the list of typechecked sig_elts, and a list of new sig_elts elaborated
 * during typechecking but not yet typechecked *)
let tc_decl env se: list<sigelt> * list<sigelt> * Env.env =
  (* If emacs is peeking, and debugging is on, don't do anything,
   * otherwise the user will see a bunch of output from typechecking
   * definitions that were not yet advanced over. *)
  if env.nosynth && Options.debug_any ()
  then [], [], env
  else begin
   let env = set_hint_correlator env se in
   if Options.debug_module (string_of_lid env.curmodule) then
     BU.print1 "Processing %s\n" (U.lids_of_sigelt se |> List.map string_of_lid |> String.concat ", ");
   if Env.debug env Options.Low then
     BU.print1 ">>>>>>>>>>>>>>tc_decl %s\n" (Print.sigelt_to_string se);

   tc_decl' env se
  end

let for_export env hidden se : list<sigelt> * list<lident> =
   (* Exporting symbols based on whether they have been marked 'abstract'


        -- NB> Symbols marked 'private' are restricted by the visibility rules enforced during desugaring.
           i.e., if a module A marks symbol x as private, then a module B simply cannot refer to A.x
           OTOH, if A marks x as abstract, B can refer to A.x, but cannot see its definition.

      Here, if a symbol is abstract, we only export its declaration, not its definition.
      The reason we export the declaration of private symbols is to account for cases like this:

        module A
           abstract let x = 0
           let y = x

        When encoding A to the SMT solver, we need to encode the definition of y.
        If we simply eliminated x altogether when exporting it, the body of y would no longer be well formed.
        So, instead, in effect, we export A as

        module A
            assume val x : int
            let y = x

   *)
   let is_abstract quals = quals |> BU.for_some (function Abstract-> true | _ -> false) in
   let is_hidden_proj_or_disc q = match q with
      | Projector(l, _)
      | Discriminator l -> hidden |> BU.for_some (lid_equals l)
      | _ -> false
   in
   match se.sigel with
  | Sig_pragma         _ -> [], hidden

  | Sig_fail _
  | Sig_splice _
  | Sig_inductive_typ _
  | Sig_datacon _ -> failwith "Impossible (Already handled)"

  | Sig_bundle(ses, _) ->
    if is_abstract se.sigquals
    then
      let for_export_bundle se (out, hidden) = match se.sigel with
        | Sig_inductive_typ(l, us, bs, t, _, _) ->
          let dec = { se with sigel = Sig_declare_typ(l, us, U.arrow bs (S.mk_Total t));
                              sigquals=Assumption::New::se.sigquals } in
          dec::out, hidden

        (* logically, each constructor just becomes an uninterpreted function *)
        | Sig_datacon(l, us, t, _, _, _) ->
          let dec = { se with sigel = Sig_declare_typ(l, us, t);
                              sigquals = [Assumption] } in
          dec::out, l::hidden

        | _ ->
          out, hidden
      in
      List.fold_right for_export_bundle ses ([], hidden)
    else [se], hidden

  | Sig_assume(_, _, _) ->
    if is_abstract se.sigquals
    then [], hidden
    else [se], hidden

  | Sig_declare_typ(l, us, t) ->
    if se.sigquals |> BU.for_some is_hidden_proj_or_disc //hidden projectors/discriminators become uninterpreted
    then [{se with sigel = Sig_declare_typ(l, us, t);
                   sigquals = [Assumption] }],
         l::hidden
    else if se.sigquals |> BU.for_some (function
      | Assumption
      | Projector _
      | Discriminator _ -> true
      | _ -> false)
    then [se], hidden //Assumptions, Intepreted proj/disc are retained
    else [], hidden   //other declarations vanish
                      //they will be replaced by the definitions that must follow

  | Sig_main  _ -> [], hidden

  | Sig_new_effect     _
  | Sig_sub_effect     _
  | Sig_effect_abbrev  _
  | Sig_polymonadic_bind _ -> [se], hidden

  | Sig_let((false, [lb]), _)
        when se.sigquals |> BU.for_some is_hidden_proj_or_disc ->
    let fv = right lb.lbname in
    let lid = fv.fv_name.v in
    if hidden |> BU.for_some (S.fv_eq_lid fv)
    then [], hidden //this projector definition already has a declare_typ
    else let dec = { sigel = Sig_declare_typ(fv.fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals =[Assumption];
                     sigrng = Ident.range_of_lid lid;
                     sigmeta = default_sigmeta;
                     sigattrs = [];
                     sigopts = None; } in
          [dec], lid::hidden

  | Sig_let(lbs, l) ->
    if is_abstract se.sigquals
    then (snd lbs |>  List.map (fun lb ->
           { se with sigel = Sig_declare_typ((right lb.lbname).fv_name.v, lb.lbunivs, lb.lbtyp);
                     sigquals = Assumption::se.sigquals}),
          hidden)
    else [se], hidden

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

    | Sig_sub_effect sub -> TcUtil.update_env_sub_eff env sub

    | Sig_polymonadic_bind (m, n, p, _, ty) -> TcUtil.update_env_polymonadic_bind env m n p ty

    | _ -> env

let tc_decls env ses =
  let rec process_one_decl (ses, exports, env, hidden) se =
    if Env.debug env Options.Low
    then BU.print2 ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                        (Print.tag_of_sigelt se)
                        (Print.sigelt_to_string se);

    let ses', ses_elaborated, env = tc_decl env se in
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
    FStar.Syntax.Unionfind.reset();

    if Options.log_types() || Env.debug env <| Options.Other "LogTypes"
    then begin
      BU.print1 "Checked: %s\n" (List.fold_left (fun s se -> s ^ Print.sigelt_to_string se ^ "\n") "" ses')
    end;

    List.iter (fun se -> env.solver.encode_sig env se) ses';

    let exports, hidden =
      if Options.use_extracted_interfaces () then List.rev_append ses' exports, []
      else
        let accum_exports_hidden (exports, hidden) se =
          let se_exported, hidden = for_export env hidden se in
          List.rev_append se_exported exports, hidden
        in
        List.fold_left accum_exports_hidden (exports, hidden) ses'
    in
    (List.rev_append ses' ses, exports, env, hidden), ses_elaborated
  in
  // A wrapper to (maybe) print the time taken for each sigelt
  let process_one_decl_timed acc se =
    let (_, _, env, _) = acc in
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
  let ses, exports, env, _ = BU.fold_flatten process_one_decl_timed ([], [], env, []) ses in
  List.rev_append ses [], List.rev_append exports [], env

let _ =
    tc_decls_knot := Some tc_decls

(* Consider the module:
        module Test
        abstract type t = nat
        let f (x:t{x > 0}) : Tot t = x

   The type of f : x:t{x>0} -> t
   from the perspective of a client of Test
   is ill-formed, since it the sub-term `x > 0` requires x:int, not x:t

   `check_exports` checks the publicly visible symbols exported by a module
   to make sure that all of them have types that are well-formed from a client's
   perspective.
*)
open FStar.TypeChecker.Err
let check_exports env (modul:modul) exports : unit =
    let env = {env with lax=true; lax_universes=true; top_level=true} in
    let check_term lid univs t =
        let univs, t = SS.open_univ_vars univs t in
        if Env.debug (Env.set_current_module env modul.name) <| Options.Other "Exports"
        then BU.print3 "Checking for export %s <%s> : %s\n"
                (Print.lid_to_string lid)
                (univs |> List.map (fun x -> Print.univ_to_string (U_name x)) |> String.concat ", ")
                (Print.term_to_string t);
        let env = Env.push_univ_vars env univs in
        TcTerm.tc_trivial_guard env t |> ignore
    in
    let check_term lid univs t =
        let _ = Errors.message_prefix.set_prefix
                (BU.format2 "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
                        (Print.lid_to_string modul.name)
                        (Print.lid_to_string lid)) in
        check_term lid univs t;
        Errors.message_prefix.clear_prefix()
    in
    let rec check_sigelt = fun se -> match se.sigel with
        | Sig_bundle(ses, _) ->
          if not (se.sigquals |> List.contains Private)
          then ses |> List.iter check_sigelt
        | Sig_inductive_typ (l, univs, binders, typ, _, _) ->
          let t = S.mk (Tm_arrow(binders, S.mk_Total typ)) None se.sigrng in
          check_term l univs t
        | Sig_datacon(l , univs, t, _, _, _) ->
          check_term l univs t
        | Sig_declare_typ(l, univs, t) ->
          if not (se.sigquals |> List.contains Private)
          then check_term l univs t
        | Sig_let((_, lbs), _) ->
          if not (se.sigquals |> List.contains Private)
          then lbs |> List.iter (fun lb ->
               let fv = right lb.lbname in
               check_term fv.fv_name.v lb.lbunivs lb.lbtyp)
        | Sig_effect_abbrev(l, univs, binders, comp, flags) ->
          if not (se.sigquals |> List.contains Private)
          then let arrow = S.mk (Tm_arrow(binders, comp)) None se.sigrng in
               check_term l univs arrow
        | Sig_main _
        | Sig_assume _
        | Sig_new_effect _
        | Sig_sub_effect _
        | Sig_pragma _
        | Sig_polymonadic_bind _ -> ()

        | Sig_fail _
        | Sig_splice _ -> failwith "Impossible (Already handled)"
    in
    if Ident.lid_equals modul.name PC.prims_lid
    then ()
    else List.iter check_sigelt exports

(*
 * extract an interface from m
 * this function uses the environment ONLY for unfolding effect abbreviations to see if the effect is reifiable etc.
 *)
let extract_interface (en:env) (m:modul) :modul =
  let is_abstract = List.contains Abstract in
  let is_irreducible = List.contains Irreducible in
  let is_assume = List.contains Assumption in
  let filter_out_abstract = List.filter (fun q -> not (q = Abstract || q = Irreducible || q = Visible_default)) in
  let filter_out_abstract_and_noeq = List.filter (fun q -> not (q = Abstract || q = Noeq || q = Unopteq || q = Irreducible || q = Visible_default)) in  //abstract inductive should not have noeq and unopteq
  let filter_out_abstract_and_inline = List.filter (fun q -> not (q = Abstract || q = Irreducible || q = Visible_default || q = Inline_for_extraction || q = Unfold_for_unification_and_vcgen)) in

  //we need to filter out projectors and discriminators of abstract inductive datacons, so keep track of such datacons, and keep tycons for haseq purposes
  let abstract_inductive_tycons   = BU.mk_ref [] in
  let abstract_inductive_datacons = BU.mk_ref [] in

  let is_projector_or_discriminator_of_an_abstract_inductive (quals:list<qualifier>) :bool =
    List.existsML (fun q ->
      match q with
      | Discriminator l
      | Projector (l, _) -> true //List.existsb (fun l' -> lid_equals l l') !abstract_inductive_datacons
      | _ -> false
    ) quals
  in

  let vals_of_abstract_inductive (s:sigelt) :sigelts =
    let mk_typ_for_abstract_inductive (bs:binders) (t:typ) (r:Range.range) :typ =
      match bs with
      | [] -> t
      | _  ->
        (match t.n with
         | Tm_arrow (bs', c ) -> mk (Tm_arrow (bs@bs', c)) None r  //flattening arrows?
         | _ -> mk (Tm_arrow (bs, mk_Total t)) None r)  //Total ok?
    in

    match s.sigel with
    | Sig_inductive_typ (lid, uvs, bs, t, _, _) ->  //add a val declaration for the type
      let s1 = { s with sigel = Sig_declare_typ (lid, uvs, mk_typ_for_abstract_inductive bs t s.sigrng);
                        sigquals = Assumption::New::(filter_out_abstract_and_noeq s.sigquals) }  //Assumption qualifier seems necessary, else smt encoding waits for the definition for the symbol to be encoded
      in
      [s1]
    | _ -> failwith "Impossible!"
  in

  let val_of_lb (s:sigelt) (lid:lident) ((uvs, t): (univ_names * typ)) (lbdef:term) :sigelt =
    let attrs =
      if TcUtil.must_erase_for_extraction en lbdef then (lid_as_fv PC.must_erase_for_extraction_attr delta_constant None |> fv_to_tm)::s.sigattrs
      else s.sigattrs
    in
    { s with sigel = Sig_declare_typ (lid, uvs, t); sigquals = Assumption::(filter_out_abstract_and_inline s.sigquals); sigattrs = attrs }
  in

  (*
   * When do we keep the body of the letbinding in the interface ...
   *)
  let should_keep_lbdef (t:typ) :bool =
    let comp_effect_name (c:comp) :lident = //internal function, caller makes sure c is a Comp case
      match c.n with | Comp c -> c.effect_name | _ -> failwith "Impossible!"
    in

    let c_opt =
      //if t is unit, make c_opt = Some (Tot unit), this will then be culled finally
      if is_unit t then Some (S.mk_Total t) else match (SS.compress t).n with | Tm_arrow (_, c) -> Some c | _ -> None
    in

    match c_opt with
    | None -> true //we can't get the comp type for sure, e.g. t is not an arrow (say if..then..else), so keep the body
    | Some c ->
        // discard lemmas, we don't need their bodies
        if is_lemma_comp c
        then false
        else if is_pure_or_ghost_comp c // keep all pure functions
        then true
        else Env.is_reifiable_effect en (comp_effect_name c) //else only keep it if the effect is reifiable
  in

  let extract_sigelt (s:sigelt) :list<sigelt> =
    if Env.debug en Options.Extreme
    then BU.print1 "Extracting interface for %s\n" (Print.sigelt_to_string s);
    match s.sigel with
    | Sig_inductive_typ _
    | Sig_datacon _ -> failwith "Impossible! extract_interface: bare data constructor"

    | Sig_splice _ -> failwith "Impossible! extract_interface: trying to extract splice"

    | Sig_fail _ -> failwith "Impossible! extract_interface: trying to extract Sig_fail"

    | Sig_bundle (sigelts, lidents) ->
      if is_abstract s.sigquals then
        //for an abstract inductive type, we will only retain the type declarations, in an unbundled form
        sigelts |> List.fold_left (fun sigelts s ->
          match s.sigel with
          | Sig_inductive_typ (lid, _, _, _, _, _) -> abstract_inductive_tycons := lid::!abstract_inductive_tycons; (vals_of_abstract_inductive s)@sigelts
          | Sig_datacon (lid, _, _, _, _, _) ->
            abstract_inductive_datacons := lid::!abstract_inductive_datacons;
            sigelts  //nothing to do for datacons
          | _ -> failwith "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon"
        ) []
      else [s]  //if it is not abstract, retain the bundle as is
    | Sig_declare_typ (lid, uvs, t) ->
      //if it's a projector or discriminator of an abstract inductive, got to go
      if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      //if it's an assumption, no let is coming, so add it as is
      else if is_assume s.sigquals then [ { s with sigquals = filter_out_abstract s.sigquals } ]
      //else leave the decision to let
      else []
    | Sig_let (lbs, lids) ->
      //if it's a projector or discriminator of an abstract inductive, got to go
      if is_projector_or_discriminator_of_an_abstract_inductive s.sigquals then []
      else
        //extract the type annotations from all the letbindings
        let flbs, slbs = lbs in
        let typs_and_defs = slbs |> List.map (fun lb -> lb.lbunivs, lb.lbtyp, lb.lbdef) in

        let is_lemma = List.existsML (fun (_, t, _) -> t |> U.is_lemma) typs_and_defs in
        //if is it abstract or irreducible or lemma, keep just the vals
        let vals = List.map2 (fun lid (u, t, d) -> val_of_lb s lid (u, t) d) lids typs_and_defs in
        if is_abstract s.sigquals || is_irreducible s.sigquals || is_lemma then vals
        else
          let should_keep_defs = List.existsML (fun (_, t, _) -> t |> should_keep_lbdef) typs_and_defs in
          if should_keep_defs then [ s ]
          else vals
    | Sig_main t -> failwith "Did not anticipate main would arise when extracting interfaces!"
    | Sig_assume (lid, _, _) ->
      //keep hasEq of abstract inductive, and drop for others (since they will be regenerated)
      let is_haseq = TcInductive.is_haseq_lid lid in
      if is_haseq then
        let is_haseq_of_abstract_inductive = List.existsML (fun l -> lid_equals lid (TcInductive.get_haseq_axiom_lid l)) !abstract_inductive_tycons in
        if is_haseq_of_abstract_inductive then [ { s with sigquals = filter_out_abstract s.sigquals } ]
        else []
      else [ { s with sigquals = filter_out_abstract s.sigquals } ]
    | Sig_new_effect _
    | Sig_sub_effect _
    | Sig_effect_abbrev _
    | Sig_pragma _
    | Sig_polymonadic_bind _ -> [s]
  in

  { m with declarations = m.declarations |> List.map extract_sigelt |> List.flatten; is_interface = true }

let snapshot_context env msg = BU.atomically (fun () ->
    TypeChecker.Env.snapshot env msg)

let rollback_context solver msg depth : env = BU.atomically (fun () ->
    let env = TypeChecker.Env.rollback solver msg depth in
    env)

let push_context env msg = snd (snapshot_context env msg)
let pop_context env msg = rollback_context env.solver msg None

let tc_partial_modul env modul =
  let verify = Options.should_verify (string_of_lid modul.name) in
  let action = if verify then "Verifying" else "Lax-checking" in
  let label = if modul.is_interface then "interface" else "implementation" in
  if Options.debug_any () then
    BU.print3 "%s %s of %s\n" action label (string_of_lid modul.name);

  let name = BU.format2 "%s %s"  (if modul.is_interface then "interface" else "module") (string_of_lid modul.name) in
  let env = {env with Env.is_iface=modul.is_interface; admit=not verify} in
  let env = Env.set_current_module env modul.name in
  let ses, exports, env = tc_decls env modul.declarations in
  {modul with declarations=ses}, exports, env

let tc_more_partial_modul env modul decls =
  let ses, exports, env = tc_decls env decls in
  let modul = {modul with declarations=modul.declarations@ses} in
  modul, exports, env

let rec tc_modul (env0:env) (m:modul) (iface_exists:bool) :(modul * env) =
  let msg = "Internals for " ^ string_of_lid m.name in
  //AR: push env, this will also push solver, and then finish_partial_modul will do the pop
  let env0 = push_context env0 msg in
  let modul, non_private_decls, env = tc_partial_modul env0 m in
  finish_partial_modul false iface_exists env modul non_private_decls

and finish_partial_modul (loading_from_cache:bool) (iface_exists:bool) (en:env) (m:modul) (exports:list<sigelt>) : (modul * env) =
  //AR: do we ever call finish_partial_modul for current buffer in the interactive mode?
  let should_extract_interface =
    (not loading_from_cache)            &&
    (not iface_exists)                  &&
    Options.use_extracted_interfaces () &&
    (not m.is_interface)                &&
    FStar.Errors.get_err_count() = 0
  in
  if should_extract_interface then begin //if we are using extracted interfaces and this is not already an interface
    //extract the interface in the new environment, this helps us figure out things like if an effect is reifiable
    let modul_iface = extract_interface en m in
    if Env.debug en <| Options.Low then
      BU.print4 "Extracting and type checking module %s interface%s%s%s\n" (string_of_lid m.name)
                (if Options.should_verify (string_of_lid m.name) then "" else " (in lax mode) ")
                (if Options.dump_module (string_of_lid m.name) then ("\nfrom: " ^ (Syntax.Print.modul_to_string m) ^ "\n") else "")
                (if Options.dump_module (string_of_lid m.name) then ("\nto: " ^ (Syntax.Print.modul_to_string modul_iface) ^ "\n") else "");

    //set up the environment to verify the interface
    let en0 =
      //pop to get the env before this module type checking...
      let en0 = pop_context en ("Ending modul " ^ (string_of_lid m.name)) in
      //.. but restore the dsenv, since typechecking `m` might have elaborated
      // some %splices that we need to properly resolve further modules
      let en0 = { en0 with dsenv = en.dsenv } in
      //for hints, we want to use the same id counter as was used in typechecking the module itself, so use the tbl from latest env
      let en0 = { en0 with qtbl_name_and_index = en.qtbl_name_and_index |> fst, None } in
      //restore command line options ad restart z3 (to reset things like nl.arith options)
      if not (Options.interactive ()) then begin  //we should not have this case actually since extracted interfaces are not supported in ide yet
        Options.restore_cmd_line_options true |> ignore;
        en0
      end
      else en0
    in

    //AR: the third flag 'true' is for iface_exists for the current file, since it's an iface already, pass true
    let modul_iface, env = tc_modul en0 modul_iface true in
    { m with exports = modul_iface.exports }, env  //note: setting the exports for m, once extracted_interfaces is default, exports should just go away
  end
  else
    let modul = { m with exports = exports } in
    let env = Env.finish_module en modul in

    //we can clear the lid to query index table
    env.qtbl_name_and_index |> fst |> BU.smap_clear;

    if not (Options.lax())
    && not loading_from_cache
    && not (Options.use_extracted_interfaces ())
    then check_exports env modul exports;

    //pop BUT ignore the old env
    pop_context env ("Ending modul " ^ string_of_lid modul.name) |> ignore;

    //moved the code for encoding the module to smt to Universal

    modul, env

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
  let _, env = finish_partial_modul true true env m m.exports in
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
