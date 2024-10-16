open Prims
let (dbg_TwoPhases : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "TwoPhases"
let (dbg_IdInfoOn : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "IdInfoOn"
let (dbg_Normalize : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "Normalize"
let (dbg_UF : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "UF"
let (dbg_LogTypes : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "LogTypes"
let (sigelt_typ :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = uu___; FStarC_Syntax_Syntax.us = uu___1;
          FStarC_Syntax_Syntax.params = uu___2;
          FStarC_Syntax_Syntax.num_uniform_params = uu___3;
          FStarC_Syntax_Syntax.t = t; FStarC_Syntax_Syntax.mutuals = uu___4;
          FStarC_Syntax_Syntax.ds = uu___5;
          FStarC_Syntax_Syntax.injective_type_params = uu___6;_}
        -> FStar_Pervasives_Native.Some t
    | FStarC_Syntax_Syntax.Sig_datacon
        { FStarC_Syntax_Syntax.lid1 = uu___;
          FStarC_Syntax_Syntax.us1 = uu___1; FStarC_Syntax_Syntax.t1 = t;
          FStarC_Syntax_Syntax.ty_lid = uu___2;
          FStarC_Syntax_Syntax.num_ty_params = uu___3;
          FStarC_Syntax_Syntax.mutuals1 = uu___4;
          FStarC_Syntax_Syntax.injective_type_params1 = uu___5;_}
        -> FStar_Pervasives_Native.Some t
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = uu___;
          FStarC_Syntax_Syntax.us2 = uu___1; FStarC_Syntax_Syntax.t2 = t;_}
        -> FStar_Pervasives_Native.Some t
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = (uu___, lb::uu___1);
          FStarC_Syntax_Syntax.lids1 = uu___2;_}
        -> FStar_Pervasives_Native.Some (lb.FStarC_Syntax_Syntax.lbtyp)
    | uu___ -> FStar_Pervasives_Native.None
let (set_hint_correlator :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      let tbl =
        FStar_Pervasives_Native.snd
          env.FStarC_TypeChecker_Env.qtbl_name_and_index in
      let get_n lid =
        let n_opt =
          let uu___ = FStarC_Class_Show.show FStarC_Ident.showable_lident lid in
          FStarC_Compiler_Util.smap_try_find tbl uu___ in
        if FStarC_Compiler_Util.is_some n_opt
        then FStarC_Compiler_Util.must n_opt
        else Prims.int_zero in
      let typ =
        let uu___ = sigelt_typ se in
        match uu___ with
        | FStar_Pervasives_Native.Some t -> t
        | uu___1 -> FStarC_Syntax_Syntax.tun in
      let uu___ = FStarC_Options.reuse_hint_for () in
      match uu___ with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu___1 = FStarC_TypeChecker_Env.current_module env in
            FStarC_Ident.lid_add_suffix uu___1 l in
          let uu___1 =
            let uu___2 =
              let uu___3 = let uu___4 = get_n lid in (lid, typ, uu___4) in
              FStar_Pervasives_Native.Some uu___3 in
            (uu___2, tbl) in
          {
            FStarC_TypeChecker_Env.solver =
              (env.FStarC_TypeChecker_Env.solver);
            FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
            FStarC_TypeChecker_Env.curmodule =
              (env.FStarC_TypeChecker_Env.curmodule);
            FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
            FStarC_TypeChecker_Env.gamma_sig =
              (env.FStarC_TypeChecker_Env.gamma_sig);
            FStarC_TypeChecker_Env.gamma_cache =
              (env.FStarC_TypeChecker_Env.gamma_cache);
            FStarC_TypeChecker_Env.modules =
              (env.FStarC_TypeChecker_Env.modules);
            FStarC_TypeChecker_Env.expected_typ =
              (env.FStarC_TypeChecker_Env.expected_typ);
            FStarC_TypeChecker_Env.sigtab =
              (env.FStarC_TypeChecker_Env.sigtab);
            FStarC_TypeChecker_Env.attrtab =
              (env.FStarC_TypeChecker_Env.attrtab);
            FStarC_TypeChecker_Env.instantiate_imp =
              (env.FStarC_TypeChecker_Env.instantiate_imp);
            FStarC_TypeChecker_Env.effects =
              (env.FStarC_TypeChecker_Env.effects);
            FStarC_TypeChecker_Env.generalize =
              (env.FStarC_TypeChecker_Env.generalize);
            FStarC_TypeChecker_Env.letrecs =
              (env.FStarC_TypeChecker_Env.letrecs);
            FStarC_TypeChecker_Env.top_level =
              (env.FStarC_TypeChecker_Env.top_level);
            FStarC_TypeChecker_Env.check_uvars =
              (env.FStarC_TypeChecker_Env.check_uvars);
            FStarC_TypeChecker_Env.use_eq_strict =
              (env.FStarC_TypeChecker_Env.use_eq_strict);
            FStarC_TypeChecker_Env.is_iface =
              (env.FStarC_TypeChecker_Env.is_iface);
            FStarC_TypeChecker_Env.admit = (env.FStarC_TypeChecker_Env.admit);
            FStarC_TypeChecker_Env.lax_universes =
              (env.FStarC_TypeChecker_Env.lax_universes);
            FStarC_TypeChecker_Env.phase1 =
              (env.FStarC_TypeChecker_Env.phase1);
            FStarC_TypeChecker_Env.failhard =
              (env.FStarC_TypeChecker_Env.failhard);
            FStarC_TypeChecker_Env.flychecking =
              (env.FStarC_TypeChecker_Env.flychecking);
            FStarC_TypeChecker_Env.uvar_subtyping =
              (env.FStarC_TypeChecker_Env.uvar_subtyping);
            FStarC_TypeChecker_Env.intactics =
              (env.FStarC_TypeChecker_Env.intactics);
            FStarC_TypeChecker_Env.nocoerce =
              (env.FStarC_TypeChecker_Env.nocoerce);
            FStarC_TypeChecker_Env.tc_term =
              (env.FStarC_TypeChecker_Env.tc_term);
            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStarC_TypeChecker_Env.universe_of =
              (env.FStarC_TypeChecker_Env.universe_of);
            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStarC_TypeChecker_Env.teq_nosmt_force =
              (env.FStarC_TypeChecker_Env.teq_nosmt_force);
            FStarC_TypeChecker_Env.subtype_nosmt_force =
              (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
            FStarC_TypeChecker_Env.qtbl_name_and_index = uu___1;
            FStarC_TypeChecker_Env.normalized_eff_names =
              (env.FStarC_TypeChecker_Env.normalized_eff_names);
            FStarC_TypeChecker_Env.fv_delta_depths =
              (env.FStarC_TypeChecker_Env.fv_delta_depths);
            FStarC_TypeChecker_Env.proof_ns =
              (env.FStarC_TypeChecker_Env.proof_ns);
            FStarC_TypeChecker_Env.synth_hook =
              (env.FStarC_TypeChecker_Env.synth_hook);
            FStarC_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
            FStarC_TypeChecker_Env.splice =
              (env.FStarC_TypeChecker_Env.splice);
            FStarC_TypeChecker_Env.mpreprocess =
              (env.FStarC_TypeChecker_Env.mpreprocess);
            FStarC_TypeChecker_Env.postprocess =
              (env.FStarC_TypeChecker_Env.postprocess);
            FStarC_TypeChecker_Env.identifier_info =
              (env.FStarC_TypeChecker_Env.identifier_info);
            FStarC_TypeChecker_Env.tc_hooks =
              (env.FStarC_TypeChecker_Env.tc_hooks);
            FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
            FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
            FStarC_TypeChecker_Env.strict_args_tab =
              (env.FStarC_TypeChecker_Env.strict_args_tab);
            FStarC_TypeChecker_Env.erasable_types_tab =
              (env.FStarC_TypeChecker_Env.erasable_types_tab);
            FStarC_TypeChecker_Env.enable_defer_to_tac =
              (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
            FStarC_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
            FStarC_TypeChecker_Env.erase_erasable_args =
              (env.FStarC_TypeChecker_Env.erase_erasable_args);
            FStarC_TypeChecker_Env.core_check =
              (env.FStarC_TypeChecker_Env.core_check);
            FStarC_TypeChecker_Env.missing_decl =
              (env.FStarC_TypeChecker_Env.missing_decl)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStarC_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu___1 = FStarC_TypeChecker_Env.current_module env in
                let uu___2 =
                  let uu___3 = FStarC_GenSym.next_id () in
                  FStarC_Compiler_Util.string_of_int uu___3 in
                FStarC_Ident.lid_add_suffix uu___1 uu___2
            | l::uu___1 -> l in
          let uu___1 =
            let uu___2 =
              let uu___3 = let uu___4 = get_n lid in (lid, typ, uu___4) in
              FStar_Pervasives_Native.Some uu___3 in
            (uu___2, tbl) in
          {
            FStarC_TypeChecker_Env.solver =
              (env.FStarC_TypeChecker_Env.solver);
            FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
            FStarC_TypeChecker_Env.curmodule =
              (env.FStarC_TypeChecker_Env.curmodule);
            FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
            FStarC_TypeChecker_Env.gamma_sig =
              (env.FStarC_TypeChecker_Env.gamma_sig);
            FStarC_TypeChecker_Env.gamma_cache =
              (env.FStarC_TypeChecker_Env.gamma_cache);
            FStarC_TypeChecker_Env.modules =
              (env.FStarC_TypeChecker_Env.modules);
            FStarC_TypeChecker_Env.expected_typ =
              (env.FStarC_TypeChecker_Env.expected_typ);
            FStarC_TypeChecker_Env.sigtab =
              (env.FStarC_TypeChecker_Env.sigtab);
            FStarC_TypeChecker_Env.attrtab =
              (env.FStarC_TypeChecker_Env.attrtab);
            FStarC_TypeChecker_Env.instantiate_imp =
              (env.FStarC_TypeChecker_Env.instantiate_imp);
            FStarC_TypeChecker_Env.effects =
              (env.FStarC_TypeChecker_Env.effects);
            FStarC_TypeChecker_Env.generalize =
              (env.FStarC_TypeChecker_Env.generalize);
            FStarC_TypeChecker_Env.letrecs =
              (env.FStarC_TypeChecker_Env.letrecs);
            FStarC_TypeChecker_Env.top_level =
              (env.FStarC_TypeChecker_Env.top_level);
            FStarC_TypeChecker_Env.check_uvars =
              (env.FStarC_TypeChecker_Env.check_uvars);
            FStarC_TypeChecker_Env.use_eq_strict =
              (env.FStarC_TypeChecker_Env.use_eq_strict);
            FStarC_TypeChecker_Env.is_iface =
              (env.FStarC_TypeChecker_Env.is_iface);
            FStarC_TypeChecker_Env.admit = (env.FStarC_TypeChecker_Env.admit);
            FStarC_TypeChecker_Env.lax_universes =
              (env.FStarC_TypeChecker_Env.lax_universes);
            FStarC_TypeChecker_Env.phase1 =
              (env.FStarC_TypeChecker_Env.phase1);
            FStarC_TypeChecker_Env.failhard =
              (env.FStarC_TypeChecker_Env.failhard);
            FStarC_TypeChecker_Env.flychecking =
              (env.FStarC_TypeChecker_Env.flychecking);
            FStarC_TypeChecker_Env.uvar_subtyping =
              (env.FStarC_TypeChecker_Env.uvar_subtyping);
            FStarC_TypeChecker_Env.intactics =
              (env.FStarC_TypeChecker_Env.intactics);
            FStarC_TypeChecker_Env.nocoerce =
              (env.FStarC_TypeChecker_Env.nocoerce);
            FStarC_TypeChecker_Env.tc_term =
              (env.FStarC_TypeChecker_Env.tc_term);
            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStarC_TypeChecker_Env.universe_of =
              (env.FStarC_TypeChecker_Env.universe_of);
            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStarC_TypeChecker_Env.teq_nosmt_force =
              (env.FStarC_TypeChecker_Env.teq_nosmt_force);
            FStarC_TypeChecker_Env.subtype_nosmt_force =
              (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
            FStarC_TypeChecker_Env.qtbl_name_and_index = uu___1;
            FStarC_TypeChecker_Env.normalized_eff_names =
              (env.FStarC_TypeChecker_Env.normalized_eff_names);
            FStarC_TypeChecker_Env.fv_delta_depths =
              (env.FStarC_TypeChecker_Env.fv_delta_depths);
            FStarC_TypeChecker_Env.proof_ns =
              (env.FStarC_TypeChecker_Env.proof_ns);
            FStarC_TypeChecker_Env.synth_hook =
              (env.FStarC_TypeChecker_Env.synth_hook);
            FStarC_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
            FStarC_TypeChecker_Env.splice =
              (env.FStarC_TypeChecker_Env.splice);
            FStarC_TypeChecker_Env.mpreprocess =
              (env.FStarC_TypeChecker_Env.mpreprocess);
            FStarC_TypeChecker_Env.postprocess =
              (env.FStarC_TypeChecker_Env.postprocess);
            FStarC_TypeChecker_Env.identifier_info =
              (env.FStarC_TypeChecker_Env.identifier_info);
            FStarC_TypeChecker_Env.tc_hooks =
              (env.FStarC_TypeChecker_Env.tc_hooks);
            FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
            FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
            FStarC_TypeChecker_Env.strict_args_tab =
              (env.FStarC_TypeChecker_Env.strict_args_tab);
            FStarC_TypeChecker_Env.erasable_types_tab =
              (env.FStarC_TypeChecker_Env.erasable_types_tab);
            FStarC_TypeChecker_Env.enable_defer_to_tac =
              (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
            FStarC_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
            FStarC_TypeChecker_Env.erase_erasable_args =
              (env.FStarC_TypeChecker_Env.erase_erasable_args);
            FStarC_TypeChecker_Env.core_check =
              (env.FStarC_TypeChecker_Env.core_check);
            FStarC_TypeChecker_Env.missing_decl =
              (env.FStarC_TypeChecker_Env.missing_decl)
          }
let (log : FStarC_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStarC_Options.log_types ()) &&
      (let uu___ =
         let uu___1 = FStarC_TypeChecker_Env.current_module env in
         FStarC_Ident.lid_equals FStarC_Parser_Const.prims_lid uu___1 in
       Prims.op_Negation uu___)
let (tc_type_common :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.tscheme ->
      FStarC_Syntax_Syntax.typ ->
        FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun uu___ ->
      fun expected_typ ->
        fun r ->
          match uu___ with
          | (uvs, t) ->
              let uu___1 = FStarC_Syntax_Subst.open_univ_vars uvs t in
              (match uu___1 with
               | (uvs1, t1) ->
                   let env1 = FStarC_TypeChecker_Env.push_univ_vars env uvs1 in
                   let t2 =
                     FStarC_TypeChecker_TcTerm.tc_check_trivial_guard env1 t1
                       expected_typ in
                   if uvs1 = []
                   then
                     let uu___2 =
                       FStarC_TypeChecker_Generalize.generalize_universes
                         env1 t2 in
                     (match uu___2 with
                      | (uvs2, t3) ->
                          (FStarC_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu___3 =
                        let uu___4 =
                          FStarC_TypeChecker_Normalize.remove_uvar_solutions
                            env1 t2 in
                        FStarC_Syntax_Subst.close_univ_vars uvs1 uu___4 in
                      (uvs1, uu___3)))
let (tc_declare_typ :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.tscheme ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStarC_Syntax_Util.type_u () in
          FStar_Pervasives_Native.fst uu___1 in
        tc_type_common env ts uu___ r
let (tc_assume :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.tscheme ->
      FStarC_Compiler_Range_Type.range -> FStarC_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStarC_Syntax_Util.type_u () in
          FStar_Pervasives_Native.fst uu___1 in
        tc_type_common env ts uu___ r
let (tc_decl_attributes :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt)
  =
  fun env ->
    fun se ->
      let uu___ =
        let uu___1 =
          FStarC_TypeChecker_Env.lid_exists env
            FStarC_Parser_Const.attr_substitute_lid in
        if uu___1
        then ([], (se.FStarC_Syntax_Syntax.sigattrs))
        else
          FStarC_Compiler_List.partition
            ((=) FStarC_Syntax_Util.attr_substitute)
            se.FStarC_Syntax_Syntax.sigattrs in
      match uu___ with
      | (blacklisted_attrs, other_attrs) ->
          let uu___1 =
            FStarC_TypeChecker_TcTerm.tc_attributes env other_attrs in
          (match uu___1 with
           | (g, other_attrs1) ->
               (FStarC_TypeChecker_Rel.force_trivial_guard env g;
                {
                  FStarC_Syntax_Syntax.sigel =
                    (se.FStarC_Syntax_Syntax.sigel);
                  FStarC_Syntax_Syntax.sigrng =
                    (se.FStarC_Syntax_Syntax.sigrng);
                  FStarC_Syntax_Syntax.sigquals =
                    (se.FStarC_Syntax_Syntax.sigquals);
                  FStarC_Syntax_Syntax.sigmeta =
                    (se.FStarC_Syntax_Syntax.sigmeta);
                  FStarC_Syntax_Syntax.sigattrs =
                    (FStarC_Compiler_List.op_At blacklisted_attrs
                       other_attrs1);
                  FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                    (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                  FStarC_Syntax_Syntax.sigopts =
                    (se.FStarC_Syntax_Syntax.sigopts)
                }))
let (tc_inductive' :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt Prims.list ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          FStarC_Ident.lident Prims.list ->
            (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.sigelt
              Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          fun lids ->
            (let uu___1 = FStarC_Compiler_Debug.low () in
             if uu___1
             then
               let uu___2 =
                 FStarC_Class_Show.show
                   (FStarC_Class_Show.show_list
                      FStarC_Syntax_Print.showable_sigelt) ses in
               FStarC_Compiler_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n"
                 uu___2
             else ());
            (let ses1 = FStarC_Compiler_List.map (tc_decl_attributes env) ses in
             let uu___1 =
               FStarC_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses1 quals lids in
             match uu___1 with
             | (sig_bndle, tcs, datas) ->
                 let sig_bndle1 =
                   FStarC_TypeChecker_Positivity.mark_uniform_type_parameters
                     env sig_bndle in
                 let attrs' =
                   FStarC_Syntax_Util.remove_attr
                     FStarC_Parser_Const.erasable_attr attrs in
                 let data_ops_ses =
                   let uu___2 =
                     FStarC_Compiler_List.map
                       (FStarC_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas in
                   FStarC_Compiler_List.flatten uu___2 in
                 ((let uu___3 =
                     (FStarC_Options.no_positivity ()) ||
                       (let uu___4 = FStarC_TypeChecker_Env.should_verify env in
                        Prims.op_Negation uu___4) in
                   if uu___3
                   then ()
                   else
                     (let env2 =
                        FStarC_TypeChecker_Env.push_sigelt env sig_bndle1 in
                      FStarC_Compiler_List.iter
                        (fun ty ->
                           let b =
                             FStarC_TypeChecker_Positivity.check_strict_positivity
                               env2 lids ty in
                           if Prims.op_Negation b
                           then
                             let uu___6 =
                               match ty.FStarC_Syntax_Syntax.sigel with
                               | FStarC_Syntax_Syntax.Sig_inductive_typ
                                   { FStarC_Syntax_Syntax.lid = lid;
                                     FStarC_Syntax_Syntax.us = uu___7;
                                     FStarC_Syntax_Syntax.params = uu___8;
                                     FStarC_Syntax_Syntax.num_uniform_params
                                       = uu___9;
                                     FStarC_Syntax_Syntax.t = uu___10;
                                     FStarC_Syntax_Syntax.mutuals = uu___11;
                                     FStarC_Syntax_Syntax.ds = uu___12;
                                     FStarC_Syntax_Syntax.injective_type_params
                                       = uu___13;_}
                                   -> (lid, (ty.FStarC_Syntax_Syntax.sigrng))
                               | uu___7 -> failwith "Impossible!" in
                             match uu___6 with
                             | (lid, r) ->
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       FStarC_Ident.string_of_lid lid in
                                     Prims.strcat uu___9
                                       " does not satisfy the strict positivity condition" in
                                   Prims.strcat "Inductive type " uu___8 in
                                 FStarC_Errors.log_issue
                                   FStarC_Class_HasRange.hasRange_range r
                                   FStarC_Errors_Codes.Error_InductiveTypeNotSatisfyPositivityCondition
                                   ()
                                   (Obj.magic
                                      FStarC_Errors_Msg.is_error_message_string)
                                   (Obj.magic uu___7)
                           else ()) tcs;
                      FStarC_Compiler_List.iter
                        (fun d ->
                           let uu___6 =
                             match d.FStarC_Syntax_Syntax.sigel with
                             | FStarC_Syntax_Syntax.Sig_datacon
                                 { FStarC_Syntax_Syntax.lid1 = data_lid;
                                   FStarC_Syntax_Syntax.us1 = uu___7;
                                   FStarC_Syntax_Syntax.t1 = uu___8;
                                   FStarC_Syntax_Syntax.ty_lid = ty_lid;
                                   FStarC_Syntax_Syntax.num_ty_params =
                                     uu___9;
                                   FStarC_Syntax_Syntax.mutuals1 = uu___10;
                                   FStarC_Syntax_Syntax.injective_type_params1
                                     = uu___11;_}
                                 -> (data_lid, ty_lid)
                             | uu___7 -> failwith "Impossible" in
                           match uu___6 with
                           | (data_lid, ty_lid) ->
                               let uu___7 =
                                 (FStarC_Ident.lid_equals ty_lid
                                    FStarC_Parser_Const.exn_lid)
                                   &&
                                   (let uu___8 =
                                      FStarC_TypeChecker_Positivity.check_exn_strict_positivity
                                        env2 data_lid in
                                    Prims.op_Negation uu___8) in
                               if uu___7
                               then
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStarC_Ident.string_of_lid data_lid in
                                     Prims.strcat uu___10
                                       " does not satisfy the positivity condition" in
                                   Prims.strcat "Exception " uu___9 in
                                 FStarC_Errors.log_issue
                                   FStarC_Syntax_Syntax.has_range_sigelt d
                                   FStarC_Errors_Codes.Error_InductiveTypeNotSatisfyPositivityCondition
                                   ()
                                   (Obj.magic
                                      FStarC_Errors_Msg.is_error_message_string)
                                   (Obj.magic uu___8)
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu___3 =
                       let lid =
                         let ty = FStarC_Compiler_List.hd tcs in
                         match ty.FStarC_Syntax_Syntax.sigel with
                         | FStarC_Syntax_Syntax.Sig_inductive_typ
                             { FStarC_Syntax_Syntax.lid = lid1;
                               FStarC_Syntax_Syntax.us = uu___4;
                               FStarC_Syntax_Syntax.params = uu___5;
                               FStarC_Syntax_Syntax.num_uniform_params =
                                 uu___6;
                               FStarC_Syntax_Syntax.t = uu___7;
                               FStarC_Syntax_Syntax.mutuals = uu___8;
                               FStarC_Syntax_Syntax.ds = uu___9;
                               FStarC_Syntax_Syntax.injective_type_params =
                                 uu___10;_}
                             -> lid1
                         | uu___4 -> failwith "Impossible" in
                       FStarC_Compiler_List.existsb
                         (fun s ->
                            let uu___4 =
                              let uu___5 = FStarC_Ident.ident_of_lid lid in
                              FStarC_Ident.string_of_id uu___5 in
                            s = uu___4)
                         FStarC_TypeChecker_TcInductive.early_prims_inductives in
                     let is_noeq =
                       FStarC_Compiler_List.existsb
                         (fun q -> q = FStarC_Syntax_Syntax.Noeq) quals in
                     let is_erasable uu___3 =
                       let uu___4 =
                         let uu___5 = FStarC_Compiler_List.hd tcs in
                         uu___5.FStarC_Syntax_Syntax.sigattrs in
                       FStarC_Syntax_Util.has_attribute uu___4
                         FStarC_Parser_Const.erasable_attr in
                     ((((FStarC_Compiler_List.length tcs) = Prims.int_zero)
                         ||
                         ((FStarC_Ident.lid_equals
                             env.FStarC_TypeChecker_Env.curmodule
                             FStarC_Parser_Const.prims_lid)
                            && (skip_prims_type ())))
                        || is_noeq)
                       || (is_erasable ()) in
                   let res =
                     if skip_haseq
                     then (sig_bndle1, data_ops_ses)
                     else
                       (let is_unopteq =
                          FStarC_Compiler_List.existsb
                            (fun q -> q = FStarC_Syntax_Syntax.Unopteq) quals in
                        let ses2 =
                          if is_unopteq
                          then
                            FStarC_TypeChecker_TcInductive.unoptimized_haseq_scheme
                              sig_bndle1 tcs datas env
                          else
                            FStarC_TypeChecker_TcInductive.optimized_haseq_scheme
                              sig_bndle1 tcs datas env in
                        (sig_bndle1,
                          (FStarC_Compiler_List.op_At ses2 data_ops_ses))) in
                   res)))
let (tc_inductive :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt Prims.list ->
      FStarC_Syntax_Syntax.qualifier Prims.list ->
        FStarC_Syntax_Syntax.attribute Prims.list ->
          FStarC_Ident.lident Prims.list ->
            (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.sigelt
              Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          fun lids ->
            let env1 = FStarC_TypeChecker_Env.push env "tc_inductive" in
            let pop uu___ =
              let uu___1 = FStarC_TypeChecker_Env.pop env1 "tc_inductive" in
              () in
            let uu___ = FStarC_Options.trace_error () in
            if uu___
            then
              let r = tc_inductive' env1 ses quals attrs lids in (pop (); r)
            else
              (try
                 (fun uu___2 ->
                    match () with
                    | () ->
                        let uu___3 = tc_inductive' env1 ses quals attrs lids in
                        (pop (); uu___3)) ()
               with | uu___2 -> (pop (); FStarC_Compiler_Effect.raise uu___2))
let proc_check_with :
  'a . FStarC_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs ->
    fun kont ->
      let uu___ =
        FStarC_Syntax_Util.get_attribute FStarC_Parser_Const.check_with_lid
          attrs in
      match uu___ with
      | FStar_Pervasives_Native.None -> kont ()
      | FStar_Pervasives_Native.Some ((a1, FStar_Pervasives_Native.None)::[])
          ->
          let uu___1 =
            FStarC_Syntax_Embeddings_Base.unembed
              FStarC_Syntax_Embeddings.e_vconfig a1
              FStarC_Syntax_Embeddings_Base.id_norm_cb in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> failwith "nah"
           | FStar_Pervasives_Native.Some vcfg ->
               FStarC_Options.with_saved_options
                 (fun uu___2 -> FStarC_Options.set_vconfig vcfg; kont ())
           | uu___2 -> failwith "ill-formed `check_with`")
let (handle_postprocess_with_attr :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.attribute Prims.list ->
      (FStarC_Syntax_Syntax.attribute Prims.list * FStarC_Syntax_Syntax.term
        FStar_Pervasives_Native.option))
  =
  fun env ->
    fun ats ->
      let uu___ =
        FStarC_Syntax_Util.extract_attr' FStarC_Parser_Const.postprocess_with
          ats in
      match uu___ with
      | FStar_Pervasives_Native.None -> (ats, FStar_Pervasives_Native.None)
      | FStar_Pervasives_Native.Some
          (ats1, (tau, FStar_Pervasives_Native.None)::[]) ->
          (ats1, (FStar_Pervasives_Native.Some tau))
      | FStar_Pervasives_Native.Some (ats1, args) ->
          ((let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Ident.showable_lident
                  FStarC_Parser_Const.postprocess_with in
              FStarC_Compiler_Util.format1 "Ill-formed application of `%s`"
                uu___3 in
            FStarC_Errors.log_issue FStarC_TypeChecker_Env.hasRange_env env
              FStarC_Errors_Codes.Warning_UnrecognizedAttribute ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___2));
           (ats1, FStar_Pervasives_Native.None))
let (store_sigopts :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ =
      let uu___1 = FStarC_Options.get_vconfig () in
      FStar_Pervasives_Native.Some uu___1 in
    {
      FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
      FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
      FStarC_Syntax_Syntax.sigquals = (se.FStarC_Syntax_Syntax.sigquals);
      FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
      FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
      FStarC_Syntax_Syntax.sigopens_and_abbrevs =
        (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
      FStarC_Syntax_Syntax.sigopts = uu___
    }
let (tc_decls_knot :
  (FStarC_TypeChecker_Env.env ->
     FStarC_Syntax_Syntax.sigelt Prims.list ->
       (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_TypeChecker_Env.env))
    FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let do_two_phases : 'uuuuu . 'uuuuu -> Prims.bool =
  fun env -> let uu___ = FStarC_Options.lax () in Prims.op_Negation uu___
let run_phase1 : 'a . (unit -> 'a) -> 'a =
  fun f ->
    FStarC_TypeChecker_Core.clear_memo_table ();
    (let r = f () in FStarC_TypeChecker_Core.clear_memo_table (); r)
let (tc_sig_let :
  FStarC_TypeChecker_Env.env ->
    FStarC_Compiler_Range_Type.range ->
      FStarC_Syntax_Syntax.sigelt ->
        (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list) ->
          FStarC_Ident.lident Prims.list ->
            (FStarC_Syntax_Syntax.sigelt Prims.list *
              FStarC_Syntax_Syntax.sigelt Prims.list *
              FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun r ->
      fun se ->
        fun lbs ->
          fun lids ->
            let env0 = env in
            let env1 = FStarC_TypeChecker_Env.set_range env r in
            let check_quals_eq l qopt val_q =
              match qopt with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some val_q
              | FStar_Pervasives_Native.Some q' ->
                  let drop_logic_and_irreducible =
                    FStarC_Compiler_List.filter
                      (fun x ->
                         Prims.op_Negation
                           ((FStarC_Syntax_Syntax.uu___is_Logic x) ||
                              (FStarC_Syntax_Syntax.uu___is_Irreducible x))) in
                  let val_q1 = drop_logic_and_irreducible val_q in
                  let q'0 = q' in
                  let q'1 = drop_logic_and_irreducible q' in
                  let uu___ =
                    FStarC_Class_Ord.ord_list_diff
                      FStarC_Syntax_Syntax.ord_qualifier val_q1 q'1 in
                  (match uu___ with
                   | ([], []) -> FStar_Pervasives_Native.Some q'0
                   | (d1, d2) ->
                       let uu___1 =
                         let uu___2 =
                           let uu___3 =
                             FStarC_Errors_Msg.text
                               "Inconsistent qualifier annotations on" in
                           let uu___4 =
                             let uu___5 =
                               FStarC_Class_Show.show
                                 FStarC_Ident.showable_lident l in
                             FStarC_Pprint.doc_of_string uu___5 in
                           FStarC_Pprint.op_Hat_Slash_Hat uu___3 uu___4 in
                         let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 = FStarC_Errors_Msg.text "Expected" in
                               let uu___7 =
                                 let uu___8 =
                                   let uu___9 =
                                     FStarC_Class_Show.show
                                       (FStarC_Class_Show.show_list
                                          FStarC_Syntax_Print.showable_qualifier)
                                       val_q1 in
                                   FStarC_Pprint.arbitrary_string uu___9 in
                                 FStarC_Pprint.squotes uu___8 in
                               FStarC_Pprint.prefix (Prims.of_int (4))
                                 Prims.int_one uu___6 uu___7 in
                             let uu___6 =
                               let uu___7 = FStarC_Errors_Msg.text "got" in
                               let uu___8 =
                                 let uu___9 =
                                   let uu___10 =
                                     FStarC_Class_Show.show
                                       (FStarC_Class_Show.show_list
                                          FStarC_Syntax_Print.showable_qualifier)
                                       q'1 in
                                   FStarC_Pprint.arbitrary_string uu___10 in
                                 FStarC_Pprint.squotes uu___9 in
                               FStarC_Pprint.prefix (Prims.of_int (4))
                                 Prims.int_one uu___7 uu___8 in
                             FStarC_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                           let uu___5 =
                             let uu___6 =
                               if Prims.uu___is_Cons d1
                               then
                                 let uu___7 =
                                   FStarC_Errors_Msg.text
                                     "Only in declaration: " in
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStarC_Class_Show.show
                                         (FStarC_Class_Show.show_list
                                            FStarC_Syntax_Print.showable_qualifier)
                                         d1 in
                                     FStarC_Pprint.arbitrary_string uu___10 in
                                   FStarC_Pprint.squotes uu___9 in
                                 FStarC_Pprint.prefix (Prims.of_int (2))
                                   Prims.int_one uu___7 uu___8
                               else FStarC_Pprint.empty in
                             let uu___7 =
                               let uu___8 =
                                 if Prims.uu___is_Cons d2
                                 then
                                   let uu___9 =
                                     FStarC_Errors_Msg.text
                                       "Only in definition: " in
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStarC_Class_Show.show
                                           (FStarC_Class_Show.show_list
                                              FStarC_Syntax_Print.showable_qualifier)
                                           d2 in
                                       FStarC_Pprint.arbitrary_string uu___12 in
                                     FStarC_Pprint.squotes uu___11 in
                                   FStarC_Pprint.prefix (Prims.of_int (2))
                                     Prims.int_one uu___9 uu___10
                                 else FStarC_Pprint.empty in
                               [uu___8] in
                             uu___6 :: uu___7 in
                           uu___4 :: uu___5 in
                         uu___2 :: uu___3 in
                       FStarC_Errors.raise_error
                         FStarC_Class_HasRange.hasRange_range r
                         FStarC_Errors_Codes.Fatal_InconsistentQualifierAnnotation
                         ()
                         (Obj.magic
                            FStarC_Errors_Msg.is_error_message_list_doc)
                         (Obj.magic uu___1)) in
            let rename_parameters lb =
              let rename_in_typ def typ =
                let typ1 = FStarC_Syntax_Subst.compress typ in
                let def_bs =
                  let uu___ =
                    let uu___1 = FStarC_Syntax_Subst.compress def in
                    uu___1.FStarC_Syntax_Syntax.n in
                  match uu___ with
                  | FStarC_Syntax_Syntax.Tm_abs
                      { FStarC_Syntax_Syntax.bs = binders;
                        FStarC_Syntax_Syntax.body = uu___1;
                        FStarC_Syntax_Syntax.rc_opt = uu___2;_}
                      -> binders
                  | uu___1 -> [] in
                match typ1 with
                | {
                    FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_arrow
                      { FStarC_Syntax_Syntax.bs1 = val_bs;
                        FStarC_Syntax_Syntax.comp = c;_};
                    FStarC_Syntax_Syntax.pos = r1;
                    FStarC_Syntax_Syntax.vars = uu___;
                    FStarC_Syntax_Syntax.hash_code = uu___1;_} ->
                    let has_auto_name bv =
                      let uu___2 =
                        FStarC_Ident.string_of_id
                          bv.FStarC_Syntax_Syntax.ppname in
                      FStarC_Compiler_Util.starts_with uu___2
                        FStarC_Ident.reserved_prefix in
                    let rec rename_binders def_bs1 val_bs1 =
                      match (def_bs1, val_bs1) with
                      | ([], uu___2) -> val_bs1
                      | (uu___2, []) -> val_bs1
                      | ({ FStarC_Syntax_Syntax.binder_bv = body_bv;
                           FStarC_Syntax_Syntax.binder_qual = uu___2;
                           FStarC_Syntax_Syntax.binder_positivity = uu___3;
                           FStarC_Syntax_Syntax.binder_attrs = uu___4;_}::bt,
                         val_b::vt) ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = has_auto_name body_bv in
                              let uu___8 =
                                has_auto_name
                                  val_b.FStarC_Syntax_Syntax.binder_bv in
                              (uu___7, uu___8) in
                            match uu___6 with
                            | (true, uu___7) -> val_b
                            | (false, true) ->
                                let uu___7 =
                                  let uu___8 =
                                    val_b.FStarC_Syntax_Syntax.binder_bv in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_Ident.string_of_id
                                          body_bv.FStarC_Syntax_Syntax.ppname in
                                      let uu___12 =
                                        FStarC_Ident.range_of_id
                                          (val_b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname in
                                      (uu___11, uu___12) in
                                    FStarC_Ident.mk_ident uu___10 in
                                  {
                                    FStarC_Syntax_Syntax.ppname = uu___9;
                                    FStarC_Syntax_Syntax.index =
                                      (uu___8.FStarC_Syntax_Syntax.index);
                                    FStarC_Syntax_Syntax.sort =
                                      (uu___8.FStarC_Syntax_Syntax.sort)
                                  } in
                                {
                                  FStarC_Syntax_Syntax.binder_bv = uu___7;
                                  FStarC_Syntax_Syntax.binder_qual =
                                    (val_b.FStarC_Syntax_Syntax.binder_qual);
                                  FStarC_Syntax_Syntax.binder_positivity =
                                    (val_b.FStarC_Syntax_Syntax.binder_positivity);
                                  FStarC_Syntax_Syntax.binder_attrs =
                                    (val_b.FStarC_Syntax_Syntax.binder_attrs)
                                }
                            | (false, false) -> val_b in
                          let uu___6 = rename_binders bt vt in uu___5 ::
                            uu___6 in
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = rename_binders def_bs val_bs in
                        {
                          FStarC_Syntax_Syntax.bs1 = uu___4;
                          FStarC_Syntax_Syntax.comp = c
                        } in
                      FStarC_Syntax_Syntax.Tm_arrow uu___3 in
                    FStarC_Syntax_Syntax.mk uu___2 r1
                | uu___ -> typ1 in
              let uu___ =
                rename_in_typ lb.FStarC_Syntax_Syntax.lbdef
                  lb.FStarC_Syntax_Syntax.lbtyp in
              {
                FStarC_Syntax_Syntax.lbname =
                  (lb.FStarC_Syntax_Syntax.lbname);
                FStarC_Syntax_Syntax.lbunivs =
                  (lb.FStarC_Syntax_Syntax.lbunivs);
                FStarC_Syntax_Syntax.lbtyp = uu___;
                FStarC_Syntax_Syntax.lbeff = (lb.FStarC_Syntax_Syntax.lbeff);
                FStarC_Syntax_Syntax.lbdef = (lb.FStarC_Syntax_Syntax.lbdef);
                FStarC_Syntax_Syntax.lbattrs =
                  (lb.FStarC_Syntax_Syntax.lbattrs);
                FStarC_Syntax_Syntax.lbpos = (lb.FStarC_Syntax_Syntax.lbpos)
              } in
            let uu___ =
              FStarC_Compiler_List.fold_left
                (fun uu___1 ->
                   fun lb ->
                     match uu___1 with
                     | (gen, lbs1, quals_opt) ->
                         let lbname =
                           FStarC_Compiler_Util.right
                             lb.FStarC_Syntax_Syntax.lbname in
                         let uu___2 =
                           let uu___3 =
                             FStarC_TypeChecker_Env.try_lookup_val_decl env1
                               (lbname.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                           match uu___3 with
                           | FStar_Pervasives_Native.None ->
                               (gen, lb, quals_opt)
                           | FStar_Pervasives_Native.Some
                               ((uvs, tval), quals) ->
                               let quals_opt1 =
                                 check_quals_eq
                                   (lbname.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                   quals_opt quals in
                               let def =
                                 match (lb.FStarC_Syntax_Syntax.lbtyp).FStarC_Syntax_Syntax.n
                                 with
                                 | FStarC_Syntax_Syntax.Tm_unknown ->
                                     lb.FStarC_Syntax_Syntax.lbdef
                                 | uu___4 ->
                                     FStarC_Syntax_Syntax.mk
                                       (FStarC_Syntax_Syntax.Tm_ascribed
                                          {
                                            FStarC_Syntax_Syntax.tm =
                                              (lb.FStarC_Syntax_Syntax.lbdef);
                                            FStarC_Syntax_Syntax.asc =
                                              ((FStar_Pervasives.Inl
                                                  (lb.FStarC_Syntax_Syntax.lbtyp)),
                                                FStar_Pervasives_Native.None,
                                                false);
                                            FStarC_Syntax_Syntax.eff_opt =
                                              FStar_Pervasives_Native.None
                                          })
                                       (lb.FStarC_Syntax_Syntax.lbdef).FStarC_Syntax_Syntax.pos in
                               (if
                                  (lb.FStarC_Syntax_Syntax.lbunivs <> []) &&
                                    ((FStarC_Compiler_List.length
                                        lb.FStarC_Syntax_Syntax.lbunivs)
                                       <> (FStarC_Compiler_List.length uvs))
                                then
                                  FStarC_Errors.raise_error
                                    FStarC_Class_HasRange.hasRange_range r
                                    FStarC_Errors_Codes.Fatal_IncoherentInlineUniverse
                                    ()
                                    (Obj.magic
                                       FStarC_Errors_Msg.is_error_message_string)
                                    (Obj.magic
                                       "Inline universes are incoherent with annotation from val declaration")
                                else ();
                                (let uu___5 =
                                   FStarC_Syntax_Syntax.mk_lb
                                     ((FStar_Pervasives.Inr lbname), uvs,
                                       FStarC_Parser_Const.effect_Tot_lid,
                                       tval, def,
                                       (lb.FStarC_Syntax_Syntax.lbattrs),
                                       (lb.FStarC_Syntax_Syntax.lbpos)) in
                                 (false, uu___5, quals_opt1))) in
                         (match uu___2 with
                          | (gen1, lb1, quals_opt1) ->
                              (gen1, (lb1 :: lbs1), quals_opt1)))
                (true, [],
                  (if se.FStarC_Syntax_Syntax.sigquals = []
                   then FStar_Pervasives_Native.None
                   else
                     FStar_Pervasives_Native.Some
                       (se.FStarC_Syntax_Syntax.sigquals)))
                (FStar_Pervasives_Native.snd lbs) in
            match uu___ with
            | (should_generalize, lbs', quals_opt) ->
                (FStarC_Syntax_Util.check_mutual_universes lbs';
                 (let quals =
                    match quals_opt with
                    | FStar_Pervasives_Native.None ->
                        [FStarC_Syntax_Syntax.Visible_default]
                    | FStar_Pervasives_Native.Some q ->
                        let uu___2 =
                          FStarC_Compiler_Util.for_some
                            (fun uu___3 ->
                               match uu___3 with
                               | FStarC_Syntax_Syntax.Irreducible -> true
                               | FStarC_Syntax_Syntax.Visible_default -> true
                               | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                   -> true
                               | uu___4 -> false) q in
                        if uu___2
                        then q
                        else FStarC_Syntax_Syntax.Visible_default :: q in
                  let lbs'1 = FStarC_Compiler_List.rev lbs' in
                  let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Util.extract_attr'
                        FStarC_Parser_Const.preprocess_with
                        se.FStarC_Syntax_Syntax.sigattrs in
                    match uu___3 with
                    | FStar_Pervasives_Native.None ->
                        ((se.FStarC_Syntax_Syntax.sigattrs),
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (ats, (tau, FStar_Pervasives_Native.None)::[]) ->
                        (ats, (FStar_Pervasives_Native.Some tau))
                    | FStar_Pervasives_Native.Some (ats, args) ->
                        (FStarC_Errors.log_issue
                           FStarC_Class_HasRange.hasRange_range r
                           FStarC_Errors_Codes.Warning_UnrecognizedAttribute
                           ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic
                              "Ill-formed application of `preprocess_with`");
                         ((se.FStarC_Syntax_Syntax.sigattrs),
                           FStar_Pervasives_Native.None)) in
                  match uu___2 with
                  | (attrs, pre_tau) ->
                      let se1 =
                        {
                          FStarC_Syntax_Syntax.sigel =
                            (se.FStarC_Syntax_Syntax.sigel);
                          FStarC_Syntax_Syntax.sigrng =
                            (se.FStarC_Syntax_Syntax.sigrng);
                          FStarC_Syntax_Syntax.sigquals =
                            (se.FStarC_Syntax_Syntax.sigquals);
                          FStarC_Syntax_Syntax.sigmeta =
                            (se.FStarC_Syntax_Syntax.sigmeta);
                          FStarC_Syntax_Syntax.sigattrs = attrs;
                          FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                            (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                          FStarC_Syntax_Syntax.sigopts =
                            (se.FStarC_Syntax_Syntax.sigopts)
                        } in
                      let preprocess_lb tau lb =
                        let lbdef =
                          FStarC_TypeChecker_Env.preprocess env1 tau
                            lb.FStarC_Syntax_Syntax.lbdef in
                        (let uu___4 =
                           (FStarC_Compiler_Debug.medium ()) ||
                             (FStarC_Compiler_Effect.op_Bang dbg_TwoPhases) in
                         if uu___4
                         then
                           let uu___5 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term lbdef in
                           FStarC_Compiler_Util.print1
                             "lb preprocessed into: %s\n" uu___5
                         else ());
                        {
                          FStarC_Syntax_Syntax.lbname =
                            (lb.FStarC_Syntax_Syntax.lbname);
                          FStarC_Syntax_Syntax.lbunivs =
                            (lb.FStarC_Syntax_Syntax.lbunivs);
                          FStarC_Syntax_Syntax.lbtyp =
                            (lb.FStarC_Syntax_Syntax.lbtyp);
                          FStarC_Syntax_Syntax.lbeff =
                            (lb.FStarC_Syntax_Syntax.lbeff);
                          FStarC_Syntax_Syntax.lbdef = lbdef;
                          FStarC_Syntax_Syntax.lbattrs =
                            (lb.FStarC_Syntax_Syntax.lbattrs);
                          FStarC_Syntax_Syntax.lbpos =
                            (lb.FStarC_Syntax_Syntax.lbpos)
                        } in
                      let lbs'2 =
                        match pre_tau with
                        | FStar_Pervasives_Native.Some tau ->
                            FStarC_Compiler_List.map (preprocess_lb tau)
                              lbs'1
                        | FStar_Pervasives_Native.None -> lbs'1 in
                      let e =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Syntax_Syntax.mk
                                (FStarC_Syntax_Syntax.Tm_constant
                                   FStarC_Const.Const_unit) r in
                            {
                              FStarC_Syntax_Syntax.lbs =
                                ((FStar_Pervasives_Native.fst lbs), lbs'2);
                              FStarC_Syntax_Syntax.body1 = uu___5
                            } in
                          FStarC_Syntax_Syntax.Tm_let uu___4 in
                        FStarC_Syntax_Syntax.mk uu___3 r in
                      let env' =
                        {
                          FStarC_TypeChecker_Env.solver =
                            (env1.FStarC_TypeChecker_Env.solver);
                          FStarC_TypeChecker_Env.range =
                            (env1.FStarC_TypeChecker_Env.range);
                          FStarC_TypeChecker_Env.curmodule =
                            (env1.FStarC_TypeChecker_Env.curmodule);
                          FStarC_TypeChecker_Env.gamma =
                            (env1.FStarC_TypeChecker_Env.gamma);
                          FStarC_TypeChecker_Env.gamma_sig =
                            (env1.FStarC_TypeChecker_Env.gamma_sig);
                          FStarC_TypeChecker_Env.gamma_cache =
                            (env1.FStarC_TypeChecker_Env.gamma_cache);
                          FStarC_TypeChecker_Env.modules =
                            (env1.FStarC_TypeChecker_Env.modules);
                          FStarC_TypeChecker_Env.expected_typ =
                            (env1.FStarC_TypeChecker_Env.expected_typ);
                          FStarC_TypeChecker_Env.sigtab =
                            (env1.FStarC_TypeChecker_Env.sigtab);
                          FStarC_TypeChecker_Env.attrtab =
                            (env1.FStarC_TypeChecker_Env.attrtab);
                          FStarC_TypeChecker_Env.instantiate_imp =
                            (env1.FStarC_TypeChecker_Env.instantiate_imp);
                          FStarC_TypeChecker_Env.effects =
                            (env1.FStarC_TypeChecker_Env.effects);
                          FStarC_TypeChecker_Env.generalize =
                            should_generalize;
                          FStarC_TypeChecker_Env.letrecs =
                            (env1.FStarC_TypeChecker_Env.letrecs);
                          FStarC_TypeChecker_Env.top_level = true;
                          FStarC_TypeChecker_Env.check_uvars =
                            (env1.FStarC_TypeChecker_Env.check_uvars);
                          FStarC_TypeChecker_Env.use_eq_strict =
                            (env1.FStarC_TypeChecker_Env.use_eq_strict);
                          FStarC_TypeChecker_Env.is_iface =
                            (env1.FStarC_TypeChecker_Env.is_iface);
                          FStarC_TypeChecker_Env.admit =
                            (env1.FStarC_TypeChecker_Env.admit);
                          FStarC_TypeChecker_Env.lax_universes =
                            (env1.FStarC_TypeChecker_Env.lax_universes);
                          FStarC_TypeChecker_Env.phase1 =
                            (env1.FStarC_TypeChecker_Env.phase1);
                          FStarC_TypeChecker_Env.failhard =
                            (env1.FStarC_TypeChecker_Env.failhard);
                          FStarC_TypeChecker_Env.flychecking =
                            (env1.FStarC_TypeChecker_Env.flychecking);
                          FStarC_TypeChecker_Env.uvar_subtyping =
                            (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                          FStarC_TypeChecker_Env.intactics =
                            (env1.FStarC_TypeChecker_Env.intactics);
                          FStarC_TypeChecker_Env.nocoerce =
                            (env1.FStarC_TypeChecker_Env.nocoerce);
                          FStarC_TypeChecker_Env.tc_term =
                            (env1.FStarC_TypeChecker_Env.tc_term);
                          FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                            (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                          FStarC_TypeChecker_Env.universe_of =
                            (env1.FStarC_TypeChecker_Env.universe_of);
                          FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                            =
                            (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                          FStarC_TypeChecker_Env.teq_nosmt_force =
                            (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                          FStarC_TypeChecker_Env.subtype_nosmt_force =
                            (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                          FStarC_TypeChecker_Env.qtbl_name_and_index =
                            (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                          FStarC_TypeChecker_Env.normalized_eff_names =
                            (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                          FStarC_TypeChecker_Env.fv_delta_depths =
                            (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                          FStarC_TypeChecker_Env.proof_ns =
                            (env1.FStarC_TypeChecker_Env.proof_ns);
                          FStarC_TypeChecker_Env.synth_hook =
                            (env1.FStarC_TypeChecker_Env.synth_hook);
                          FStarC_TypeChecker_Env.try_solve_implicits_hook =
                            (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                          FStarC_TypeChecker_Env.splice =
                            (env1.FStarC_TypeChecker_Env.splice);
                          FStarC_TypeChecker_Env.mpreprocess =
                            (env1.FStarC_TypeChecker_Env.mpreprocess);
                          FStarC_TypeChecker_Env.postprocess =
                            (env1.FStarC_TypeChecker_Env.postprocess);
                          FStarC_TypeChecker_Env.identifier_info =
                            (env1.FStarC_TypeChecker_Env.identifier_info);
                          FStarC_TypeChecker_Env.tc_hooks =
                            (env1.FStarC_TypeChecker_Env.tc_hooks);
                          FStarC_TypeChecker_Env.dsenv =
                            (env1.FStarC_TypeChecker_Env.dsenv);
                          FStarC_TypeChecker_Env.nbe =
                            (env1.FStarC_TypeChecker_Env.nbe);
                          FStarC_TypeChecker_Env.strict_args_tab =
                            (env1.FStarC_TypeChecker_Env.strict_args_tab);
                          FStarC_TypeChecker_Env.erasable_types_tab =
                            (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                          FStarC_TypeChecker_Env.enable_defer_to_tac =
                            (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                          FStarC_TypeChecker_Env.unif_allow_ref_guards =
                            (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                          FStarC_TypeChecker_Env.erase_erasable_args =
                            (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                          FStarC_TypeChecker_Env.core_check =
                            (env1.FStarC_TypeChecker_Env.core_check);
                          FStarC_TypeChecker_Env.missing_decl =
                            (env1.FStarC_TypeChecker_Env.missing_decl)
                        } in
                      let e1 =
                        let uu___3 = do_two_phases env' in
                        if uu___3
                        then
                          run_phase1
                            (fun uu___4 ->
                               let drop_lbtyp e_lax =
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Syntax_Subst.compress e_lax in
                                   uu___6.FStarC_Syntax_Syntax.n in
                                 match uu___5 with
                                 | FStarC_Syntax_Syntax.Tm_let
                                     {
                                       FStarC_Syntax_Syntax.lbs =
                                         (false, lb::[]);
                                       FStarC_Syntax_Syntax.body1 = e2;_}
                                     ->
                                     let lb_unannotated =
                                       let uu___6 =
                                         let uu___7 =
                                           FStarC_Syntax_Subst.compress e in
                                         uu___7.FStarC_Syntax_Syntax.n in
                                       match uu___6 with
                                       | FStarC_Syntax_Syntax.Tm_let
                                           {
                                             FStarC_Syntax_Syntax.lbs =
                                               (uu___7, lb1::[]);
                                             FStarC_Syntax_Syntax.body1 =
                                               uu___8;_}
                                           ->
                                           let uu___9 =
                                             let uu___10 =
                                               FStarC_Syntax_Subst.compress
                                                 lb1.FStarC_Syntax_Syntax.lbtyp in
                                             uu___10.FStarC_Syntax_Syntax.n in
                                           (match uu___9 with
                                            | FStarC_Syntax_Syntax.Tm_unknown
                                                -> true
                                            | uu___10 -> false)
                                       | uu___7 ->
                                           failwith
                                             "Impossible: first phase lb and second phase lb differ in structure!" in
                                     if lb_unannotated
                                     then
                                       {
                                         FStarC_Syntax_Syntax.n =
                                           (FStarC_Syntax_Syntax.Tm_let
                                              {
                                                FStarC_Syntax_Syntax.lbs =
                                                  (false,
                                                    [{
                                                       FStarC_Syntax_Syntax.lbname
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbname);
                                                       FStarC_Syntax_Syntax.lbunivs
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbunivs);
                                                       FStarC_Syntax_Syntax.lbtyp
                                                         =
                                                         FStarC_Syntax_Syntax.tun;
                                                       FStarC_Syntax_Syntax.lbeff
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbeff);
                                                       FStarC_Syntax_Syntax.lbdef
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbdef);
                                                       FStarC_Syntax_Syntax.lbattrs
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbattrs);
                                                       FStarC_Syntax_Syntax.lbpos
                                                         =
                                                         (lb.FStarC_Syntax_Syntax.lbpos)
                                                     }]);
                                                FStarC_Syntax_Syntax.body1 =
                                                  e2
                                              });
                                         FStarC_Syntax_Syntax.pos =
                                           (e_lax.FStarC_Syntax_Syntax.pos);
                                         FStarC_Syntax_Syntax.vars =
                                           (e_lax.FStarC_Syntax_Syntax.vars);
                                         FStarC_Syntax_Syntax.hash_code =
                                           (e_lax.FStarC_Syntax_Syntax.hash_code)
                                       }
                                     else e_lax
                                 | FStarC_Syntax_Syntax.Tm_let
                                     {
                                       FStarC_Syntax_Syntax.lbs =
                                         (true, lbs1);
                                       FStarC_Syntax_Syntax.body1 = uu___6;_}
                                     ->
                                     (FStarC_Syntax_Util.check_mutual_universes
                                        lbs1;
                                      e_lax) in
                               let e2 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_TypeChecker_Env.current_module
                                         env1 in
                                     FStarC_Ident.string_of_lid uu___7 in
                                   FStar_Pervasives_Native.Some uu___6 in
                                 FStarC_Profiling.profile
                                   (fun uu___6 ->
                                      let uu___7 =
                                        FStarC_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                          {
                                            FStarC_TypeChecker_Env.solver =
                                              (env'.FStarC_TypeChecker_Env.solver);
                                            FStarC_TypeChecker_Env.range =
                                              (env'.FStarC_TypeChecker_Env.range);
                                            FStarC_TypeChecker_Env.curmodule
                                              =
                                              (env'.FStarC_TypeChecker_Env.curmodule);
                                            FStarC_TypeChecker_Env.gamma =
                                              (env'.FStarC_TypeChecker_Env.gamma);
                                            FStarC_TypeChecker_Env.gamma_sig
                                              =
                                              (env'.FStarC_TypeChecker_Env.gamma_sig);
                                            FStarC_TypeChecker_Env.gamma_cache
                                              =
                                              (env'.FStarC_TypeChecker_Env.gamma_cache);
                                            FStarC_TypeChecker_Env.modules =
                                              (env'.FStarC_TypeChecker_Env.modules);
                                            FStarC_TypeChecker_Env.expected_typ
                                              =
                                              (env'.FStarC_TypeChecker_Env.expected_typ);
                                            FStarC_TypeChecker_Env.sigtab =
                                              (env'.FStarC_TypeChecker_Env.sigtab);
                                            FStarC_TypeChecker_Env.attrtab =
                                              (env'.FStarC_TypeChecker_Env.attrtab);
                                            FStarC_TypeChecker_Env.instantiate_imp
                                              =
                                              (env'.FStarC_TypeChecker_Env.instantiate_imp);
                                            FStarC_TypeChecker_Env.effects =
                                              (env'.FStarC_TypeChecker_Env.effects);
                                            FStarC_TypeChecker_Env.generalize
                                              =
                                              (env'.FStarC_TypeChecker_Env.generalize);
                                            FStarC_TypeChecker_Env.letrecs =
                                              (env'.FStarC_TypeChecker_Env.letrecs);
                                            FStarC_TypeChecker_Env.top_level
                                              =
                                              (env'.FStarC_TypeChecker_Env.top_level);
                                            FStarC_TypeChecker_Env.check_uvars
                                              =
                                              (env'.FStarC_TypeChecker_Env.check_uvars);
                                            FStarC_TypeChecker_Env.use_eq_strict
                                              =
                                              (env'.FStarC_TypeChecker_Env.use_eq_strict);
                                            FStarC_TypeChecker_Env.is_iface =
                                              (env'.FStarC_TypeChecker_Env.is_iface);
                                            FStarC_TypeChecker_Env.admit =
                                              true;
                                            FStarC_TypeChecker_Env.lax_universes
                                              =
                                              (env'.FStarC_TypeChecker_Env.lax_universes);
                                            FStarC_TypeChecker_Env.phase1 =
                                              true;
                                            FStarC_TypeChecker_Env.failhard =
                                              (env'.FStarC_TypeChecker_Env.failhard);
                                            FStarC_TypeChecker_Env.flychecking
                                              =
                                              (env'.FStarC_TypeChecker_Env.flychecking);
                                            FStarC_TypeChecker_Env.uvar_subtyping
                                              =
                                              (env'.FStarC_TypeChecker_Env.uvar_subtyping);
                                            FStarC_TypeChecker_Env.intactics
                                              =
                                              (env'.FStarC_TypeChecker_Env.intactics);
                                            FStarC_TypeChecker_Env.nocoerce =
                                              (env'.FStarC_TypeChecker_Env.nocoerce);
                                            FStarC_TypeChecker_Env.tc_term =
                                              (env'.FStarC_TypeChecker_Env.tc_term);
                                            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                              =
                                              (env'.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                            FStarC_TypeChecker_Env.universe_of
                                              =
                                              (env'.FStarC_TypeChecker_Env.universe_of);
                                            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                              =
                                              (env'.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                            FStarC_TypeChecker_Env.teq_nosmt_force
                                              =
                                              (env'.FStarC_TypeChecker_Env.teq_nosmt_force);
                                            FStarC_TypeChecker_Env.subtype_nosmt_force
                                              =
                                              (env'.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                            FStarC_TypeChecker_Env.qtbl_name_and_index
                                              =
                                              (env'.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                            FStarC_TypeChecker_Env.normalized_eff_names
                                              =
                                              (env'.FStarC_TypeChecker_Env.normalized_eff_names);
                                            FStarC_TypeChecker_Env.fv_delta_depths
                                              =
                                              (env'.FStarC_TypeChecker_Env.fv_delta_depths);
                                            FStarC_TypeChecker_Env.proof_ns =
                                              (env'.FStarC_TypeChecker_Env.proof_ns);
                                            FStarC_TypeChecker_Env.synth_hook
                                              =
                                              (env'.FStarC_TypeChecker_Env.synth_hook);
                                            FStarC_TypeChecker_Env.try_solve_implicits_hook
                                              =
                                              (env'.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                            FStarC_TypeChecker_Env.splice =
                                              (env'.FStarC_TypeChecker_Env.splice);
                                            FStarC_TypeChecker_Env.mpreprocess
                                              =
                                              (env'.FStarC_TypeChecker_Env.mpreprocess);
                                            FStarC_TypeChecker_Env.postprocess
                                              =
                                              (env'.FStarC_TypeChecker_Env.postprocess);
                                            FStarC_TypeChecker_Env.identifier_info
                                              =
                                              (env'.FStarC_TypeChecker_Env.identifier_info);
                                            FStarC_TypeChecker_Env.tc_hooks =
                                              (env'.FStarC_TypeChecker_Env.tc_hooks);
                                            FStarC_TypeChecker_Env.dsenv =
                                              (env'.FStarC_TypeChecker_Env.dsenv);
                                            FStarC_TypeChecker_Env.nbe =
                                              (env'.FStarC_TypeChecker_Env.nbe);
                                            FStarC_TypeChecker_Env.strict_args_tab
                                              =
                                              (env'.FStarC_TypeChecker_Env.strict_args_tab);
                                            FStarC_TypeChecker_Env.erasable_types_tab
                                              =
                                              (env'.FStarC_TypeChecker_Env.erasable_types_tab);
                                            FStarC_TypeChecker_Env.enable_defer_to_tac
                                              =
                                              (env'.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                            FStarC_TypeChecker_Env.unif_allow_ref_guards
                                              =
                                              (env'.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                            FStarC_TypeChecker_Env.erase_erasable_args
                                              =
                                              (env'.FStarC_TypeChecker_Env.erase_erasable_args);
                                            FStarC_TypeChecker_Env.core_check
                                              =
                                              (env'.FStarC_TypeChecker_Env.core_check);
                                            FStarC_TypeChecker_Env.missing_decl
                                              =
                                              (env'.FStarC_TypeChecker_Env.missing_decl)
                                          } e in
                                      match uu___7 with
                                      | (e3, uu___8, uu___9) -> e3) uu___5
                                   "FStarC.TypeChecker.Tc.tc_sig_let-tc-phase1" in
                               (let uu___6 =
                                  (FStarC_Compiler_Debug.medium ()) ||
                                    (FStarC_Compiler_Effect.op_Bang
                                       dbg_TwoPhases) in
                                if uu___6
                                then
                                  let uu___7 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term e2 in
                                  FStarC_Compiler_Util.print1
                                    "Let binding after phase 1, before removing uvars: %s\n"
                                    uu___7
                                else ());
                               (let e3 =
                                  let uu___6 =
                                    FStarC_TypeChecker_Normalize.remove_uvar_solutions
                                      env' e2 in
                                  drop_lbtyp uu___6 in
                                (let uu___7 =
                                   (FStarC_Compiler_Debug.medium ()) ||
                                     (FStarC_Compiler_Effect.op_Bang
                                        dbg_TwoPhases) in
                                 if uu___7
                                 then
                                   let uu___8 =
                                     FStarC_Class_Show.show
                                       FStarC_Syntax_Print.showable_term e3 in
                                   FStarC_Compiler_Util.print1
                                     "Let binding after phase 1, uvars removed: %s\n"
                                     uu___8
                                 else ());
                                e3))
                        else e in
                      let uu___3 =
                        handle_postprocess_with_attr env1
                          se1.FStarC_Syntax_Syntax.sigattrs in
                      (match uu___3 with
                       | (attrs1, post_tau) ->
                           let se2 =
                             {
                               FStarC_Syntax_Syntax.sigel =
                                 (se1.FStarC_Syntax_Syntax.sigel);
                               FStarC_Syntax_Syntax.sigrng =
                                 (se1.FStarC_Syntax_Syntax.sigrng);
                               FStarC_Syntax_Syntax.sigquals =
                                 (se1.FStarC_Syntax_Syntax.sigquals);
                               FStarC_Syntax_Syntax.sigmeta =
                                 (se1.FStarC_Syntax_Syntax.sigmeta);
                               FStarC_Syntax_Syntax.sigattrs = attrs1;
                               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                 (se1.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                               FStarC_Syntax_Syntax.sigopts =
                                 (se1.FStarC_Syntax_Syntax.sigopts)
                             } in
                           let postprocess_lb tau lb =
                             let uu___4 =
                               FStarC_Syntax_Subst.univ_var_opening
                                 lb.FStarC_Syntax_Syntax.lbunivs in
                             match uu___4 with
                             | (s, univnames) ->
                                 let lbdef =
                                   FStarC_Syntax_Subst.subst s
                                     lb.FStarC_Syntax_Syntax.lbdef in
                                 let lbtyp =
                                   FStarC_Syntax_Subst.subst s
                                     lb.FStarC_Syntax_Syntax.lbtyp in
                                 let env2 =
                                   FStarC_TypeChecker_Env.push_univ_vars env1
                                     univnames in
                                 let lbdef1 =
                                   FStarC_TypeChecker_Env.postprocess env2
                                     tau lbtyp lbdef in
                                 let lbdef2 =
                                   FStarC_Syntax_Subst.close_univ_vars
                                     univnames lbdef1 in
                                 {
                                   FStarC_Syntax_Syntax.lbname =
                                     (lb.FStarC_Syntax_Syntax.lbname);
                                   FStarC_Syntax_Syntax.lbunivs =
                                     (lb.FStarC_Syntax_Syntax.lbunivs);
                                   FStarC_Syntax_Syntax.lbtyp =
                                     (lb.FStarC_Syntax_Syntax.lbtyp);
                                   FStarC_Syntax_Syntax.lbeff =
                                     (lb.FStarC_Syntax_Syntax.lbeff);
                                   FStarC_Syntax_Syntax.lbdef = lbdef2;
                                   FStarC_Syntax_Syntax.lbattrs =
                                     (lb.FStarC_Syntax_Syntax.lbattrs);
                                   FStarC_Syntax_Syntax.lbpos =
                                     (lb.FStarC_Syntax_Syntax.lbpos)
                                 } in
                           let env'1 =
                             let uu___4 =
                               let uu___5 = FStarC_Syntax_Subst.compress e1 in
                               uu___5.FStarC_Syntax_Syntax.n in
                             match uu___4 with
                             | FStarC_Syntax_Syntax.Tm_let
                                 { FStarC_Syntax_Syntax.lbs = lbs1;
                                   FStarC_Syntax_Syntax.body1 = uu___5;_}
                                 ->
                                 let se3 =
                                   {
                                     FStarC_Syntax_Syntax.sigel =
                                       (FStarC_Syntax_Syntax.Sig_let
                                          {
                                            FStarC_Syntax_Syntax.lbs1 = lbs1;
                                            FStarC_Syntax_Syntax.lids1 = lids
                                          });
                                     FStarC_Syntax_Syntax.sigrng =
                                       (se2.FStarC_Syntax_Syntax.sigrng);
                                     FStarC_Syntax_Syntax.sigquals =
                                       (se2.FStarC_Syntax_Syntax.sigquals);
                                     FStarC_Syntax_Syntax.sigmeta =
                                       (se2.FStarC_Syntax_Syntax.sigmeta);
                                     FStarC_Syntax_Syntax.sigattrs =
                                       (se2.FStarC_Syntax_Syntax.sigattrs);
                                     FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                       =
                                       (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                     FStarC_Syntax_Syntax.sigopts =
                                       (se2.FStarC_Syntax_Syntax.sigopts)
                                   } in
                                 set_hint_correlator env' se3
                             | uu___5 -> failwith "no way, not a let?" in
                           (FStarC_Errors.stop_if_err ();
                            (let r1 =
                               let should_generalize1 =
                                 let uu___5 = do_two_phases env'1 in
                                 Prims.op_Negation uu___5 in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_TypeChecker_Env.current_module
                                       env1 in
                                   FStarC_Ident.string_of_lid uu___7 in
                                 FStar_Pervasives_Native.Some uu___6 in
                               FStarC_Profiling.profile
                                 (fun uu___6 ->
                                    FStarC_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                      {
                                        FStarC_TypeChecker_Env.solver =
                                          (env'1.FStarC_TypeChecker_Env.solver);
                                        FStarC_TypeChecker_Env.range =
                                          (env'1.FStarC_TypeChecker_Env.range);
                                        FStarC_TypeChecker_Env.curmodule =
                                          (env'1.FStarC_TypeChecker_Env.curmodule);
                                        FStarC_TypeChecker_Env.gamma =
                                          (env'1.FStarC_TypeChecker_Env.gamma);
                                        FStarC_TypeChecker_Env.gamma_sig =
                                          (env'1.FStarC_TypeChecker_Env.gamma_sig);
                                        FStarC_TypeChecker_Env.gamma_cache =
                                          (env'1.FStarC_TypeChecker_Env.gamma_cache);
                                        FStarC_TypeChecker_Env.modules =
                                          (env'1.FStarC_TypeChecker_Env.modules);
                                        FStarC_TypeChecker_Env.expected_typ =
                                          (env'1.FStarC_TypeChecker_Env.expected_typ);
                                        FStarC_TypeChecker_Env.sigtab =
                                          (env'1.FStarC_TypeChecker_Env.sigtab);
                                        FStarC_TypeChecker_Env.attrtab =
                                          (env'1.FStarC_TypeChecker_Env.attrtab);
                                        FStarC_TypeChecker_Env.instantiate_imp
                                          =
                                          (env'1.FStarC_TypeChecker_Env.instantiate_imp);
                                        FStarC_TypeChecker_Env.effects =
                                          (env'1.FStarC_TypeChecker_Env.effects);
                                        FStarC_TypeChecker_Env.generalize =
                                          should_generalize1;
                                        FStarC_TypeChecker_Env.letrecs =
                                          (env'1.FStarC_TypeChecker_Env.letrecs);
                                        FStarC_TypeChecker_Env.top_level =
                                          (env'1.FStarC_TypeChecker_Env.top_level);
                                        FStarC_TypeChecker_Env.check_uvars =
                                          (env'1.FStarC_TypeChecker_Env.check_uvars);
                                        FStarC_TypeChecker_Env.use_eq_strict
                                          =
                                          (env'1.FStarC_TypeChecker_Env.use_eq_strict);
                                        FStarC_TypeChecker_Env.is_iface =
                                          (env'1.FStarC_TypeChecker_Env.is_iface);
                                        FStarC_TypeChecker_Env.admit =
                                          (env'1.FStarC_TypeChecker_Env.admit);
                                        FStarC_TypeChecker_Env.lax_universes
                                          =
                                          (env'1.FStarC_TypeChecker_Env.lax_universes);
                                        FStarC_TypeChecker_Env.phase1 =
                                          (env'1.FStarC_TypeChecker_Env.phase1);
                                        FStarC_TypeChecker_Env.failhard =
                                          (env'1.FStarC_TypeChecker_Env.failhard);
                                        FStarC_TypeChecker_Env.flychecking =
                                          (env'1.FStarC_TypeChecker_Env.flychecking);
                                        FStarC_TypeChecker_Env.uvar_subtyping
                                          =
                                          (env'1.FStarC_TypeChecker_Env.uvar_subtyping);
                                        FStarC_TypeChecker_Env.intactics =
                                          (env'1.FStarC_TypeChecker_Env.intactics);
                                        FStarC_TypeChecker_Env.nocoerce =
                                          (env'1.FStarC_TypeChecker_Env.nocoerce);
                                        FStarC_TypeChecker_Env.tc_term =
                                          (env'1.FStarC_TypeChecker_Env.tc_term);
                                        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                          =
                                          (env'1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                        FStarC_TypeChecker_Env.universe_of =
                                          (env'1.FStarC_TypeChecker_Env.universe_of);
                                        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                          =
                                          (env'1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                        FStarC_TypeChecker_Env.teq_nosmt_force
                                          =
                                          (env'1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                        FStarC_TypeChecker_Env.subtype_nosmt_force
                                          =
                                          (env'1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                        FStarC_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (env'1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                        FStarC_TypeChecker_Env.normalized_eff_names
                                          =
                                          (env'1.FStarC_TypeChecker_Env.normalized_eff_names);
                                        FStarC_TypeChecker_Env.fv_delta_depths
                                          =
                                          (env'1.FStarC_TypeChecker_Env.fv_delta_depths);
                                        FStarC_TypeChecker_Env.proof_ns =
                                          (env'1.FStarC_TypeChecker_Env.proof_ns);
                                        FStarC_TypeChecker_Env.synth_hook =
                                          (env'1.FStarC_TypeChecker_Env.synth_hook);
                                        FStarC_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (env'1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                        FStarC_TypeChecker_Env.splice =
                                          (env'1.FStarC_TypeChecker_Env.splice);
                                        FStarC_TypeChecker_Env.mpreprocess =
                                          (env'1.FStarC_TypeChecker_Env.mpreprocess);
                                        FStarC_TypeChecker_Env.postprocess =
                                          (env'1.FStarC_TypeChecker_Env.postprocess);
                                        FStarC_TypeChecker_Env.identifier_info
                                          =
                                          (env'1.FStarC_TypeChecker_Env.identifier_info);
                                        FStarC_TypeChecker_Env.tc_hooks =
                                          (env'1.FStarC_TypeChecker_Env.tc_hooks);
                                        FStarC_TypeChecker_Env.dsenv =
                                          (env'1.FStarC_TypeChecker_Env.dsenv);
                                        FStarC_TypeChecker_Env.nbe =
                                          (env'1.FStarC_TypeChecker_Env.nbe);
                                        FStarC_TypeChecker_Env.strict_args_tab
                                          =
                                          (env'1.FStarC_TypeChecker_Env.strict_args_tab);
                                        FStarC_TypeChecker_Env.erasable_types_tab
                                          =
                                          (env'1.FStarC_TypeChecker_Env.erasable_types_tab);
                                        FStarC_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (env'1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                        FStarC_TypeChecker_Env.unif_allow_ref_guards
                                          =
                                          (env'1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                        FStarC_TypeChecker_Env.erase_erasable_args
                                          =
                                          (env'1.FStarC_TypeChecker_Env.erase_erasable_args);
                                        FStarC_TypeChecker_Env.core_check =
                                          (env'1.FStarC_TypeChecker_Env.core_check);
                                        FStarC_TypeChecker_Env.missing_decl =
                                          (env'1.FStarC_TypeChecker_Env.missing_decl)
                                      } e1) uu___5
                                 "FStarC.TypeChecker.Tc.tc_sig_let-tc-phase2" in
                             let uu___5 =
                               match r1 with
                               | ({
                                    FStarC_Syntax_Syntax.n =
                                      FStarC_Syntax_Syntax.Tm_let
                                      { FStarC_Syntax_Syntax.lbs = lbs1;
                                        FStarC_Syntax_Syntax.body1 = e2;_};
                                    FStarC_Syntax_Syntax.pos = uu___6;
                                    FStarC_Syntax_Syntax.vars = uu___7;
                                    FStarC_Syntax_Syntax.hash_code = uu___8;_},
                                  uu___9, g) when
                                   FStarC_TypeChecker_Env.is_trivial g ->
                                   (FStarC_Syntax_Util.check_mutual_universes
                                      (FStar_Pervasives_Native.snd lbs1);
                                    (let lbs2 =
                                       let uu___11 =
                                         FStarC_Compiler_List.map
                                           rename_parameters
                                           (FStar_Pervasives_Native.snd lbs1) in
                                       ((FStar_Pervasives_Native.fst lbs1),
                                         uu___11) in
                                     let lbs3 =
                                       let uu___11 =
                                         match post_tau with
                                         | FStar_Pervasives_Native.Some tau
                                             ->
                                             FStarC_Compiler_List.map
                                               (postprocess_lb tau)
                                               (FStar_Pervasives_Native.snd
                                                  lbs2)
                                         | FStar_Pervasives_Native.None ->
                                             FStar_Pervasives_Native.snd lbs2 in
                                       ((FStar_Pervasives_Native.fst lbs2),
                                         uu___11) in
                                     let quals1 =
                                       match e2.FStarC_Syntax_Syntax.n with
                                       | FStarC_Syntax_Syntax.Tm_meta
                                           {
                                             FStarC_Syntax_Syntax.tm2 =
                                               uu___11;
                                             FStarC_Syntax_Syntax.meta =
                                               FStarC_Syntax_Syntax.Meta_desugared
                                               (FStarC_Syntax_Syntax.Masked_effect);_}
                                           ->
                                           FStarC_Syntax_Syntax.HasMaskedEffect
                                           :: quals
                                       | uu___11 -> quals in
                                     ({
                                        FStarC_Syntax_Syntax.sigel =
                                          (FStarC_Syntax_Syntax.Sig_let
                                             {
                                               FStarC_Syntax_Syntax.lbs1 =
                                                 lbs3;
                                               FStarC_Syntax_Syntax.lids1 =
                                                 lids
                                             });
                                        FStarC_Syntax_Syntax.sigrng =
                                          (se2.FStarC_Syntax_Syntax.sigrng);
                                        FStarC_Syntax_Syntax.sigquals =
                                          quals1;
                                        FStarC_Syntax_Syntax.sigmeta =
                                          (se2.FStarC_Syntax_Syntax.sigmeta);
                                        FStarC_Syntax_Syntax.sigattrs =
                                          (se2.FStarC_Syntax_Syntax.sigattrs);
                                        FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                          =
                                          (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                        FStarC_Syntax_Syntax.sigopts =
                                          (se2.FStarC_Syntax_Syntax.sigopts)
                                      }, lbs3)))
                               | uu___6 ->
                                   failwith
                                     "impossible (typechecking should preserve Tm_let)" in
                             match uu___5 with
                             | (se3, lbs1) ->
                                 ((let uu___7 =
                                     FStarC_Syntax_Util.has_attribute
                                       se3.FStarC_Syntax_Syntax.sigattrs
                                       FStarC_Parser_Const.no_subtping_attr_lid in
                                   if uu___7
                                   then
                                     let env'2 =
                                       {
                                         FStarC_TypeChecker_Env.solver =
                                           (env'1.FStarC_TypeChecker_Env.solver);
                                         FStarC_TypeChecker_Env.range =
                                           (env'1.FStarC_TypeChecker_Env.range);
                                         FStarC_TypeChecker_Env.curmodule =
                                           (env'1.FStarC_TypeChecker_Env.curmodule);
                                         FStarC_TypeChecker_Env.gamma =
                                           (env'1.FStarC_TypeChecker_Env.gamma);
                                         FStarC_TypeChecker_Env.gamma_sig =
                                           (env'1.FStarC_TypeChecker_Env.gamma_sig);
                                         FStarC_TypeChecker_Env.gamma_cache =
                                           (env'1.FStarC_TypeChecker_Env.gamma_cache);
                                         FStarC_TypeChecker_Env.modules =
                                           (env'1.FStarC_TypeChecker_Env.modules);
                                         FStarC_TypeChecker_Env.expected_typ
                                           =
                                           (env'1.FStarC_TypeChecker_Env.expected_typ);
                                         FStarC_TypeChecker_Env.sigtab =
                                           (env'1.FStarC_TypeChecker_Env.sigtab);
                                         FStarC_TypeChecker_Env.attrtab =
                                           (env'1.FStarC_TypeChecker_Env.attrtab);
                                         FStarC_TypeChecker_Env.instantiate_imp
                                           =
                                           (env'1.FStarC_TypeChecker_Env.instantiate_imp);
                                         FStarC_TypeChecker_Env.effects =
                                           (env'1.FStarC_TypeChecker_Env.effects);
                                         FStarC_TypeChecker_Env.generalize =
                                           (env'1.FStarC_TypeChecker_Env.generalize);
                                         FStarC_TypeChecker_Env.letrecs =
                                           (env'1.FStarC_TypeChecker_Env.letrecs);
                                         FStarC_TypeChecker_Env.top_level =
                                           (env'1.FStarC_TypeChecker_Env.top_level);
                                         FStarC_TypeChecker_Env.check_uvars =
                                           (env'1.FStarC_TypeChecker_Env.check_uvars);
                                         FStarC_TypeChecker_Env.use_eq_strict
                                           = true;
                                         FStarC_TypeChecker_Env.is_iface =
                                           (env'1.FStarC_TypeChecker_Env.is_iface);
                                         FStarC_TypeChecker_Env.admit =
                                           (env'1.FStarC_TypeChecker_Env.admit);
                                         FStarC_TypeChecker_Env.lax_universes
                                           =
                                           (env'1.FStarC_TypeChecker_Env.lax_universes);
                                         FStarC_TypeChecker_Env.phase1 =
                                           (env'1.FStarC_TypeChecker_Env.phase1);
                                         FStarC_TypeChecker_Env.failhard =
                                           (env'1.FStarC_TypeChecker_Env.failhard);
                                         FStarC_TypeChecker_Env.flychecking =
                                           (env'1.FStarC_TypeChecker_Env.flychecking);
                                         FStarC_TypeChecker_Env.uvar_subtyping
                                           =
                                           (env'1.FStarC_TypeChecker_Env.uvar_subtyping);
                                         FStarC_TypeChecker_Env.intactics =
                                           (env'1.FStarC_TypeChecker_Env.intactics);
                                         FStarC_TypeChecker_Env.nocoerce =
                                           (env'1.FStarC_TypeChecker_Env.nocoerce);
                                         FStarC_TypeChecker_Env.tc_term =
                                           (env'1.FStarC_TypeChecker_Env.tc_term);
                                         FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                           =
                                           (env'1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                         FStarC_TypeChecker_Env.universe_of =
                                           (env'1.FStarC_TypeChecker_Env.universe_of);
                                         FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                           =
                                           (env'1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                         FStarC_TypeChecker_Env.teq_nosmt_force
                                           =
                                           (env'1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                         FStarC_TypeChecker_Env.subtype_nosmt_force
                                           =
                                           (env'1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                         FStarC_TypeChecker_Env.qtbl_name_and_index
                                           =
                                           (env'1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                         FStarC_TypeChecker_Env.normalized_eff_names
                                           =
                                           (env'1.FStarC_TypeChecker_Env.normalized_eff_names);
                                         FStarC_TypeChecker_Env.fv_delta_depths
                                           =
                                           (env'1.FStarC_TypeChecker_Env.fv_delta_depths);
                                         FStarC_TypeChecker_Env.proof_ns =
                                           (env'1.FStarC_TypeChecker_Env.proof_ns);
                                         FStarC_TypeChecker_Env.synth_hook =
                                           (env'1.FStarC_TypeChecker_Env.synth_hook);
                                         FStarC_TypeChecker_Env.try_solve_implicits_hook
                                           =
                                           (env'1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                         FStarC_TypeChecker_Env.splice =
                                           (env'1.FStarC_TypeChecker_Env.splice);
                                         FStarC_TypeChecker_Env.mpreprocess =
                                           (env'1.FStarC_TypeChecker_Env.mpreprocess);
                                         FStarC_TypeChecker_Env.postprocess =
                                           (env'1.FStarC_TypeChecker_Env.postprocess);
                                         FStarC_TypeChecker_Env.identifier_info
                                           =
                                           (env'1.FStarC_TypeChecker_Env.identifier_info);
                                         FStarC_TypeChecker_Env.tc_hooks =
                                           (env'1.FStarC_TypeChecker_Env.tc_hooks);
                                         FStarC_TypeChecker_Env.dsenv =
                                           (env'1.FStarC_TypeChecker_Env.dsenv);
                                         FStarC_TypeChecker_Env.nbe =
                                           (env'1.FStarC_TypeChecker_Env.nbe);
                                         FStarC_TypeChecker_Env.strict_args_tab
                                           =
                                           (env'1.FStarC_TypeChecker_Env.strict_args_tab);
                                         FStarC_TypeChecker_Env.erasable_types_tab
                                           =
                                           (env'1.FStarC_TypeChecker_Env.erasable_types_tab);
                                         FStarC_TypeChecker_Env.enable_defer_to_tac
                                           =
                                           (env'1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                         FStarC_TypeChecker_Env.unif_allow_ref_guards
                                           =
                                           (env'1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                         FStarC_TypeChecker_Env.erase_erasable_args
                                           =
                                           (env'1.FStarC_TypeChecker_Env.erase_erasable_args);
                                         FStarC_TypeChecker_Env.core_check =
                                           (env'1.FStarC_TypeChecker_Env.core_check);
                                         FStarC_TypeChecker_Env.missing_decl
                                           =
                                           (env'1.FStarC_TypeChecker_Env.missing_decl)
                                       } in
                                     let err s pos =
                                       FStarC_Errors.raise_error
                                         FStarC_Class_HasRange.hasRange_range
                                         pos
                                         FStarC_Errors_Codes.Fatal_InconsistentQualifierAnnotation
                                         ()
                                         (Obj.magic
                                            FStarC_Errors_Msg.is_error_message_string)
                                         (Obj.magic s) in
                                     FStarC_Compiler_List.iter
                                       (fun lb ->
                                          let uu___8 =
                                            let uu___9 =
                                              FStarC_Syntax_Util.is_lemma
                                                lb.FStarC_Syntax_Syntax.lbtyp in
                                            Prims.op_Negation uu___9 in
                                          if uu___8
                                          then
                                            err
                                              "no_subtype annotation on a non-lemma"
                                              lb.FStarC_Syntax_Syntax.lbpos
                                          else
                                            (let lid_opt =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStarC_Syntax_Free.fvars
                                                     lb.FStarC_Syntax_Syntax.lbtyp in
                                                 FStarC_Class_Setlike.elems
                                                   ()
                                                   (Obj.magic
                                                      (FStarC_Compiler_RBSet.setlike_rbset
                                                         FStarC_Syntax_Syntax.ord_fv))
                                                   (Obj.magic uu___11) in
                                               FStarC_Compiler_List.tryFind
                                                 (fun lid ->
                                                    let uu___11 =
                                                      (let uu___12 =
                                                         let uu___13 =
                                                           FStarC_Ident.path_of_lid
                                                             lid in
                                                         FStarC_Compiler_List.hd
                                                           uu___13 in
                                                       uu___12 = "Prims") ||
                                                        (FStarC_Ident.lid_equals
                                                           lid
                                                           FStarC_Parser_Const.pattern_lid) in
                                                    Prims.op_Negation uu___11)
                                                 uu___10 in
                                             if
                                               FStarC_Compiler_Util.is_some
                                                 lid_opt
                                             then
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     FStarC_Compiler_Util.must
                                                       lid_opt in
                                                   FStarC_Ident.string_of_lid
                                                     uu___12 in
                                                 FStarC_Compiler_Util.format1
                                                   "%s is not allowed in no_subtyping lemmas (only prims symbols)"
                                                   uu___11 in
                                               err uu___10
                                                 lb.FStarC_Syntax_Syntax.lbpos
                                             else
                                               (let uu___11 =
                                                  FStarC_Syntax_Util.type_u
                                                    () in
                                                match uu___11 with
                                                | (t, uu___12) ->
                                                    let uu___13 =
                                                      FStarC_Syntax_Subst.open_univ_vars
                                                        lb.FStarC_Syntax_Syntax.lbunivs
                                                        lb.FStarC_Syntax_Syntax.lbtyp in
                                                    (match uu___13 with
                                                     | (uvs, lbtyp) ->
                                                         let uu___14 =
                                                           let uu___15 =
                                                             FStarC_TypeChecker_Env.push_univ_vars
                                                               env'2 uvs in
                                                           FStarC_TypeChecker_TcTerm.tc_check_tot_or_gtot_term
                                                             uu___15 lbtyp t
                                                             (FStar_Pervasives_Native.Some
                                                                "checking no_subtype annotation") in
                                                         (match uu___14 with
                                                          | (uu___15,
                                                             uu___16, g) ->
                                                              FStarC_TypeChecker_Rel.force_trivial_guard
                                                                env'2 g)))))
                                       (FStar_Pervasives_Native.snd lbs1)
                                   else ());
                                  FStarC_Compiler_List.iter
                                    (fun lb ->
                                       let fv =
                                         FStarC_Compiler_Util.right
                                           lb.FStarC_Syntax_Syntax.lbname in
                                       FStarC_TypeChecker_Env.insert_fv_info
                                         env1 fv
                                         lb.FStarC_Syntax_Syntax.lbtyp)
                                    (FStar_Pervasives_Native.snd lbs1);
                                  (let uu___9 = log env1 in
                                   if uu___9
                                   then
                                     let uu___10 =
                                       let uu___11 =
                                         FStarC_Compiler_List.map
                                           (fun lb ->
                                              let should_log =
                                                let uu___12 =
                                                  let uu___13 =
                                                    let uu___14 =
                                                      let uu___15 =
                                                        FStarC_Compiler_Util.right
                                                          lb.FStarC_Syntax_Syntax.lbname in
                                                      uu___15.FStarC_Syntax_Syntax.fv_name in
                                                    uu___14.FStarC_Syntax_Syntax.v in
                                                  FStarC_TypeChecker_Env.try_lookup_val_decl
                                                    env1 uu___13 in
                                                match uu___12 with
                                                | FStar_Pervasives_Native.None
                                                    -> true
                                                | uu___13 -> false in
                                              if should_log
                                              then
                                                let uu___12 =
                                                  FStarC_Class_Show.show
                                                    (FStarC_Class_Show.show_either
                                                       FStarC_Syntax_Print.showable_bv
                                                       FStarC_Syntax_Print.showable_fv)
                                                    lb.FStarC_Syntax_Syntax.lbname in
                                                let uu___13 =
                                                  FStarC_Class_Show.show
                                                    FStarC_Syntax_Print.showable_term
                                                    lb.FStarC_Syntax_Syntax.lbtyp in
                                                FStarC_Compiler_Util.format2
                                                  "let %s : %s" uu___12
                                                  uu___13
                                              else "")
                                           (FStar_Pervasives_Native.snd lbs1) in
                                       FStarC_Compiler_String.concat "\n"
                                         uu___11 in
                                     FStarC_Compiler_Util.print1 "%s\n"
                                       uu___10
                                   else ());
                                  ([se3], [], env0)))))))
let (tc_decl' :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt ->
      (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_Syntax_Syntax.sigelt
        Prims.list * FStarC_TypeChecker_Env.env))
  =
  fun env0 ->
    fun se ->
      let env = env0 in
      let se1 =
        match se.FStarC_Syntax_Syntax.sigel with
        | FStarC_Syntax_Syntax.Sig_fail uu___ -> se
        | uu___ -> tc_decl_attributes env se in
      FStarC_TypeChecker_Quals.check_sigelt_quals_pre env se1;
      proc_check_with se1.FStarC_Syntax_Syntax.sigattrs
        (fun uu___1 ->
           let r = se1.FStarC_Syntax_Syntax.sigrng in
           let se2 =
             let uu___2 = FStarC_Options.record_options () in
             if uu___2 then store_sigopts se1 else se1 in
           match se2.FStarC_Syntax_Syntax.sigel with
           | FStarC_Syntax_Syntax.Sig_inductive_typ uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStarC_Syntax_Syntax.Sig_datacon uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStarC_Syntax_Syntax.Sig_fail
               { FStarC_Syntax_Syntax.errs = uu___2;
                 FStarC_Syntax_Syntax.fail_in_lax = false;
                 FStarC_Syntax_Syntax.ses1 = uu___3;_}
               when env.FStarC_TypeChecker_Env.admit ->
               ((let uu___5 = FStarC_Compiler_Debug.any () in
                 if uu___5
                 then
                   let uu___6 =
                     FStarC_Syntax_Print.sigelt_to_string_short se2 in
                   FStarC_Compiler_Util.print1
                     "Skipping %s since env.admit=true and this is not an expect_lax_failure\n"
                     uu___6
                 else ());
                ([], [], env))
           | FStarC_Syntax_Syntax.Sig_fail
               { FStarC_Syntax_Syntax.errs = expected_errors;
                 FStarC_Syntax_Syntax.fail_in_lax = lax;
                 FStarC_Syntax_Syntax.ses1 = ses;_}
               ->
               let env' =
                 if lax
                 then
                   {
                     FStarC_TypeChecker_Env.solver =
                       (env.FStarC_TypeChecker_Env.solver);
                     FStarC_TypeChecker_Env.range =
                       (env.FStarC_TypeChecker_Env.range);
                     FStarC_TypeChecker_Env.curmodule =
                       (env.FStarC_TypeChecker_Env.curmodule);
                     FStarC_TypeChecker_Env.gamma =
                       (env.FStarC_TypeChecker_Env.gamma);
                     FStarC_TypeChecker_Env.gamma_sig =
                       (env.FStarC_TypeChecker_Env.gamma_sig);
                     FStarC_TypeChecker_Env.gamma_cache =
                       (env.FStarC_TypeChecker_Env.gamma_cache);
                     FStarC_TypeChecker_Env.modules =
                       (env.FStarC_TypeChecker_Env.modules);
                     FStarC_TypeChecker_Env.expected_typ =
                       (env.FStarC_TypeChecker_Env.expected_typ);
                     FStarC_TypeChecker_Env.sigtab =
                       (env.FStarC_TypeChecker_Env.sigtab);
                     FStarC_TypeChecker_Env.attrtab =
                       (env.FStarC_TypeChecker_Env.attrtab);
                     FStarC_TypeChecker_Env.instantiate_imp =
                       (env.FStarC_TypeChecker_Env.instantiate_imp);
                     FStarC_TypeChecker_Env.effects =
                       (env.FStarC_TypeChecker_Env.effects);
                     FStarC_TypeChecker_Env.generalize =
                       (env.FStarC_TypeChecker_Env.generalize);
                     FStarC_TypeChecker_Env.letrecs =
                       (env.FStarC_TypeChecker_Env.letrecs);
                     FStarC_TypeChecker_Env.top_level =
                       (env.FStarC_TypeChecker_Env.top_level);
                     FStarC_TypeChecker_Env.check_uvars =
                       (env.FStarC_TypeChecker_Env.check_uvars);
                     FStarC_TypeChecker_Env.use_eq_strict =
                       (env.FStarC_TypeChecker_Env.use_eq_strict);
                     FStarC_TypeChecker_Env.is_iface =
                       (env.FStarC_TypeChecker_Env.is_iface);
                     FStarC_TypeChecker_Env.admit = true;
                     FStarC_TypeChecker_Env.lax_universes =
                       (env.FStarC_TypeChecker_Env.lax_universes);
                     FStarC_TypeChecker_Env.phase1 =
                       (env.FStarC_TypeChecker_Env.phase1);
                     FStarC_TypeChecker_Env.failhard =
                       (env.FStarC_TypeChecker_Env.failhard);
                     FStarC_TypeChecker_Env.flychecking =
                       (env.FStarC_TypeChecker_Env.flychecking);
                     FStarC_TypeChecker_Env.uvar_subtyping =
                       (env.FStarC_TypeChecker_Env.uvar_subtyping);
                     FStarC_TypeChecker_Env.intactics =
                       (env.FStarC_TypeChecker_Env.intactics);
                     FStarC_TypeChecker_Env.nocoerce =
                       (env.FStarC_TypeChecker_Env.nocoerce);
                     FStarC_TypeChecker_Env.tc_term =
                       (env.FStarC_TypeChecker_Env.tc_term);
                     FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.universe_of =
                       (env.FStarC_TypeChecker_Env.universe_of);
                     FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.teq_nosmt_force =
                       (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                     FStarC_TypeChecker_Env.subtype_nosmt_force =
                       (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                     FStarC_TypeChecker_Env.qtbl_name_and_index =
                       (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                     FStarC_TypeChecker_Env.normalized_eff_names =
                       (env.FStarC_TypeChecker_Env.normalized_eff_names);
                     FStarC_TypeChecker_Env.fv_delta_depths =
                       (env.FStarC_TypeChecker_Env.fv_delta_depths);
                     FStarC_TypeChecker_Env.proof_ns =
                       (env.FStarC_TypeChecker_Env.proof_ns);
                     FStarC_TypeChecker_Env.synth_hook =
                       (env.FStarC_TypeChecker_Env.synth_hook);
                     FStarC_TypeChecker_Env.try_solve_implicits_hook =
                       (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                     FStarC_TypeChecker_Env.splice =
                       (env.FStarC_TypeChecker_Env.splice);
                     FStarC_TypeChecker_Env.mpreprocess =
                       (env.FStarC_TypeChecker_Env.mpreprocess);
                     FStarC_TypeChecker_Env.postprocess =
                       (env.FStarC_TypeChecker_Env.postprocess);
                     FStarC_TypeChecker_Env.identifier_info =
                       (env.FStarC_TypeChecker_Env.identifier_info);
                     FStarC_TypeChecker_Env.tc_hooks =
                       (env.FStarC_TypeChecker_Env.tc_hooks);
                     FStarC_TypeChecker_Env.dsenv =
                       (env.FStarC_TypeChecker_Env.dsenv);
                     FStarC_TypeChecker_Env.nbe =
                       (env.FStarC_TypeChecker_Env.nbe);
                     FStarC_TypeChecker_Env.strict_args_tab =
                       (env.FStarC_TypeChecker_Env.strict_args_tab);
                     FStarC_TypeChecker_Env.erasable_types_tab =
                       (env.FStarC_TypeChecker_Env.erasable_types_tab);
                     FStarC_TypeChecker_Env.enable_defer_to_tac =
                       (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                     FStarC_TypeChecker_Env.unif_allow_ref_guards =
                       (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                     FStarC_TypeChecker_Env.erase_erasable_args =
                       (env.FStarC_TypeChecker_Env.erase_erasable_args);
                     FStarC_TypeChecker_Env.core_check =
                       (env.FStarC_TypeChecker_Env.core_check);
                     FStarC_TypeChecker_Env.missing_decl =
                       (env.FStarC_TypeChecker_Env.missing_decl)
                   }
                 else env in
               let env'1 = FStarC_TypeChecker_Env.push env' "expect_failure" in
               ((let uu___3 = FStarC_Compiler_Debug.low () in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       FStarC_Compiler_List.map
                         FStarC_Compiler_Util.string_of_int expected_errors in
                     FStarC_Compiler_String.concat "; " uu___5 in
                   FStarC_Compiler_Util.print1 ">> Expecting errors: [%s]\n"
                     uu___4
                 else ());
                (let uu___3 =
                   FStarC_Errors.catch_errors
                     (fun uu___4 ->
                        FStarC_Options.with_saved_options
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 FStarC_Compiler_Effect.op_Bang tc_decls_knot in
                               FStarC_Compiler_Util.must uu___7 in
                             uu___6 env'1 ses)) in
                 match uu___3 with
                 | (errs, uu___4) ->
                     ((let uu___6 =
                         (FStarC_Options.print_expected_failures ()) ||
                           (FStarC_Compiler_Debug.low ()) in
                       if uu___6
                       then
                         (FStarC_Compiler_Util.print_string
                            ">> Got issues: [\n";
                          FStarC_Compiler_List.iter FStarC_Errors.print_issue
                            errs;
                          FStarC_Compiler_Util.print_string ">>]\n")
                       else ());
                      (let uu___6 =
                         FStarC_TypeChecker_Env.pop env'1 "expect_failure" in
                       let actual_errors =
                         FStarC_Compiler_List.concatMap
                           (fun i ->
                              FStarC_Common.list_of_option
                                i.FStarC_Errors.issue_number) errs in
                       (match errs with
                        | [] ->
                            (FStarC_Compiler_List.iter
                               FStarC_Errors.print_issue errs;
                             (let uu___9 =
                                let uu___10 =
                                  FStarC_Errors_Msg.text
                                    "This top-level definition was expected to fail, but it succeeded" in
                                [uu___10] in
                              FStarC_Errors.log_issue
                                FStarC_Syntax_Syntax.has_range_sigelt se2
                                FStarC_Errors_Codes.Error_DidNotFail ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_list_doc)
                                (Obj.magic uu___9)))
                        | uu___8 ->
                            if expected_errors <> []
                            then
                              let uu___9 =
                                FStarC_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors in
                              (match uu___9 with
                               | FStar_Pervasives_Native.None -> ()
                               | FStar_Pervasives_Native.Some (e, n1, n2) ->
                                   (FStarC_Compiler_List.iter
                                      FStarC_Errors.print_issue errs;
                                    (let uu___11 =
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             FStarC_Errors_Msg.text
                                               "This top-level definition was expected to raise error codes" in
                                           let uu___15 =
                                             FStarC_Class_PP.pp
                                               (FStarC_Class_PP.pp_list
                                                  FStarC_Class_PP.pp_int)
                                               expected_errors in
                                           FStarC_Pprint.prefix
                                             (Prims.of_int (2)) Prims.int_one
                                             uu___14 uu___15 in
                                         let uu___14 =
                                           let uu___15 =
                                             let uu___16 =
                                               FStarC_Errors_Msg.text
                                                 "but it raised" in
                                             let uu___17 =
                                               FStarC_Class_PP.pp
                                                 (FStarC_Class_PP.pp_list
                                                    FStarC_Class_PP.pp_int)
                                                 actual_errors in
                                             FStarC_Pprint.prefix
                                               (Prims.of_int (2))
                                               Prims.int_one uu___16 uu___17 in
                                           FStarC_Pprint.op_Hat_Hat uu___15
                                             FStarC_Pprint.dot in
                                         FStarC_Pprint.op_Hat_Slash_Hat
                                           uu___13 uu___14 in
                                       let uu___13 =
                                         let uu___14 =
                                           let uu___15 =
                                             let uu___16 =
                                               FStarC_Class_Show.show
                                                 FStarC_Class_Show.showable_int
                                                 e in
                                             let uu___17 =
                                               FStarC_Class_Show.show
                                                 FStarC_Class_Show.showable_int
                                                 n2 in
                                             let uu___18 =
                                               FStarC_Class_Show.show
                                                 FStarC_Class_Show.showable_int
                                                 n1 in
                                             FStarC_Compiler_Util.format3
                                               "Error #%s was raised %s times, instead of %s."
                                               uu___16 uu___17 uu___18 in
                                           FStarC_Errors_Msg.text uu___15 in
                                         [uu___14] in
                                       uu___12 :: uu___13 in
                                     FStarC_Errors.log_issue
                                       FStarC_Syntax_Syntax.has_range_sigelt
                                       se2
                                       FStarC_Errors_Codes.Error_DidNotFail
                                       ()
                                       (Obj.magic
                                          FStarC_Errors_Msg.is_error_message_list_doc)
                                       (Obj.magic uu___11))))
                            else ());
                       ([], [], env)))))
           | FStarC_Syntax_Syntax.Sig_bundle
               { FStarC_Syntax_Syntax.ses = ses;
                 FStarC_Syntax_Syntax.lids = lids;_}
               ->
               let env1 = FStarC_TypeChecker_Env.set_range env r in
               let ses1 =
                 let uu___2 = do_two_phases env1 in
                 if uu___2
                 then
                   run_phase1
                     (fun uu___3 ->
                        let ses2 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                tc_inductive
                                  {
                                    FStarC_TypeChecker_Env.solver =
                                      (env1.FStarC_TypeChecker_Env.solver);
                                    FStarC_TypeChecker_Env.range =
                                      (env1.FStarC_TypeChecker_Env.range);
                                    FStarC_TypeChecker_Env.curmodule =
                                      (env1.FStarC_TypeChecker_Env.curmodule);
                                    FStarC_TypeChecker_Env.gamma =
                                      (env1.FStarC_TypeChecker_Env.gamma);
                                    FStarC_TypeChecker_Env.gamma_sig =
                                      (env1.FStarC_TypeChecker_Env.gamma_sig);
                                    FStarC_TypeChecker_Env.gamma_cache =
                                      (env1.FStarC_TypeChecker_Env.gamma_cache);
                                    FStarC_TypeChecker_Env.modules =
                                      (env1.FStarC_TypeChecker_Env.modules);
                                    FStarC_TypeChecker_Env.expected_typ =
                                      (env1.FStarC_TypeChecker_Env.expected_typ);
                                    FStarC_TypeChecker_Env.sigtab =
                                      (env1.FStarC_TypeChecker_Env.sigtab);
                                    FStarC_TypeChecker_Env.attrtab =
                                      (env1.FStarC_TypeChecker_Env.attrtab);
                                    FStarC_TypeChecker_Env.instantiate_imp =
                                      (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                    FStarC_TypeChecker_Env.effects =
                                      (env1.FStarC_TypeChecker_Env.effects);
                                    FStarC_TypeChecker_Env.generalize =
                                      (env1.FStarC_TypeChecker_Env.generalize);
                                    FStarC_TypeChecker_Env.letrecs =
                                      (env1.FStarC_TypeChecker_Env.letrecs);
                                    FStarC_TypeChecker_Env.top_level =
                                      (env1.FStarC_TypeChecker_Env.top_level);
                                    FStarC_TypeChecker_Env.check_uvars =
                                      (env1.FStarC_TypeChecker_Env.check_uvars);
                                    FStarC_TypeChecker_Env.use_eq_strict =
                                      (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                    FStarC_TypeChecker_Env.is_iface =
                                      (env1.FStarC_TypeChecker_Env.is_iface);
                                    FStarC_TypeChecker_Env.admit = true;
                                    FStarC_TypeChecker_Env.lax_universes =
                                      (env1.FStarC_TypeChecker_Env.lax_universes);
                                    FStarC_TypeChecker_Env.phase1 = true;
                                    FStarC_TypeChecker_Env.failhard =
                                      (env1.FStarC_TypeChecker_Env.failhard);
                                    FStarC_TypeChecker_Env.flychecking =
                                      (env1.FStarC_TypeChecker_Env.flychecking);
                                    FStarC_TypeChecker_Env.uvar_subtyping =
                                      (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                    FStarC_TypeChecker_Env.intactics =
                                      (env1.FStarC_TypeChecker_Env.intactics);
                                    FStarC_TypeChecker_Env.nocoerce =
                                      (env1.FStarC_TypeChecker_Env.nocoerce);
                                    FStarC_TypeChecker_Env.tc_term =
                                      (env1.FStarC_TypeChecker_Env.tc_term);
                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.universe_of =
                                      (env1.FStarC_TypeChecker_Env.universe_of);
                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.teq_nosmt_force =
                                      (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                    FStarC_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                    FStarC_TypeChecker_Env.fv_delta_depths =
                                      (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                    FStarC_TypeChecker_Env.proof_ns =
                                      (env1.FStarC_TypeChecker_Env.proof_ns);
                                    FStarC_TypeChecker_Env.synth_hook =
                                      (env1.FStarC_TypeChecker_Env.synth_hook);
                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                    FStarC_TypeChecker_Env.splice =
                                      (env1.FStarC_TypeChecker_Env.splice);
                                    FStarC_TypeChecker_Env.mpreprocess =
                                      (env1.FStarC_TypeChecker_Env.mpreprocess);
                                    FStarC_TypeChecker_Env.postprocess =
                                      (env1.FStarC_TypeChecker_Env.postprocess);
                                    FStarC_TypeChecker_Env.identifier_info =
                                      (env1.FStarC_TypeChecker_Env.identifier_info);
                                    FStarC_TypeChecker_Env.tc_hooks =
                                      (env1.FStarC_TypeChecker_Env.tc_hooks);
                                    FStarC_TypeChecker_Env.dsenv =
                                      (env1.FStarC_TypeChecker_Env.dsenv);
                                    FStarC_TypeChecker_Env.nbe =
                                      (env1.FStarC_TypeChecker_Env.nbe);
                                    FStarC_TypeChecker_Env.strict_args_tab =
                                      (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                    FStarC_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                    FStarC_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                    FStarC_TypeChecker_Env.core_check =
                                      (env1.FStarC_TypeChecker_Env.core_check);
                                    FStarC_TypeChecker_Env.missing_decl =
                                      (env1.FStarC_TypeChecker_Env.missing_decl)
                                  } ses se2.FStarC_Syntax_Syntax.sigquals
                                  se2.FStarC_Syntax_Syntax.sigattrs lids in
                              FStar_Pervasives_Native.fst uu___6 in
                            FStarC_TypeChecker_Normalize.elim_uvars env1
                              uu___5 in
                          FStarC_Syntax_Util.ses_of_sigbundle uu___4 in
                        (let uu___5 =
                           (FStarC_Compiler_Debug.medium ()) ||
                             (FStarC_Compiler_Effect.op_Bang dbg_TwoPhases) in
                         if uu___5
                         then
                           let uu___6 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_sigelt
                               {
                                 FStarC_Syntax_Syntax.sigel =
                                   (FStarC_Syntax_Syntax.Sig_bundle
                                      {
                                        FStarC_Syntax_Syntax.ses = ses2;
                                        FStarC_Syntax_Syntax.lids = lids
                                      });
                                 FStarC_Syntax_Syntax.sigrng =
                                   (se2.FStarC_Syntax_Syntax.sigrng);
                                 FStarC_Syntax_Syntax.sigquals =
                                   (se2.FStarC_Syntax_Syntax.sigquals);
                                 FStarC_Syntax_Syntax.sigmeta =
                                   (se2.FStarC_Syntax_Syntax.sigmeta);
                                 FStarC_Syntax_Syntax.sigattrs =
                                   (se2.FStarC_Syntax_Syntax.sigattrs);
                                 FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                   (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                 FStarC_Syntax_Syntax.sigopts =
                                   (se2.FStarC_Syntax_Syntax.sigopts)
                               } in
                           FStarC_Compiler_Util.print1
                             "Inductive after phase 1: %s\n" uu___6
                         else ());
                        ses2)
                 else ses in
               let uu___2 =
                 tc_inductive env1 ses1 se2.FStarC_Syntax_Syntax.sigquals
                   se2.FStarC_Syntax_Syntax.sigattrs lids in
               (match uu___2 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      {
                        FStarC_Syntax_Syntax.sigel =
                          (sigbndle.FStarC_Syntax_Syntax.sigel);
                        FStarC_Syntax_Syntax.sigrng =
                          (sigbndle.FStarC_Syntax_Syntax.sigrng);
                        FStarC_Syntax_Syntax.sigquals =
                          (sigbndle.FStarC_Syntax_Syntax.sigquals);
                        FStarC_Syntax_Syntax.sigmeta =
                          (sigbndle.FStarC_Syntax_Syntax.sigmeta);
                        FStarC_Syntax_Syntax.sigattrs =
                          (se2.FStarC_Syntax_Syntax.sigattrs);
                        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                          (sigbndle.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                        FStarC_Syntax_Syntax.sigopts =
                          (sigbndle.FStarC_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStarC_Syntax_Syntax.Sig_pragma p ->
               (FStarC_Syntax_Util.process_pragma p r; ([se2], [], env0))
           | FStarC_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStarC_Syntax_Syntax.combinators with
                 | FStarC_Syntax_Syntax.DM4F_eff combs ->
                     let uu___2 =
                       FStarC_Syntax_Subst.compress
                         (FStar_Pervasives_Native.snd
                            combs.FStarC_Syntax_Syntax.ret_wp) in
                     (match uu___2 with
                      | {
                          FStarC_Syntax_Syntax.n =
                            FStarC_Syntax_Syntax.Tm_unknown;
                          FStarC_Syntax_Syntax.pos = uu___3;
                          FStarC_Syntax_Syntax.vars = uu___4;
                          FStarC_Syntax_Syntax.hash_code = uu___5;_} -> true
                      | uu___3 -> false)
                 | uu___2 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStarC_TypeChecker_Env.set_range env r in
                 let uu___2 =
                   FStarC_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu___2 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [{
                               FStarC_Syntax_Syntax.sigel =
                                 (FStarC_Syntax_Syntax.Sig_new_effect ne1);
                               FStarC_Syntax_Syntax.sigrng =
                                 (se2.FStarC_Syntax_Syntax.sigrng);
                               FStarC_Syntax_Syntax.sigquals =
                                 (se2.FStarC_Syntax_Syntax.sigquals);
                               FStarC_Syntax_Syntax.sigmeta =
                                 (se2.FStarC_Syntax_Syntax.sigmeta);
                               FStarC_Syntax_Syntax.sigattrs =
                                 (se2.FStarC_Syntax_Syntax.sigattrs);
                               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                 (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                               FStarC_Syntax_Syntax.sigopts =
                                 (se2.FStarC_Syntax_Syntax.sigopts)
                             };
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [{
                               FStarC_Syntax_Syntax.sigel =
                                 (FStarC_Syntax_Syntax.Sig_new_effect ne1);
                               FStarC_Syntax_Syntax.sigrng =
                                 (se2.FStarC_Syntax_Syntax.sigrng);
                               FStarC_Syntax_Syntax.sigquals =
                                 (se2.FStarC_Syntax_Syntax.sigquals);
                               FStarC_Syntax_Syntax.sigmeta =
                                 (se2.FStarC_Syntax_Syntax.sigmeta);
                               FStarC_Syntax_Syntax.sigattrs =
                                 (se2.FStarC_Syntax_Syntax.sigattrs);
                               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                 (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                               FStarC_Syntax_Syntax.sigopts =
                                 (se2.FStarC_Syntax_Syntax.sigopts)
                             }] in
                      let effect_and_lift_ses1 =
                        FStarC_Compiler_List.map
                          (fun sigelt ->
                             {
                               FStarC_Syntax_Syntax.sigel =
                                 (sigelt.FStarC_Syntax_Syntax.sigel);
                               FStarC_Syntax_Syntax.sigrng =
                                 (sigelt.FStarC_Syntax_Syntax.sigrng);
                               FStarC_Syntax_Syntax.sigquals =
                                 (sigelt.FStarC_Syntax_Syntax.sigquals);
                               FStarC_Syntax_Syntax.sigmeta =
                                 (let uu___3 =
                                    sigelt.FStarC_Syntax_Syntax.sigmeta in
                                  {
                                    FStarC_Syntax_Syntax.sigmeta_active =
                                      (uu___3.FStarC_Syntax_Syntax.sigmeta_active);
                                    FStarC_Syntax_Syntax.sigmeta_fact_db_ids
                                      =
                                      (uu___3.FStarC_Syntax_Syntax.sigmeta_fact_db_ids);
                                    FStarC_Syntax_Syntax.sigmeta_admit = true;
                                    FStarC_Syntax_Syntax.sigmeta_spliced =
                                      (uu___3.FStarC_Syntax_Syntax.sigmeta_spliced);
                                    FStarC_Syntax_Syntax.sigmeta_already_checked
                                      =
                                      (uu___3.FStarC_Syntax_Syntax.sigmeta_already_checked);
                                    FStarC_Syntax_Syntax.sigmeta_extension_data
                                      =
                                      (uu___3.FStarC_Syntax_Syntax.sigmeta_extension_data)
                                  });
                               FStarC_Syntax_Syntax.sigattrs =
                                 (sigelt.FStarC_Syntax_Syntax.sigattrs);
                               FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                 (sigelt.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                               FStarC_Syntax_Syntax.sigopts =
                                 (sigelt.FStarC_Syntax_Syntax.sigopts)
                             }) effect_and_lift_ses in
                      ([],
                        (FStarC_Compiler_List.op_At ses effect_and_lift_ses1),
                        env0))
               else
                 (let ne1 =
                    let uu___3 = do_two_phases env in
                    if uu___3
                    then
                      run_phase1
                        (fun uu___4 ->
                           let ne2 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStarC_TypeChecker_TcEffect.tc_eff_decl
                                     {
                                       FStarC_TypeChecker_Env.solver =
                                         (env.FStarC_TypeChecker_Env.solver);
                                       FStarC_TypeChecker_Env.range =
                                         (env.FStarC_TypeChecker_Env.range);
                                       FStarC_TypeChecker_Env.curmodule =
                                         (env.FStarC_TypeChecker_Env.curmodule);
                                       FStarC_TypeChecker_Env.gamma =
                                         (env.FStarC_TypeChecker_Env.gamma);
                                       FStarC_TypeChecker_Env.gamma_sig =
                                         (env.FStarC_TypeChecker_Env.gamma_sig);
                                       FStarC_TypeChecker_Env.gamma_cache =
                                         (env.FStarC_TypeChecker_Env.gamma_cache);
                                       FStarC_TypeChecker_Env.modules =
                                         (env.FStarC_TypeChecker_Env.modules);
                                       FStarC_TypeChecker_Env.expected_typ =
                                         (env.FStarC_TypeChecker_Env.expected_typ);
                                       FStarC_TypeChecker_Env.sigtab =
                                         (env.FStarC_TypeChecker_Env.sigtab);
                                       FStarC_TypeChecker_Env.attrtab =
                                         (env.FStarC_TypeChecker_Env.attrtab);
                                       FStarC_TypeChecker_Env.instantiate_imp
                                         =
                                         (env.FStarC_TypeChecker_Env.instantiate_imp);
                                       FStarC_TypeChecker_Env.effects =
                                         (env.FStarC_TypeChecker_Env.effects);
                                       FStarC_TypeChecker_Env.generalize =
                                         (env.FStarC_TypeChecker_Env.generalize);
                                       FStarC_TypeChecker_Env.letrecs =
                                         (env.FStarC_TypeChecker_Env.letrecs);
                                       FStarC_TypeChecker_Env.top_level =
                                         (env.FStarC_TypeChecker_Env.top_level);
                                       FStarC_TypeChecker_Env.check_uvars =
                                         (env.FStarC_TypeChecker_Env.check_uvars);
                                       FStarC_TypeChecker_Env.use_eq_strict =
                                         (env.FStarC_TypeChecker_Env.use_eq_strict);
                                       FStarC_TypeChecker_Env.is_iface =
                                         (env.FStarC_TypeChecker_Env.is_iface);
                                       FStarC_TypeChecker_Env.admit = true;
                                       FStarC_TypeChecker_Env.lax_universes =
                                         (env.FStarC_TypeChecker_Env.lax_universes);
                                       FStarC_TypeChecker_Env.phase1 = true;
                                       FStarC_TypeChecker_Env.failhard =
                                         (env.FStarC_TypeChecker_Env.failhard);
                                       FStarC_TypeChecker_Env.flychecking =
                                         (env.FStarC_TypeChecker_Env.flychecking);
                                       FStarC_TypeChecker_Env.uvar_subtyping
                                         =
                                         (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                       FStarC_TypeChecker_Env.intactics =
                                         (env.FStarC_TypeChecker_Env.intactics);
                                       FStarC_TypeChecker_Env.nocoerce =
                                         (env.FStarC_TypeChecker_Env.nocoerce);
                                       FStarC_TypeChecker_Env.tc_term =
                                         (env.FStarC_TypeChecker_Env.tc_term);
                                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                         =
                                         (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                       FStarC_TypeChecker_Env.universe_of =
                                         (env.FStarC_TypeChecker_Env.universe_of);
                                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                         =
                                         (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                       FStarC_TypeChecker_Env.teq_nosmt_force
                                         =
                                         (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                       FStarC_TypeChecker_Env.subtype_nosmt_force
                                         =
                                         (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                       FStarC_TypeChecker_Env.qtbl_name_and_index
                                         =
                                         (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                       FStarC_TypeChecker_Env.normalized_eff_names
                                         =
                                         (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                       FStarC_TypeChecker_Env.fv_delta_depths
                                         =
                                         (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                       FStarC_TypeChecker_Env.proof_ns =
                                         (env.FStarC_TypeChecker_Env.proof_ns);
                                       FStarC_TypeChecker_Env.synth_hook =
                                         (env.FStarC_TypeChecker_Env.synth_hook);
                                       FStarC_TypeChecker_Env.try_solve_implicits_hook
                                         =
                                         (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                       FStarC_TypeChecker_Env.splice =
                                         (env.FStarC_TypeChecker_Env.splice);
                                       FStarC_TypeChecker_Env.mpreprocess =
                                         (env.FStarC_TypeChecker_Env.mpreprocess);
                                       FStarC_TypeChecker_Env.postprocess =
                                         (env.FStarC_TypeChecker_Env.postprocess);
                                       FStarC_TypeChecker_Env.identifier_info
                                         =
                                         (env.FStarC_TypeChecker_Env.identifier_info);
                                       FStarC_TypeChecker_Env.tc_hooks =
                                         (env.FStarC_TypeChecker_Env.tc_hooks);
                                       FStarC_TypeChecker_Env.dsenv =
                                         (env.FStarC_TypeChecker_Env.dsenv);
                                       FStarC_TypeChecker_Env.nbe =
                                         (env.FStarC_TypeChecker_Env.nbe);
                                       FStarC_TypeChecker_Env.strict_args_tab
                                         =
                                         (env.FStarC_TypeChecker_Env.strict_args_tab);
                                       FStarC_TypeChecker_Env.erasable_types_tab
                                         =
                                         (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                       FStarC_TypeChecker_Env.enable_defer_to_tac
                                         =
                                         (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                       FStarC_TypeChecker_Env.unif_allow_ref_guards
                                         =
                                         (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                       FStarC_TypeChecker_Env.erase_erasable_args
                                         =
                                         (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                       FStarC_TypeChecker_Env.core_check =
                                         (env.FStarC_TypeChecker_Env.core_check);
                                       FStarC_TypeChecker_Env.missing_decl =
                                         (env.FStarC_TypeChecker_Env.missing_decl)
                                     } ne se2.FStarC_Syntax_Syntax.sigquals
                                     se2.FStarC_Syntax_Syntax.sigattrs in
                                 {
                                   FStarC_Syntax_Syntax.sigel =
                                     (FStarC_Syntax_Syntax.Sig_new_effect
                                        uu___7);
                                   FStarC_Syntax_Syntax.sigrng =
                                     (se2.FStarC_Syntax_Syntax.sigrng);
                                   FStarC_Syntax_Syntax.sigquals =
                                     (se2.FStarC_Syntax_Syntax.sigquals);
                                   FStarC_Syntax_Syntax.sigmeta =
                                     (se2.FStarC_Syntax_Syntax.sigmeta);
                                   FStarC_Syntax_Syntax.sigattrs =
                                     (se2.FStarC_Syntax_Syntax.sigattrs);
                                   FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                     =
                                     (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                   FStarC_Syntax_Syntax.sigopts =
                                     (se2.FStarC_Syntax_Syntax.sigopts)
                                 } in
                               FStarC_TypeChecker_Normalize.elim_uvars env
                                 uu___6 in
                             FStarC_Syntax_Util.eff_decl_of_new_effect uu___5 in
                           (let uu___6 =
                              (FStarC_Compiler_Debug.medium ()) ||
                                (FStarC_Compiler_Effect.op_Bang dbg_TwoPhases) in
                            if uu___6
                            then
                              let uu___7 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_sigelt
                                  {
                                    FStarC_Syntax_Syntax.sigel =
                                      (FStarC_Syntax_Syntax.Sig_new_effect
                                         ne2);
                                    FStarC_Syntax_Syntax.sigrng =
                                      (se2.FStarC_Syntax_Syntax.sigrng);
                                    FStarC_Syntax_Syntax.sigquals =
                                      (se2.FStarC_Syntax_Syntax.sigquals);
                                    FStarC_Syntax_Syntax.sigmeta =
                                      (se2.FStarC_Syntax_Syntax.sigmeta);
                                    FStarC_Syntax_Syntax.sigattrs =
                                      (se2.FStarC_Syntax_Syntax.sigattrs);
                                    FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                      =
                                      (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                    FStarC_Syntax_Syntax.sigopts =
                                      (se2.FStarC_Syntax_Syntax.sigopts)
                                  } in
                              FStarC_Compiler_Util.print1
                                "Effect decl after phase 1: %s\n" uu___7
                            else ());
                           ne2)
                    else ne in
                  let ne2 =
                    FStarC_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se2.FStarC_Syntax_Syntax.sigquals
                      se2.FStarC_Syntax_Syntax.sigattrs in
                  let se3 =
                    {
                      FStarC_Syntax_Syntax.sigel =
                        (FStarC_Syntax_Syntax.Sig_new_effect ne2);
                      FStarC_Syntax_Syntax.sigrng =
                        (se2.FStarC_Syntax_Syntax.sigrng);
                      FStarC_Syntax_Syntax.sigquals =
                        (se2.FStarC_Syntax_Syntax.sigquals);
                      FStarC_Syntax_Syntax.sigmeta =
                        (se2.FStarC_Syntax_Syntax.sigmeta);
                      FStarC_Syntax_Syntax.sigattrs =
                        (se2.FStarC_Syntax_Syntax.sigattrs);
                      FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                        (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                      FStarC_Syntax_Syntax.sigopts =
                        (se2.FStarC_Syntax_Syntax.sigopts)
                    } in
                  ([se3], [], env0))
           | FStarC_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStarC_TypeChecker_TcEffect.tc_lift env sub r in
               let se3 =
                 {
                   FStarC_Syntax_Syntax.sigel =
                     (FStarC_Syntax_Syntax.Sig_sub_effect sub1);
                   FStarC_Syntax_Syntax.sigrng =
                     (se2.FStarC_Syntax_Syntax.sigrng);
                   FStarC_Syntax_Syntax.sigquals =
                     (se2.FStarC_Syntax_Syntax.sigquals);
                   FStarC_Syntax_Syntax.sigmeta =
                     (se2.FStarC_Syntax_Syntax.sigmeta);
                   FStarC_Syntax_Syntax.sigattrs =
                     (se2.FStarC_Syntax_Syntax.sigattrs);
                   FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                     (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                   FStarC_Syntax_Syntax.sigopts =
                     (se2.FStarC_Syntax_Syntax.sigopts)
                 } in
               ([se3], [], env)
           | FStarC_Syntax_Syntax.Sig_effect_abbrev
               { FStarC_Syntax_Syntax.lid4 = lid;
                 FStarC_Syntax_Syntax.us4 = uvs;
                 FStarC_Syntax_Syntax.bs2 = tps;
                 FStarC_Syntax_Syntax.comp1 = c;
                 FStarC_Syntax_Syntax.cflags = flags;_}
               ->
               let uu___2 =
                 let uu___3 = do_two_phases env in
                 if uu___3
                 then
                   run_phase1
                     (fun uu___4 ->
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStarC_TypeChecker_TcEffect.tc_effect_abbrev
                                {
                                  FStarC_TypeChecker_Env.solver =
                                    (env.FStarC_TypeChecker_Env.solver);
                                  FStarC_TypeChecker_Env.range =
                                    (env.FStarC_TypeChecker_Env.range);
                                  FStarC_TypeChecker_Env.curmodule =
                                    (env.FStarC_TypeChecker_Env.curmodule);
                                  FStarC_TypeChecker_Env.gamma =
                                    (env.FStarC_TypeChecker_Env.gamma);
                                  FStarC_TypeChecker_Env.gamma_sig =
                                    (env.FStarC_TypeChecker_Env.gamma_sig);
                                  FStarC_TypeChecker_Env.gamma_cache =
                                    (env.FStarC_TypeChecker_Env.gamma_cache);
                                  FStarC_TypeChecker_Env.modules =
                                    (env.FStarC_TypeChecker_Env.modules);
                                  FStarC_TypeChecker_Env.expected_typ =
                                    (env.FStarC_TypeChecker_Env.expected_typ);
                                  FStarC_TypeChecker_Env.sigtab =
                                    (env.FStarC_TypeChecker_Env.sigtab);
                                  FStarC_TypeChecker_Env.attrtab =
                                    (env.FStarC_TypeChecker_Env.attrtab);
                                  FStarC_TypeChecker_Env.instantiate_imp =
                                    (env.FStarC_TypeChecker_Env.instantiate_imp);
                                  FStarC_TypeChecker_Env.effects =
                                    (env.FStarC_TypeChecker_Env.effects);
                                  FStarC_TypeChecker_Env.generalize =
                                    (env.FStarC_TypeChecker_Env.generalize);
                                  FStarC_TypeChecker_Env.letrecs =
                                    (env.FStarC_TypeChecker_Env.letrecs);
                                  FStarC_TypeChecker_Env.top_level =
                                    (env.FStarC_TypeChecker_Env.top_level);
                                  FStarC_TypeChecker_Env.check_uvars =
                                    (env.FStarC_TypeChecker_Env.check_uvars);
                                  FStarC_TypeChecker_Env.use_eq_strict =
                                    (env.FStarC_TypeChecker_Env.use_eq_strict);
                                  FStarC_TypeChecker_Env.is_iface =
                                    (env.FStarC_TypeChecker_Env.is_iface);
                                  FStarC_TypeChecker_Env.admit = true;
                                  FStarC_TypeChecker_Env.lax_universes =
                                    (env.FStarC_TypeChecker_Env.lax_universes);
                                  FStarC_TypeChecker_Env.phase1 = true;
                                  FStarC_TypeChecker_Env.failhard =
                                    (env.FStarC_TypeChecker_Env.failhard);
                                  FStarC_TypeChecker_Env.flychecking =
                                    (env.FStarC_TypeChecker_Env.flychecking);
                                  FStarC_TypeChecker_Env.uvar_subtyping =
                                    (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                  FStarC_TypeChecker_Env.intactics =
                                    (env.FStarC_TypeChecker_Env.intactics);
                                  FStarC_TypeChecker_Env.nocoerce =
                                    (env.FStarC_TypeChecker_Env.nocoerce);
                                  FStarC_TypeChecker_Env.tc_term =
                                    (env.FStarC_TypeChecker_Env.tc_term);
                                  FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStarC_TypeChecker_Env.universe_of =
                                    (env.FStarC_TypeChecker_Env.universe_of);
                                  FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStarC_TypeChecker_Env.teq_nosmt_force =
                                    (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                  FStarC_TypeChecker_Env.subtype_nosmt_force
                                    =
                                    (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                  FStarC_TypeChecker_Env.qtbl_name_and_index
                                    =
                                    (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                  FStarC_TypeChecker_Env.normalized_eff_names
                                    =
                                    (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                  FStarC_TypeChecker_Env.fv_delta_depths =
                                    (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                  FStarC_TypeChecker_Env.proof_ns =
                                    (env.FStarC_TypeChecker_Env.proof_ns);
                                  FStarC_TypeChecker_Env.synth_hook =
                                    (env.FStarC_TypeChecker_Env.synth_hook);
                                  FStarC_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                  FStarC_TypeChecker_Env.splice =
                                    (env.FStarC_TypeChecker_Env.splice);
                                  FStarC_TypeChecker_Env.mpreprocess =
                                    (env.FStarC_TypeChecker_Env.mpreprocess);
                                  FStarC_TypeChecker_Env.postprocess =
                                    (env.FStarC_TypeChecker_Env.postprocess);
                                  FStarC_TypeChecker_Env.identifier_info =
                                    (env.FStarC_TypeChecker_Env.identifier_info);
                                  FStarC_TypeChecker_Env.tc_hooks =
                                    (env.FStarC_TypeChecker_Env.tc_hooks);
                                  FStarC_TypeChecker_Env.dsenv =
                                    (env.FStarC_TypeChecker_Env.dsenv);
                                  FStarC_TypeChecker_Env.nbe =
                                    (env.FStarC_TypeChecker_Env.nbe);
                                  FStarC_TypeChecker_Env.strict_args_tab =
                                    (env.FStarC_TypeChecker_Env.strict_args_tab);
                                  FStarC_TypeChecker_Env.erasable_types_tab =
                                    (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                  FStarC_TypeChecker_Env.enable_defer_to_tac
                                    =
                                    (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                  FStarC_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                  FStarC_TypeChecker_Env.erase_erasable_args
                                    =
                                    (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                  FStarC_TypeChecker_Env.core_check =
                                    (env.FStarC_TypeChecker_Env.core_check);
                                  FStarC_TypeChecker_Env.missing_decl =
                                    (env.FStarC_TypeChecker_Env.missing_decl)
                                } (lid, uvs, tps, c) r in
                            match uu___7 with
                            | (lid1, uvs1, tps1, c1) ->
                                {
                                  FStarC_Syntax_Syntax.sigel =
                                    (FStarC_Syntax_Syntax.Sig_effect_abbrev
                                       {
                                         FStarC_Syntax_Syntax.lid4 = lid1;
                                         FStarC_Syntax_Syntax.us4 = uvs1;
                                         FStarC_Syntax_Syntax.bs2 = tps1;
                                         FStarC_Syntax_Syntax.comp1 = c1;
                                         FStarC_Syntax_Syntax.cflags = flags
                                       });
                                  FStarC_Syntax_Syntax.sigrng =
                                    (se2.FStarC_Syntax_Syntax.sigrng);
                                  FStarC_Syntax_Syntax.sigquals =
                                    (se2.FStarC_Syntax_Syntax.sigquals);
                                  FStarC_Syntax_Syntax.sigmeta =
                                    (se2.FStarC_Syntax_Syntax.sigmeta);
                                  FStarC_Syntax_Syntax.sigattrs =
                                    (se2.FStarC_Syntax_Syntax.sigattrs);
                                  FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                    (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                  FStarC_Syntax_Syntax.sigopts =
                                    (se2.FStarC_Syntax_Syntax.sigopts)
                                } in
                          FStarC_TypeChecker_Normalize.elim_uvars env uu___6 in
                        match uu___5.FStarC_Syntax_Syntax.sigel with
                        | FStarC_Syntax_Syntax.Sig_effect_abbrev
                            { FStarC_Syntax_Syntax.lid4 = lid1;
                              FStarC_Syntax_Syntax.us4 = uvs1;
                              FStarC_Syntax_Syntax.bs2 = tps1;
                              FStarC_Syntax_Syntax.comp1 = c1;
                              FStarC_Syntax_Syntax.cflags = uu___6;_}
                            -> (lid1, uvs1, tps1, c1)
                        | uu___6 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu___2 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu___3 =
                      FStarC_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu___3 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se3 =
                           {
                             FStarC_Syntax_Syntax.sigel =
                               (FStarC_Syntax_Syntax.Sig_effect_abbrev
                                  {
                                    FStarC_Syntax_Syntax.lid4 = lid2;
                                    FStarC_Syntax_Syntax.us4 = uvs2;
                                    FStarC_Syntax_Syntax.bs2 = tps2;
                                    FStarC_Syntax_Syntax.comp1 = c2;
                                    FStarC_Syntax_Syntax.cflags = flags
                                  });
                             FStarC_Syntax_Syntax.sigrng =
                               (se2.FStarC_Syntax_Syntax.sigrng);
                             FStarC_Syntax_Syntax.sigquals =
                               (se2.FStarC_Syntax_Syntax.sigquals);
                             FStarC_Syntax_Syntax.sigmeta =
                               (se2.FStarC_Syntax_Syntax.sigmeta);
                             FStarC_Syntax_Syntax.sigattrs =
                               (se2.FStarC_Syntax_Syntax.sigattrs);
                             FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                               (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                             FStarC_Syntax_Syntax.sigopts =
                               (se2.FStarC_Syntax_Syntax.sigopts)
                           } in
                         ([se3], [], env0)))
           | FStarC_Syntax_Syntax.Sig_declare_typ uu___2 when
               FStarC_Compiler_Util.for_some
                 (fun uu___3 ->
                    match uu___3 with
                    | FStarC_Syntax_Syntax.OnlyName -> true
                    | uu___4 -> false) se2.FStarC_Syntax_Syntax.sigquals
               -> ([], [], env0)
           | FStarC_Syntax_Syntax.Sig_let uu___2 when
               FStarC_Compiler_Util.for_some
                 (fun uu___3 ->
                    match uu___3 with
                    | FStarC_Syntax_Syntax.OnlyName -> true
                    | uu___4 -> false) se2.FStarC_Syntax_Syntax.sigquals
               -> ([], [], env0)
           | FStarC_Syntax_Syntax.Sig_declare_typ
               { FStarC_Syntax_Syntax.lid2 = lid;
                 FStarC_Syntax_Syntax.us2 = uvs;
                 FStarC_Syntax_Syntax.t2 = t;_}
               ->
               ((let uu___3 = FStarC_TypeChecker_Env.lid_exists env lid in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_Ident.showable_lident lid in
                         FStarC_Compiler_Util.format1
                           "Top-level declaration %s for a name that is already used in this module."
                           uu___7 in
                       FStarC_Errors_Msg.text uu___6 in
                     let uu___6 =
                       let uu___7 =
                         FStarC_Errors_Msg.text
                           "Top-level declarations must be unique in their module." in
                       [uu___7] in
                     uu___5 :: uu___6 in
                   FStarC_Errors.raise_error
                     FStarC_Class_HasRange.hasRange_range r
                     FStarC_Errors_Codes.Fatal_AlreadyDefinedTopLevelDeclaration
                     ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___4)
                 else ());
                (let env1 = FStarC_TypeChecker_Env.set_range env r in
                 let uu___3 =
                   let uu___4 = do_two_phases env1 in
                   if uu___4
                   then
                     run_phase1
                       (fun uu___5 ->
                          let uu___6 =
                            tc_declare_typ
                              {
                                FStarC_TypeChecker_Env.solver =
                                  (env1.FStarC_TypeChecker_Env.solver);
                                FStarC_TypeChecker_Env.range =
                                  (env1.FStarC_TypeChecker_Env.range);
                                FStarC_TypeChecker_Env.curmodule =
                                  (env1.FStarC_TypeChecker_Env.curmodule);
                                FStarC_TypeChecker_Env.gamma =
                                  (env1.FStarC_TypeChecker_Env.gamma);
                                FStarC_TypeChecker_Env.gamma_sig =
                                  (env1.FStarC_TypeChecker_Env.gamma_sig);
                                FStarC_TypeChecker_Env.gamma_cache =
                                  (env1.FStarC_TypeChecker_Env.gamma_cache);
                                FStarC_TypeChecker_Env.modules =
                                  (env1.FStarC_TypeChecker_Env.modules);
                                FStarC_TypeChecker_Env.expected_typ =
                                  (env1.FStarC_TypeChecker_Env.expected_typ);
                                FStarC_TypeChecker_Env.sigtab =
                                  (env1.FStarC_TypeChecker_Env.sigtab);
                                FStarC_TypeChecker_Env.attrtab =
                                  (env1.FStarC_TypeChecker_Env.attrtab);
                                FStarC_TypeChecker_Env.instantiate_imp =
                                  (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                FStarC_TypeChecker_Env.effects =
                                  (env1.FStarC_TypeChecker_Env.effects);
                                FStarC_TypeChecker_Env.generalize =
                                  (env1.FStarC_TypeChecker_Env.generalize);
                                FStarC_TypeChecker_Env.letrecs =
                                  (env1.FStarC_TypeChecker_Env.letrecs);
                                FStarC_TypeChecker_Env.top_level =
                                  (env1.FStarC_TypeChecker_Env.top_level);
                                FStarC_TypeChecker_Env.check_uvars =
                                  (env1.FStarC_TypeChecker_Env.check_uvars);
                                FStarC_TypeChecker_Env.use_eq_strict =
                                  (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                FStarC_TypeChecker_Env.is_iface =
                                  (env1.FStarC_TypeChecker_Env.is_iface);
                                FStarC_TypeChecker_Env.admit = true;
                                FStarC_TypeChecker_Env.lax_universes =
                                  (env1.FStarC_TypeChecker_Env.lax_universes);
                                FStarC_TypeChecker_Env.phase1 = true;
                                FStarC_TypeChecker_Env.failhard =
                                  (env1.FStarC_TypeChecker_Env.failhard);
                                FStarC_TypeChecker_Env.flychecking =
                                  (env1.FStarC_TypeChecker_Env.flychecking);
                                FStarC_TypeChecker_Env.uvar_subtyping =
                                  (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                FStarC_TypeChecker_Env.intactics =
                                  (env1.FStarC_TypeChecker_Env.intactics);
                                FStarC_TypeChecker_Env.nocoerce =
                                  (env1.FStarC_TypeChecker_Env.nocoerce);
                                FStarC_TypeChecker_Env.tc_term =
                                  (env1.FStarC_TypeChecker_Env.tc_term);
                                FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                  =
                                  (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                FStarC_TypeChecker_Env.universe_of =
                                  (env1.FStarC_TypeChecker_Env.universe_of);
                                FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                  =
                                  (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                FStarC_TypeChecker_Env.teq_nosmt_force =
                                  (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                FStarC_TypeChecker_Env.subtype_nosmt_force =
                                  (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                FStarC_TypeChecker_Env.qtbl_name_and_index =
                                  (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                FStarC_TypeChecker_Env.normalized_eff_names =
                                  (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                FStarC_TypeChecker_Env.fv_delta_depths =
                                  (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                FStarC_TypeChecker_Env.proof_ns =
                                  (env1.FStarC_TypeChecker_Env.proof_ns);
                                FStarC_TypeChecker_Env.synth_hook =
                                  (env1.FStarC_TypeChecker_Env.synth_hook);
                                FStarC_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                FStarC_TypeChecker_Env.splice =
                                  (env1.FStarC_TypeChecker_Env.splice);
                                FStarC_TypeChecker_Env.mpreprocess =
                                  (env1.FStarC_TypeChecker_Env.mpreprocess);
                                FStarC_TypeChecker_Env.postprocess =
                                  (env1.FStarC_TypeChecker_Env.postprocess);
                                FStarC_TypeChecker_Env.identifier_info =
                                  (env1.FStarC_TypeChecker_Env.identifier_info);
                                FStarC_TypeChecker_Env.tc_hooks =
                                  (env1.FStarC_TypeChecker_Env.tc_hooks);
                                FStarC_TypeChecker_Env.dsenv =
                                  (env1.FStarC_TypeChecker_Env.dsenv);
                                FStarC_TypeChecker_Env.nbe =
                                  (env1.FStarC_TypeChecker_Env.nbe);
                                FStarC_TypeChecker_Env.strict_args_tab =
                                  (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                FStarC_TypeChecker_Env.erasable_types_tab =
                                  (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                FStarC_TypeChecker_Env.enable_defer_to_tac =
                                  (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                FStarC_TypeChecker_Env.unif_allow_ref_guards
                                  =
                                  (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                FStarC_TypeChecker_Env.erase_erasable_args =
                                  (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                FStarC_TypeChecker_Env.core_check =
                                  (env1.FStarC_TypeChecker_Env.core_check);
                                FStarC_TypeChecker_Env.missing_decl =
                                  (env1.FStarC_TypeChecker_Env.missing_decl)
                              } (uvs, t) se2.FStarC_Syntax_Syntax.sigrng in
                          match uu___6 with
                          | (uvs1, t1) ->
                              ((let uu___8 =
                                  (FStarC_Compiler_Debug.medium ()) ||
                                    (FStarC_Compiler_Effect.op_Bang
                                       dbg_TwoPhases) in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term t1 in
                                  let uu___10 =
                                    FStarC_Class_Show.show
                                      (FStarC_Class_Show.show_list
                                         FStarC_Ident.showable_ident) uvs1 in
                                  FStarC_Compiler_Util.print2
                                    "Val declaration after phase 1: %s and uvs: %s\n"
                                    uu___9 uu___10
                                else ());
                               (uvs1, t1)))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_declare_typ env1 (uvs1, t1)
                         se2.FStarC_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([{
                              FStarC_Syntax_Syntax.sigel =
                                (FStarC_Syntax_Syntax.Sig_declare_typ
                                   {
                                     FStarC_Syntax_Syntax.lid2 = lid;
                                     FStarC_Syntax_Syntax.us2 = uvs2;
                                     FStarC_Syntax_Syntax.t2 = t2
                                   });
                              FStarC_Syntax_Syntax.sigrng =
                                (se2.FStarC_Syntax_Syntax.sigrng);
                              FStarC_Syntax_Syntax.sigquals =
                                (se2.FStarC_Syntax_Syntax.sigquals);
                              FStarC_Syntax_Syntax.sigmeta =
                                (se2.FStarC_Syntax_Syntax.sigmeta);
                              FStarC_Syntax_Syntax.sigattrs =
                                (se2.FStarC_Syntax_Syntax.sigattrs);
                              FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                              FStarC_Syntax_Syntax.sigopts =
                                (se2.FStarC_Syntax_Syntax.sigopts)
                            }], [], env0))))
           | FStarC_Syntax_Syntax.Sig_assume
               { FStarC_Syntax_Syntax.lid3 = lid;
                 FStarC_Syntax_Syntax.us3 = uvs;
                 FStarC_Syntax_Syntax.phi1 = t;_}
               ->
               (if
                  Prims.op_Negation
                    (FStarC_Compiler_List.contains
                       FStarC_Syntax_Syntax.InternalAssumption
                       se2.FStarC_Syntax_Syntax.sigquals)
                then
                  (let uu___3 =
                     let uu___4 =
                       FStarC_Class_Show.show FStarC_Ident.showable_lident
                         lid in
                     FStarC_Compiler_Util.format1
                       "Admitting a top-level assumption %s" uu___4 in
                   FStarC_Errors.log_issue
                     FStarC_Class_HasRange.hasRange_range r
                     FStarC_Errors_Codes.Warning_WarnOnUse ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___3))
                else ();
                (let env1 = FStarC_TypeChecker_Env.set_range env r in
                 let uu___3 =
                   let uu___4 = do_two_phases env1 in
                   if uu___4
                   then
                     run_phase1
                       (fun uu___5 ->
                          let uu___6 =
                            tc_assume
                              {
                                FStarC_TypeChecker_Env.solver =
                                  (env1.FStarC_TypeChecker_Env.solver);
                                FStarC_TypeChecker_Env.range =
                                  (env1.FStarC_TypeChecker_Env.range);
                                FStarC_TypeChecker_Env.curmodule =
                                  (env1.FStarC_TypeChecker_Env.curmodule);
                                FStarC_TypeChecker_Env.gamma =
                                  (env1.FStarC_TypeChecker_Env.gamma);
                                FStarC_TypeChecker_Env.gamma_sig =
                                  (env1.FStarC_TypeChecker_Env.gamma_sig);
                                FStarC_TypeChecker_Env.gamma_cache =
                                  (env1.FStarC_TypeChecker_Env.gamma_cache);
                                FStarC_TypeChecker_Env.modules =
                                  (env1.FStarC_TypeChecker_Env.modules);
                                FStarC_TypeChecker_Env.expected_typ =
                                  (env1.FStarC_TypeChecker_Env.expected_typ);
                                FStarC_TypeChecker_Env.sigtab =
                                  (env1.FStarC_TypeChecker_Env.sigtab);
                                FStarC_TypeChecker_Env.attrtab =
                                  (env1.FStarC_TypeChecker_Env.attrtab);
                                FStarC_TypeChecker_Env.instantiate_imp =
                                  (env1.FStarC_TypeChecker_Env.instantiate_imp);
                                FStarC_TypeChecker_Env.effects =
                                  (env1.FStarC_TypeChecker_Env.effects);
                                FStarC_TypeChecker_Env.generalize =
                                  (env1.FStarC_TypeChecker_Env.generalize);
                                FStarC_TypeChecker_Env.letrecs =
                                  (env1.FStarC_TypeChecker_Env.letrecs);
                                FStarC_TypeChecker_Env.top_level =
                                  (env1.FStarC_TypeChecker_Env.top_level);
                                FStarC_TypeChecker_Env.check_uvars =
                                  (env1.FStarC_TypeChecker_Env.check_uvars);
                                FStarC_TypeChecker_Env.use_eq_strict =
                                  (env1.FStarC_TypeChecker_Env.use_eq_strict);
                                FStarC_TypeChecker_Env.is_iface =
                                  (env1.FStarC_TypeChecker_Env.is_iface);
                                FStarC_TypeChecker_Env.admit = true;
                                FStarC_TypeChecker_Env.lax_universes =
                                  (env1.FStarC_TypeChecker_Env.lax_universes);
                                FStarC_TypeChecker_Env.phase1 = true;
                                FStarC_TypeChecker_Env.failhard =
                                  (env1.FStarC_TypeChecker_Env.failhard);
                                FStarC_TypeChecker_Env.flychecking =
                                  (env1.FStarC_TypeChecker_Env.flychecking);
                                FStarC_TypeChecker_Env.uvar_subtyping =
                                  (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                                FStarC_TypeChecker_Env.intactics =
                                  (env1.FStarC_TypeChecker_Env.intactics);
                                FStarC_TypeChecker_Env.nocoerce =
                                  (env1.FStarC_TypeChecker_Env.nocoerce);
                                FStarC_TypeChecker_Env.tc_term =
                                  (env1.FStarC_TypeChecker_Env.tc_term);
                                FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                  =
                                  (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                FStarC_TypeChecker_Env.universe_of =
                                  (env1.FStarC_TypeChecker_Env.universe_of);
                                FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                  =
                                  (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                FStarC_TypeChecker_Env.teq_nosmt_force =
                                  (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                                FStarC_TypeChecker_Env.subtype_nosmt_force =
                                  (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                FStarC_TypeChecker_Env.qtbl_name_and_index =
                                  (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                FStarC_TypeChecker_Env.normalized_eff_names =
                                  (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                                FStarC_TypeChecker_Env.fv_delta_depths =
                                  (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                                FStarC_TypeChecker_Env.proof_ns =
                                  (env1.FStarC_TypeChecker_Env.proof_ns);
                                FStarC_TypeChecker_Env.synth_hook =
                                  (env1.FStarC_TypeChecker_Env.synth_hook);
                                FStarC_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                FStarC_TypeChecker_Env.splice =
                                  (env1.FStarC_TypeChecker_Env.splice);
                                FStarC_TypeChecker_Env.mpreprocess =
                                  (env1.FStarC_TypeChecker_Env.mpreprocess);
                                FStarC_TypeChecker_Env.postprocess =
                                  (env1.FStarC_TypeChecker_Env.postprocess);
                                FStarC_TypeChecker_Env.identifier_info =
                                  (env1.FStarC_TypeChecker_Env.identifier_info);
                                FStarC_TypeChecker_Env.tc_hooks =
                                  (env1.FStarC_TypeChecker_Env.tc_hooks);
                                FStarC_TypeChecker_Env.dsenv =
                                  (env1.FStarC_TypeChecker_Env.dsenv);
                                FStarC_TypeChecker_Env.nbe =
                                  (env1.FStarC_TypeChecker_Env.nbe);
                                FStarC_TypeChecker_Env.strict_args_tab =
                                  (env1.FStarC_TypeChecker_Env.strict_args_tab);
                                FStarC_TypeChecker_Env.erasable_types_tab =
                                  (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                                FStarC_TypeChecker_Env.enable_defer_to_tac =
                                  (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                FStarC_TypeChecker_Env.unif_allow_ref_guards
                                  =
                                  (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                FStarC_TypeChecker_Env.erase_erasable_args =
                                  (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                                FStarC_TypeChecker_Env.core_check =
                                  (env1.FStarC_TypeChecker_Env.core_check);
                                FStarC_TypeChecker_Env.missing_decl =
                                  (env1.FStarC_TypeChecker_Env.missing_decl)
                              } (uvs, t) se2.FStarC_Syntax_Syntax.sigrng in
                          match uu___6 with
                          | (uvs1, t1) ->
                              ((let uu___8 =
                                  (FStarC_Compiler_Debug.medium ()) ||
                                    (FStarC_Compiler_Effect.op_Bang
                                       dbg_TwoPhases) in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term t1 in
                                  let uu___10 =
                                    FStarC_Class_Show.show
                                      (FStarC_Class_Show.show_list
                                         FStarC_Ident.showable_ident) uvs1 in
                                  FStarC_Compiler_Util.print2
                                    "Assume after phase 1: %s and uvs: %s\n"
                                    uu___9 uu___10
                                else ());
                               (uvs1, t1)))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_assume env1 (uvs1, t1)
                         se2.FStarC_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([{
                              FStarC_Syntax_Syntax.sigel =
                                (FStarC_Syntax_Syntax.Sig_assume
                                   {
                                     FStarC_Syntax_Syntax.lid3 = lid;
                                     FStarC_Syntax_Syntax.us3 = uvs2;
                                     FStarC_Syntax_Syntax.phi1 = t2
                                   });
                              FStarC_Syntax_Syntax.sigrng =
                                (se2.FStarC_Syntax_Syntax.sigrng);
                              FStarC_Syntax_Syntax.sigquals =
                                (se2.FStarC_Syntax_Syntax.sigquals);
                              FStarC_Syntax_Syntax.sigmeta =
                                (se2.FStarC_Syntax_Syntax.sigmeta);
                              FStarC_Syntax_Syntax.sigattrs =
                                (se2.FStarC_Syntax_Syntax.sigattrs);
                              FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                                (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                              FStarC_Syntax_Syntax.sigopts =
                                (se2.FStarC_Syntax_Syntax.sigopts)
                            }], [], env0))))
           | FStarC_Syntax_Syntax.Sig_splice
               { FStarC_Syntax_Syntax.is_typed = is_typed;
                 FStarC_Syntax_Syntax.lids2 = lids;
                 FStarC_Syntax_Syntax.tac = t;_}
               ->
               ((let uu___3 = FStarC_Compiler_Debug.any () in
                 if uu___3
                 then
                   let uu___4 =
                     FStarC_Ident.string_of_lid
                       env.FStarC_TypeChecker_Env.curmodule in
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t in
                   let uu___6 = FStarC_Compiler_Util.string_of_bool is_typed in
                   FStarC_Compiler_Util.print3
                     "%s: Found splice of (%s) with is_typed: %s\n" uu___4
                     uu___5 uu___6
                 else ());
                (let ses =
                   env.FStarC_TypeChecker_Env.splice env is_typed lids t
                     se2.FStarC_Syntax_Syntax.sigrng in
                 let ses1 =
                   if is_typed
                   then
                     let sigquals =
                       match se2.FStarC_Syntax_Syntax.sigquals with
                       | [] -> [FStarC_Syntax_Syntax.Visible_default]
                       | qs -> qs in
                     FStarC_Compiler_List.map
                       (fun sp ->
                          {
                            FStarC_Syntax_Syntax.sigel =
                              (sp.FStarC_Syntax_Syntax.sigel);
                            FStarC_Syntax_Syntax.sigrng =
                              (sp.FStarC_Syntax_Syntax.sigrng);
                            FStarC_Syntax_Syntax.sigquals =
                              (FStarC_Compiler_List.op_At sigquals
                                 sp.FStarC_Syntax_Syntax.sigquals);
                            FStarC_Syntax_Syntax.sigmeta =
                              (sp.FStarC_Syntax_Syntax.sigmeta);
                            FStarC_Syntax_Syntax.sigattrs =
                              (FStarC_Compiler_List.op_At
                                 se2.FStarC_Syntax_Syntax.sigattrs
                                 sp.FStarC_Syntax_Syntax.sigattrs);
                            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                              (sp.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                            FStarC_Syntax_Syntax.sigopts =
                              (sp.FStarC_Syntax_Syntax.sigopts)
                          }) ses
                   else ses in
                 let ses2 =
                   FStarC_Compiler_List.map
                     (fun se3 ->
                        if
                          env.FStarC_TypeChecker_Env.is_iface &&
                            (FStarC_Syntax_Syntax.uu___is_Sig_declare_typ
                               se3.FStarC_Syntax_Syntax.sigel)
                        then
                          let uu___3 =
                            let uu___4 =
                              FStarC_Compiler_List.filter
                                (fun q ->
                                   q <> FStarC_Syntax_Syntax.Irreducible)
                                se3.FStarC_Syntax_Syntax.sigquals in
                            FStarC_Syntax_Syntax.Assumption :: uu___4 in
                          {
                            FStarC_Syntax_Syntax.sigel =
                              (se3.FStarC_Syntax_Syntax.sigel);
                            FStarC_Syntax_Syntax.sigrng =
                              (se3.FStarC_Syntax_Syntax.sigrng);
                            FStarC_Syntax_Syntax.sigquals = uu___3;
                            FStarC_Syntax_Syntax.sigmeta =
                              (se3.FStarC_Syntax_Syntax.sigmeta);
                            FStarC_Syntax_Syntax.sigattrs =
                              (se3.FStarC_Syntax_Syntax.sigattrs);
                            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                              (se3.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                            FStarC_Syntax_Syntax.sigopts =
                              (se3.FStarC_Syntax_Syntax.sigopts)
                          }
                        else se3) ses1 in
                 let ses3 =
                   FStarC_Compiler_List.map
                     (fun se3 ->
                        {
                          FStarC_Syntax_Syntax.sigel =
                            (se3.FStarC_Syntax_Syntax.sigel);
                          FStarC_Syntax_Syntax.sigrng =
                            (se3.FStarC_Syntax_Syntax.sigrng);
                          FStarC_Syntax_Syntax.sigquals =
                            (se3.FStarC_Syntax_Syntax.sigquals);
                          FStarC_Syntax_Syntax.sigmeta =
                            (let uu___3 = se3.FStarC_Syntax_Syntax.sigmeta in
                             {
                               FStarC_Syntax_Syntax.sigmeta_active =
                                 (uu___3.FStarC_Syntax_Syntax.sigmeta_active);
                               FStarC_Syntax_Syntax.sigmeta_fact_db_ids =
                                 (uu___3.FStarC_Syntax_Syntax.sigmeta_fact_db_ids);
                               FStarC_Syntax_Syntax.sigmeta_admit =
                                 (uu___3.FStarC_Syntax_Syntax.sigmeta_admit);
                               FStarC_Syntax_Syntax.sigmeta_spliced = true;
                               FStarC_Syntax_Syntax.sigmeta_already_checked =
                                 (uu___3.FStarC_Syntax_Syntax.sigmeta_already_checked);
                               FStarC_Syntax_Syntax.sigmeta_extension_data =
                                 (uu___3.FStarC_Syntax_Syntax.sigmeta_extension_data)
                             });
                          FStarC_Syntax_Syntax.sigattrs =
                            (se3.FStarC_Syntax_Syntax.sigattrs);
                          FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                            (se3.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                          FStarC_Syntax_Syntax.sigopts =
                            (se3.FStarC_Syntax_Syntax.sigopts)
                        }) ses2 in
                 let dsenv =
                   FStarC_Compiler_List.fold_left
                     FStarC_Syntax_DsEnv.push_sigelt_force
                     env.FStarC_TypeChecker_Env.dsenv ses3 in
                 let env1 =
                   {
                     FStarC_TypeChecker_Env.solver =
                       (env.FStarC_TypeChecker_Env.solver);
                     FStarC_TypeChecker_Env.range =
                       (env.FStarC_TypeChecker_Env.range);
                     FStarC_TypeChecker_Env.curmodule =
                       (env.FStarC_TypeChecker_Env.curmodule);
                     FStarC_TypeChecker_Env.gamma =
                       (env.FStarC_TypeChecker_Env.gamma);
                     FStarC_TypeChecker_Env.gamma_sig =
                       (env.FStarC_TypeChecker_Env.gamma_sig);
                     FStarC_TypeChecker_Env.gamma_cache =
                       (env.FStarC_TypeChecker_Env.gamma_cache);
                     FStarC_TypeChecker_Env.modules =
                       (env.FStarC_TypeChecker_Env.modules);
                     FStarC_TypeChecker_Env.expected_typ =
                       (env.FStarC_TypeChecker_Env.expected_typ);
                     FStarC_TypeChecker_Env.sigtab =
                       (env.FStarC_TypeChecker_Env.sigtab);
                     FStarC_TypeChecker_Env.attrtab =
                       (env.FStarC_TypeChecker_Env.attrtab);
                     FStarC_TypeChecker_Env.instantiate_imp =
                       (env.FStarC_TypeChecker_Env.instantiate_imp);
                     FStarC_TypeChecker_Env.effects =
                       (env.FStarC_TypeChecker_Env.effects);
                     FStarC_TypeChecker_Env.generalize =
                       (env.FStarC_TypeChecker_Env.generalize);
                     FStarC_TypeChecker_Env.letrecs =
                       (env.FStarC_TypeChecker_Env.letrecs);
                     FStarC_TypeChecker_Env.top_level =
                       (env.FStarC_TypeChecker_Env.top_level);
                     FStarC_TypeChecker_Env.check_uvars =
                       (env.FStarC_TypeChecker_Env.check_uvars);
                     FStarC_TypeChecker_Env.use_eq_strict =
                       (env.FStarC_TypeChecker_Env.use_eq_strict);
                     FStarC_TypeChecker_Env.is_iface =
                       (env.FStarC_TypeChecker_Env.is_iface);
                     FStarC_TypeChecker_Env.admit =
                       (env.FStarC_TypeChecker_Env.admit);
                     FStarC_TypeChecker_Env.lax_universes =
                       (env.FStarC_TypeChecker_Env.lax_universes);
                     FStarC_TypeChecker_Env.phase1 =
                       (env.FStarC_TypeChecker_Env.phase1);
                     FStarC_TypeChecker_Env.failhard =
                       (env.FStarC_TypeChecker_Env.failhard);
                     FStarC_TypeChecker_Env.flychecking =
                       (env.FStarC_TypeChecker_Env.flychecking);
                     FStarC_TypeChecker_Env.uvar_subtyping =
                       (env.FStarC_TypeChecker_Env.uvar_subtyping);
                     FStarC_TypeChecker_Env.intactics =
                       (env.FStarC_TypeChecker_Env.intactics);
                     FStarC_TypeChecker_Env.nocoerce =
                       (env.FStarC_TypeChecker_Env.nocoerce);
                     FStarC_TypeChecker_Env.tc_term =
                       (env.FStarC_TypeChecker_Env.tc_term);
                     FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.universe_of =
                       (env.FStarC_TypeChecker_Env.universe_of);
                     FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.teq_nosmt_force =
                       (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                     FStarC_TypeChecker_Env.subtype_nosmt_force =
                       (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                     FStarC_TypeChecker_Env.qtbl_name_and_index =
                       (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                     FStarC_TypeChecker_Env.normalized_eff_names =
                       (env.FStarC_TypeChecker_Env.normalized_eff_names);
                     FStarC_TypeChecker_Env.fv_delta_depths =
                       (env.FStarC_TypeChecker_Env.fv_delta_depths);
                     FStarC_TypeChecker_Env.proof_ns =
                       (env.FStarC_TypeChecker_Env.proof_ns);
                     FStarC_TypeChecker_Env.synth_hook =
                       (env.FStarC_TypeChecker_Env.synth_hook);
                     FStarC_TypeChecker_Env.try_solve_implicits_hook =
                       (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                     FStarC_TypeChecker_Env.splice =
                       (env.FStarC_TypeChecker_Env.splice);
                     FStarC_TypeChecker_Env.mpreprocess =
                       (env.FStarC_TypeChecker_Env.mpreprocess);
                     FStarC_TypeChecker_Env.postprocess =
                       (env.FStarC_TypeChecker_Env.postprocess);
                     FStarC_TypeChecker_Env.identifier_info =
                       (env.FStarC_TypeChecker_Env.identifier_info);
                     FStarC_TypeChecker_Env.tc_hooks =
                       (env.FStarC_TypeChecker_Env.tc_hooks);
                     FStarC_TypeChecker_Env.dsenv = dsenv;
                     FStarC_TypeChecker_Env.nbe =
                       (env.FStarC_TypeChecker_Env.nbe);
                     FStarC_TypeChecker_Env.strict_args_tab =
                       (env.FStarC_TypeChecker_Env.strict_args_tab);
                     FStarC_TypeChecker_Env.erasable_types_tab =
                       (env.FStarC_TypeChecker_Env.erasable_types_tab);
                     FStarC_TypeChecker_Env.enable_defer_to_tac =
                       (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                     FStarC_TypeChecker_Env.unif_allow_ref_guards =
                       (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                     FStarC_TypeChecker_Env.erase_erasable_args =
                       (env.FStarC_TypeChecker_Env.erase_erasable_args);
                     FStarC_TypeChecker_Env.core_check =
                       (env.FStarC_TypeChecker_Env.core_check);
                     FStarC_TypeChecker_Env.missing_decl =
                       (env.FStarC_TypeChecker_Env.missing_decl)
                   } in
                 (let uu___4 = FStarC_Compiler_Debug.low () in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 =
                        FStarC_Compiler_List.map
                          (FStarC_Class_Show.show
                             FStarC_Syntax_Print.showable_sigelt) ses3 in
                      FStarC_Compiler_String.concat "\n" uu___6 in
                    FStarC_Compiler_Util.print1
                      "Splice returned sigelts {\n%s\n}\n" uu___5
                  else ());
                 ([], ses3, env1)))
           | FStarC_Syntax_Syntax.Sig_let
               { FStarC_Syntax_Syntax.lbs1 = lbs;
                 FStarC_Syntax_Syntax.lids1 = lids;_}
               ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_TypeChecker_Env.current_module env in
                   FStarC_Ident.string_of_lid uu___4 in
                 FStar_Pervasives_Native.Some uu___3 in
               FStarC_Profiling.profile
                 (fun uu___3 -> tc_sig_let env r se2 lbs lids) uu___2
                 "FStarC.TypeChecker.Tc.tc_sig_let"
           | FStarC_Syntax_Syntax.Sig_polymonadic_bind
               { FStarC_Syntax_Syntax.m_lid = m;
                 FStarC_Syntax_Syntax.n_lid = n;
                 FStarC_Syntax_Syntax.p_lid = p;
                 FStarC_Syntax_Syntax.tm3 = t;
                 FStarC_Syntax_Syntax.typ = uu___2;
                 FStarC_Syntax_Syntax.kind1 = uu___3;_}
               ->
               let t1 =
                 let uu___4 = do_two_phases env in
                 if uu___4
                 then
                   run_phase1
                     (fun uu___5 ->
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_TypeChecker_TcEffect.tc_polymonadic_bind
                                  {
                                    FStarC_TypeChecker_Env.solver =
                                      (env.FStarC_TypeChecker_Env.solver);
                                    FStarC_TypeChecker_Env.range =
                                      (env.FStarC_TypeChecker_Env.range);
                                    FStarC_TypeChecker_Env.curmodule =
                                      (env.FStarC_TypeChecker_Env.curmodule);
                                    FStarC_TypeChecker_Env.gamma =
                                      (env.FStarC_TypeChecker_Env.gamma);
                                    FStarC_TypeChecker_Env.gamma_sig =
                                      (env.FStarC_TypeChecker_Env.gamma_sig);
                                    FStarC_TypeChecker_Env.gamma_cache =
                                      (env.FStarC_TypeChecker_Env.gamma_cache);
                                    FStarC_TypeChecker_Env.modules =
                                      (env.FStarC_TypeChecker_Env.modules);
                                    FStarC_TypeChecker_Env.expected_typ =
                                      (env.FStarC_TypeChecker_Env.expected_typ);
                                    FStarC_TypeChecker_Env.sigtab =
                                      (env.FStarC_TypeChecker_Env.sigtab);
                                    FStarC_TypeChecker_Env.attrtab =
                                      (env.FStarC_TypeChecker_Env.attrtab);
                                    FStarC_TypeChecker_Env.instantiate_imp =
                                      (env.FStarC_TypeChecker_Env.instantiate_imp);
                                    FStarC_TypeChecker_Env.effects =
                                      (env.FStarC_TypeChecker_Env.effects);
                                    FStarC_TypeChecker_Env.generalize =
                                      (env.FStarC_TypeChecker_Env.generalize);
                                    FStarC_TypeChecker_Env.letrecs =
                                      (env.FStarC_TypeChecker_Env.letrecs);
                                    FStarC_TypeChecker_Env.top_level =
                                      (env.FStarC_TypeChecker_Env.top_level);
                                    FStarC_TypeChecker_Env.check_uvars =
                                      (env.FStarC_TypeChecker_Env.check_uvars);
                                    FStarC_TypeChecker_Env.use_eq_strict =
                                      (env.FStarC_TypeChecker_Env.use_eq_strict);
                                    FStarC_TypeChecker_Env.is_iface =
                                      (env.FStarC_TypeChecker_Env.is_iface);
                                    FStarC_TypeChecker_Env.admit = true;
                                    FStarC_TypeChecker_Env.lax_universes =
                                      (env.FStarC_TypeChecker_Env.lax_universes);
                                    FStarC_TypeChecker_Env.phase1 = true;
                                    FStarC_TypeChecker_Env.failhard =
                                      (env.FStarC_TypeChecker_Env.failhard);
                                    FStarC_TypeChecker_Env.flychecking =
                                      (env.FStarC_TypeChecker_Env.flychecking);
                                    FStarC_TypeChecker_Env.uvar_subtyping =
                                      (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                    FStarC_TypeChecker_Env.intactics =
                                      (env.FStarC_TypeChecker_Env.intactics);
                                    FStarC_TypeChecker_Env.nocoerce =
                                      (env.FStarC_TypeChecker_Env.nocoerce);
                                    FStarC_TypeChecker_Env.tc_term =
                                      (env.FStarC_TypeChecker_Env.tc_term);
                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.universe_of =
                                      (env.FStarC_TypeChecker_Env.universe_of);
                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.teq_nosmt_force =
                                      (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                    FStarC_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                    FStarC_TypeChecker_Env.fv_delta_depths =
                                      (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                    FStarC_TypeChecker_Env.proof_ns =
                                      (env.FStarC_TypeChecker_Env.proof_ns);
                                    FStarC_TypeChecker_Env.synth_hook =
                                      (env.FStarC_TypeChecker_Env.synth_hook);
                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                    FStarC_TypeChecker_Env.splice =
                                      (env.FStarC_TypeChecker_Env.splice);
                                    FStarC_TypeChecker_Env.mpreprocess =
                                      (env.FStarC_TypeChecker_Env.mpreprocess);
                                    FStarC_TypeChecker_Env.postprocess =
                                      (env.FStarC_TypeChecker_Env.postprocess);
                                    FStarC_TypeChecker_Env.identifier_info =
                                      (env.FStarC_TypeChecker_Env.identifier_info);
                                    FStarC_TypeChecker_Env.tc_hooks =
                                      (env.FStarC_TypeChecker_Env.tc_hooks);
                                    FStarC_TypeChecker_Env.dsenv =
                                      (env.FStarC_TypeChecker_Env.dsenv);
                                    FStarC_TypeChecker_Env.nbe =
                                      (env.FStarC_TypeChecker_Env.nbe);
                                    FStarC_TypeChecker_Env.strict_args_tab =
                                      (env.FStarC_TypeChecker_Env.strict_args_tab);
                                    FStarC_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                    FStarC_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                    FStarC_TypeChecker_Env.core_check =
                                      (env.FStarC_TypeChecker_Env.core_check);
                                    FStarC_TypeChecker_Env.missing_decl =
                                      (env.FStarC_TypeChecker_Env.missing_decl)
                                  } m n p t in
                              match uu___9 with
                              | (t2, ty, uu___10) ->
                                  {
                                    FStarC_Syntax_Syntax.sigel =
                                      (FStarC_Syntax_Syntax.Sig_polymonadic_bind
                                         {
                                           FStarC_Syntax_Syntax.m_lid = m;
                                           FStarC_Syntax_Syntax.n_lid = n;
                                           FStarC_Syntax_Syntax.p_lid = p;
                                           FStarC_Syntax_Syntax.tm3 = t2;
                                           FStarC_Syntax_Syntax.typ = ty;
                                           FStarC_Syntax_Syntax.kind1 =
                                             FStar_Pervasives_Native.None
                                         });
                                    FStarC_Syntax_Syntax.sigrng =
                                      (se2.FStarC_Syntax_Syntax.sigrng);
                                    FStarC_Syntax_Syntax.sigquals =
                                      (se2.FStarC_Syntax_Syntax.sigquals);
                                    FStarC_Syntax_Syntax.sigmeta =
                                      (se2.FStarC_Syntax_Syntax.sigmeta);
                                    FStarC_Syntax_Syntax.sigattrs =
                                      (se2.FStarC_Syntax_Syntax.sigattrs);
                                    FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                      =
                                      (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                    FStarC_Syntax_Syntax.sigopts =
                                      (se2.FStarC_Syntax_Syntax.sigopts)
                                  } in
                            FStarC_TypeChecker_Normalize.elim_uvars env
                              uu___8 in
                          match uu___7.FStarC_Syntax_Syntax.sigel with
                          | FStarC_Syntax_Syntax.Sig_polymonadic_bind
                              { FStarC_Syntax_Syntax.m_lid = uu___8;
                                FStarC_Syntax_Syntax.n_lid = uu___9;
                                FStarC_Syntax_Syntax.p_lid = uu___10;
                                FStarC_Syntax_Syntax.tm3 = t2;
                                FStarC_Syntax_Syntax.typ = ty;
                                FStarC_Syntax_Syntax.kind1 = uu___11;_}
                              -> (t2, ty)
                          | uu___8 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind" in
                        match uu___6 with
                        | (t2, ty) ->
                            ((let uu___8 =
                                (FStarC_Compiler_Debug.medium ()) ||
                                  (FStarC_Compiler_Effect.op_Bang
                                     dbg_TwoPhases) in
                              if uu___8
                              then
                                let uu___9 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_sigelt
                                    {
                                      FStarC_Syntax_Syntax.sigel =
                                        (FStarC_Syntax_Syntax.Sig_polymonadic_bind
                                           {
                                             FStarC_Syntax_Syntax.m_lid = m;
                                             FStarC_Syntax_Syntax.n_lid = n;
                                             FStarC_Syntax_Syntax.p_lid = p;
                                             FStarC_Syntax_Syntax.tm3 = t2;
                                             FStarC_Syntax_Syntax.typ = ty;
                                             FStarC_Syntax_Syntax.kind1 =
                                               FStar_Pervasives_Native.None
                                           });
                                      FStarC_Syntax_Syntax.sigrng =
                                        (se2.FStarC_Syntax_Syntax.sigrng);
                                      FStarC_Syntax_Syntax.sigquals =
                                        (se2.FStarC_Syntax_Syntax.sigquals);
                                      FStarC_Syntax_Syntax.sigmeta =
                                        (se2.FStarC_Syntax_Syntax.sigmeta);
                                      FStarC_Syntax_Syntax.sigattrs =
                                        (se2.FStarC_Syntax_Syntax.sigattrs);
                                      FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                        =
                                        (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                      FStarC_Syntax_Syntax.sigopts =
                                        (se2.FStarC_Syntax_Syntax.sigopts)
                                    } in
                                FStarC_Compiler_Util.print1
                                  "Polymonadic bind after phase 1: %s\n"
                                  uu___9
                              else ());
                             t2))
                 else t in
               let uu___4 =
                 FStarC_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu___4 with
                | (t2, ty, k) ->
                    let se3 =
                      {
                        FStarC_Syntax_Syntax.sigel =
                          (FStarC_Syntax_Syntax.Sig_polymonadic_bind
                             {
                               FStarC_Syntax_Syntax.m_lid = m;
                               FStarC_Syntax_Syntax.n_lid = n;
                               FStarC_Syntax_Syntax.p_lid = p;
                               FStarC_Syntax_Syntax.tm3 = t2;
                               FStarC_Syntax_Syntax.typ = ty;
                               FStarC_Syntax_Syntax.kind1 =
                                 (FStar_Pervasives_Native.Some k)
                             });
                        FStarC_Syntax_Syntax.sigrng =
                          (se2.FStarC_Syntax_Syntax.sigrng);
                        FStarC_Syntax_Syntax.sigquals =
                          (se2.FStarC_Syntax_Syntax.sigquals);
                        FStarC_Syntax_Syntax.sigmeta =
                          (se2.FStarC_Syntax_Syntax.sigmeta);
                        FStarC_Syntax_Syntax.sigattrs =
                          (se2.FStarC_Syntax_Syntax.sigattrs);
                        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                          (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                        FStarC_Syntax_Syntax.sigopts =
                          (se2.FStarC_Syntax_Syntax.sigopts)
                      } in
                    ([se3], [], env0))
           | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
               { FStarC_Syntax_Syntax.m_lid1 = m;
                 FStarC_Syntax_Syntax.n_lid1 = n;
                 FStarC_Syntax_Syntax.tm4 = t;
                 FStarC_Syntax_Syntax.typ1 = uu___2;
                 FStarC_Syntax_Syntax.kind2 = uu___3;_}
               ->
               let t1 =
                 let uu___4 = do_two_phases env in
                 if uu___4
                 then
                   run_phase1
                     (fun uu___5 ->
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_TypeChecker_TcEffect.tc_polymonadic_subcomp
                                  {
                                    FStarC_TypeChecker_Env.solver =
                                      (env.FStarC_TypeChecker_Env.solver);
                                    FStarC_TypeChecker_Env.range =
                                      (env.FStarC_TypeChecker_Env.range);
                                    FStarC_TypeChecker_Env.curmodule =
                                      (env.FStarC_TypeChecker_Env.curmodule);
                                    FStarC_TypeChecker_Env.gamma =
                                      (env.FStarC_TypeChecker_Env.gamma);
                                    FStarC_TypeChecker_Env.gamma_sig =
                                      (env.FStarC_TypeChecker_Env.gamma_sig);
                                    FStarC_TypeChecker_Env.gamma_cache =
                                      (env.FStarC_TypeChecker_Env.gamma_cache);
                                    FStarC_TypeChecker_Env.modules =
                                      (env.FStarC_TypeChecker_Env.modules);
                                    FStarC_TypeChecker_Env.expected_typ =
                                      (env.FStarC_TypeChecker_Env.expected_typ);
                                    FStarC_TypeChecker_Env.sigtab =
                                      (env.FStarC_TypeChecker_Env.sigtab);
                                    FStarC_TypeChecker_Env.attrtab =
                                      (env.FStarC_TypeChecker_Env.attrtab);
                                    FStarC_TypeChecker_Env.instantiate_imp =
                                      (env.FStarC_TypeChecker_Env.instantiate_imp);
                                    FStarC_TypeChecker_Env.effects =
                                      (env.FStarC_TypeChecker_Env.effects);
                                    FStarC_TypeChecker_Env.generalize =
                                      (env.FStarC_TypeChecker_Env.generalize);
                                    FStarC_TypeChecker_Env.letrecs =
                                      (env.FStarC_TypeChecker_Env.letrecs);
                                    FStarC_TypeChecker_Env.top_level =
                                      (env.FStarC_TypeChecker_Env.top_level);
                                    FStarC_TypeChecker_Env.check_uvars =
                                      (env.FStarC_TypeChecker_Env.check_uvars);
                                    FStarC_TypeChecker_Env.use_eq_strict =
                                      (env.FStarC_TypeChecker_Env.use_eq_strict);
                                    FStarC_TypeChecker_Env.is_iface =
                                      (env.FStarC_TypeChecker_Env.is_iface);
                                    FStarC_TypeChecker_Env.admit = true;
                                    FStarC_TypeChecker_Env.lax_universes =
                                      (env.FStarC_TypeChecker_Env.lax_universes);
                                    FStarC_TypeChecker_Env.phase1 = true;
                                    FStarC_TypeChecker_Env.failhard =
                                      (env.FStarC_TypeChecker_Env.failhard);
                                    FStarC_TypeChecker_Env.flychecking =
                                      (env.FStarC_TypeChecker_Env.flychecking);
                                    FStarC_TypeChecker_Env.uvar_subtyping =
                                      (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                    FStarC_TypeChecker_Env.intactics =
                                      (env.FStarC_TypeChecker_Env.intactics);
                                    FStarC_TypeChecker_Env.nocoerce =
                                      (env.FStarC_TypeChecker_Env.nocoerce);
                                    FStarC_TypeChecker_Env.tc_term =
                                      (env.FStarC_TypeChecker_Env.tc_term);
                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.universe_of =
                                      (env.FStarC_TypeChecker_Env.universe_of);
                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStarC_TypeChecker_Env.teq_nosmt_force =
                                      (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                    FStarC_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                    FStarC_TypeChecker_Env.fv_delta_depths =
                                      (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                    FStarC_TypeChecker_Env.proof_ns =
                                      (env.FStarC_TypeChecker_Env.proof_ns);
                                    FStarC_TypeChecker_Env.synth_hook =
                                      (env.FStarC_TypeChecker_Env.synth_hook);
                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                    FStarC_TypeChecker_Env.splice =
                                      (env.FStarC_TypeChecker_Env.splice);
                                    FStarC_TypeChecker_Env.mpreprocess =
                                      (env.FStarC_TypeChecker_Env.mpreprocess);
                                    FStarC_TypeChecker_Env.postprocess =
                                      (env.FStarC_TypeChecker_Env.postprocess);
                                    FStarC_TypeChecker_Env.identifier_info =
                                      (env.FStarC_TypeChecker_Env.identifier_info);
                                    FStarC_TypeChecker_Env.tc_hooks =
                                      (env.FStarC_TypeChecker_Env.tc_hooks);
                                    FStarC_TypeChecker_Env.dsenv =
                                      (env.FStarC_TypeChecker_Env.dsenv);
                                    FStarC_TypeChecker_Env.nbe =
                                      (env.FStarC_TypeChecker_Env.nbe);
                                    FStarC_TypeChecker_Env.strict_args_tab =
                                      (env.FStarC_TypeChecker_Env.strict_args_tab);
                                    FStarC_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                    FStarC_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                    FStarC_TypeChecker_Env.core_check =
                                      (env.FStarC_TypeChecker_Env.core_check);
                                    FStarC_TypeChecker_Env.missing_decl =
                                      (env.FStarC_TypeChecker_Env.missing_decl)
                                  } m n t in
                              match uu___9 with
                              | (t2, ty, uu___10) ->
                                  {
                                    FStarC_Syntax_Syntax.sigel =
                                      (FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                                         {
                                           FStarC_Syntax_Syntax.m_lid1 = m;
                                           FStarC_Syntax_Syntax.n_lid1 = n;
                                           FStarC_Syntax_Syntax.tm4 = t2;
                                           FStarC_Syntax_Syntax.typ1 = ty;
                                           FStarC_Syntax_Syntax.kind2 =
                                             FStar_Pervasives_Native.None
                                         });
                                    FStarC_Syntax_Syntax.sigrng =
                                      (se2.FStarC_Syntax_Syntax.sigrng);
                                    FStarC_Syntax_Syntax.sigquals =
                                      (se2.FStarC_Syntax_Syntax.sigquals);
                                    FStarC_Syntax_Syntax.sigmeta =
                                      (se2.FStarC_Syntax_Syntax.sigmeta);
                                    FStarC_Syntax_Syntax.sigattrs =
                                      (se2.FStarC_Syntax_Syntax.sigattrs);
                                    FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                      =
                                      (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                    FStarC_Syntax_Syntax.sigopts =
                                      (se2.FStarC_Syntax_Syntax.sigopts)
                                  } in
                            FStarC_TypeChecker_Normalize.elim_uvars env
                              uu___8 in
                          match uu___7.FStarC_Syntax_Syntax.sigel with
                          | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                              { FStarC_Syntax_Syntax.m_lid1 = uu___8;
                                FStarC_Syntax_Syntax.n_lid1 = uu___9;
                                FStarC_Syntax_Syntax.tm4 = t2;
                                FStarC_Syntax_Syntax.typ1 = ty;
                                FStarC_Syntax_Syntax.kind2 = uu___10;_}
                              -> (t2, ty)
                          | uu___8 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp" in
                        match uu___6 with
                        | (t2, ty) ->
                            ((let uu___8 =
                                (FStarC_Compiler_Debug.medium ()) ||
                                  (FStarC_Compiler_Effect.op_Bang
                                     dbg_TwoPhases) in
                              if uu___8
                              then
                                let uu___9 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_sigelt
                                    {
                                      FStarC_Syntax_Syntax.sigel =
                                        (FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                                           {
                                             FStarC_Syntax_Syntax.m_lid1 = m;
                                             FStarC_Syntax_Syntax.n_lid1 = n;
                                             FStarC_Syntax_Syntax.tm4 = t2;
                                             FStarC_Syntax_Syntax.typ1 = ty;
                                             FStarC_Syntax_Syntax.kind2 =
                                               FStar_Pervasives_Native.None
                                           });
                                      FStarC_Syntax_Syntax.sigrng =
                                        (se2.FStarC_Syntax_Syntax.sigrng);
                                      FStarC_Syntax_Syntax.sigquals =
                                        (se2.FStarC_Syntax_Syntax.sigquals);
                                      FStarC_Syntax_Syntax.sigmeta =
                                        (se2.FStarC_Syntax_Syntax.sigmeta);
                                      FStarC_Syntax_Syntax.sigattrs =
                                        (se2.FStarC_Syntax_Syntax.sigattrs);
                                      FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                        =
                                        (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                      FStarC_Syntax_Syntax.sigopts =
                                        (se2.FStarC_Syntax_Syntax.sigopts)
                                    } in
                                FStarC_Compiler_Util.print1
                                  "Polymonadic subcomp after phase 1: %s\n"
                                  uu___9
                              else ());
                             t2))
                 else t in
               let uu___4 =
                 FStarC_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n
                   t1 in
               (match uu___4 with
                | (t2, ty, k) ->
                    let se3 =
                      {
                        FStarC_Syntax_Syntax.sigel =
                          (FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                             {
                               FStarC_Syntax_Syntax.m_lid1 = m;
                               FStarC_Syntax_Syntax.n_lid1 = n;
                               FStarC_Syntax_Syntax.tm4 = t2;
                               FStarC_Syntax_Syntax.typ1 = ty;
                               FStarC_Syntax_Syntax.kind2 =
                                 (FStar_Pervasives_Native.Some k)
                             });
                        FStarC_Syntax_Syntax.sigrng =
                          (se2.FStarC_Syntax_Syntax.sigrng);
                        FStarC_Syntax_Syntax.sigquals =
                          (se2.FStarC_Syntax_Syntax.sigquals);
                        FStarC_Syntax_Syntax.sigmeta =
                          (se2.FStarC_Syntax_Syntax.sigmeta);
                        FStarC_Syntax_Syntax.sigattrs =
                          (se2.FStarC_Syntax_Syntax.sigattrs);
                        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                          (se2.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                        FStarC_Syntax_Syntax.sigopts =
                          (se2.FStarC_Syntax_Syntax.sigopts)
                      } in
                    ([se3], [], env0)))
let (tc_decl :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt ->
      (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_Syntax_Syntax.sigelt
        Prims.list * FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun se ->
      FStarC_GenSym.reset_gensym ();
      (let env0 = env in
       let env1 = set_hint_correlator env se in
       let env2 =
         let uu___1 = FStarC_Options.admit_smt_queries () in
         if uu___1
         then
           {
             FStarC_TypeChecker_Env.solver =
               (env1.FStarC_TypeChecker_Env.solver);
             FStarC_TypeChecker_Env.range =
               (env1.FStarC_TypeChecker_Env.range);
             FStarC_TypeChecker_Env.curmodule =
               (env1.FStarC_TypeChecker_Env.curmodule);
             FStarC_TypeChecker_Env.gamma =
               (env1.FStarC_TypeChecker_Env.gamma);
             FStarC_TypeChecker_Env.gamma_sig =
               (env1.FStarC_TypeChecker_Env.gamma_sig);
             FStarC_TypeChecker_Env.gamma_cache =
               (env1.FStarC_TypeChecker_Env.gamma_cache);
             FStarC_TypeChecker_Env.modules =
               (env1.FStarC_TypeChecker_Env.modules);
             FStarC_TypeChecker_Env.expected_typ =
               (env1.FStarC_TypeChecker_Env.expected_typ);
             FStarC_TypeChecker_Env.sigtab =
               (env1.FStarC_TypeChecker_Env.sigtab);
             FStarC_TypeChecker_Env.attrtab =
               (env1.FStarC_TypeChecker_Env.attrtab);
             FStarC_TypeChecker_Env.instantiate_imp =
               (env1.FStarC_TypeChecker_Env.instantiate_imp);
             FStarC_TypeChecker_Env.effects =
               (env1.FStarC_TypeChecker_Env.effects);
             FStarC_TypeChecker_Env.generalize =
               (env1.FStarC_TypeChecker_Env.generalize);
             FStarC_TypeChecker_Env.letrecs =
               (env1.FStarC_TypeChecker_Env.letrecs);
             FStarC_TypeChecker_Env.top_level =
               (env1.FStarC_TypeChecker_Env.top_level);
             FStarC_TypeChecker_Env.check_uvars =
               (env1.FStarC_TypeChecker_Env.check_uvars);
             FStarC_TypeChecker_Env.use_eq_strict =
               (env1.FStarC_TypeChecker_Env.use_eq_strict);
             FStarC_TypeChecker_Env.is_iface =
               (env1.FStarC_TypeChecker_Env.is_iface);
             FStarC_TypeChecker_Env.admit = true;
             FStarC_TypeChecker_Env.lax_universes =
               (env1.FStarC_TypeChecker_Env.lax_universes);
             FStarC_TypeChecker_Env.phase1 =
               (env1.FStarC_TypeChecker_Env.phase1);
             FStarC_TypeChecker_Env.failhard =
               (env1.FStarC_TypeChecker_Env.failhard);
             FStarC_TypeChecker_Env.flychecking =
               (env1.FStarC_TypeChecker_Env.flychecking);
             FStarC_TypeChecker_Env.uvar_subtyping =
               (env1.FStarC_TypeChecker_Env.uvar_subtyping);
             FStarC_TypeChecker_Env.intactics =
               (env1.FStarC_TypeChecker_Env.intactics);
             FStarC_TypeChecker_Env.nocoerce =
               (env1.FStarC_TypeChecker_Env.nocoerce);
             FStarC_TypeChecker_Env.tc_term =
               (env1.FStarC_TypeChecker_Env.tc_term);
             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
               (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
             FStarC_TypeChecker_Env.universe_of =
               (env1.FStarC_TypeChecker_Env.universe_of);
             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
               (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
             FStarC_TypeChecker_Env.teq_nosmt_force =
               (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
             FStarC_TypeChecker_Env.subtype_nosmt_force =
               (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
             FStarC_TypeChecker_Env.qtbl_name_and_index =
               (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
             FStarC_TypeChecker_Env.normalized_eff_names =
               (env1.FStarC_TypeChecker_Env.normalized_eff_names);
             FStarC_TypeChecker_Env.fv_delta_depths =
               (env1.FStarC_TypeChecker_Env.fv_delta_depths);
             FStarC_TypeChecker_Env.proof_ns =
               (env1.FStarC_TypeChecker_Env.proof_ns);
             FStarC_TypeChecker_Env.synth_hook =
               (env1.FStarC_TypeChecker_Env.synth_hook);
             FStarC_TypeChecker_Env.try_solve_implicits_hook =
               (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
             FStarC_TypeChecker_Env.splice =
               (env1.FStarC_TypeChecker_Env.splice);
             FStarC_TypeChecker_Env.mpreprocess =
               (env1.FStarC_TypeChecker_Env.mpreprocess);
             FStarC_TypeChecker_Env.postprocess =
               (env1.FStarC_TypeChecker_Env.postprocess);
             FStarC_TypeChecker_Env.identifier_info =
               (env1.FStarC_TypeChecker_Env.identifier_info);
             FStarC_TypeChecker_Env.tc_hooks =
               (env1.FStarC_TypeChecker_Env.tc_hooks);
             FStarC_TypeChecker_Env.dsenv =
               (env1.FStarC_TypeChecker_Env.dsenv);
             FStarC_TypeChecker_Env.nbe = (env1.FStarC_TypeChecker_Env.nbe);
             FStarC_TypeChecker_Env.strict_args_tab =
               (env1.FStarC_TypeChecker_Env.strict_args_tab);
             FStarC_TypeChecker_Env.erasable_types_tab =
               (env1.FStarC_TypeChecker_Env.erasable_types_tab);
             FStarC_TypeChecker_Env.enable_defer_to_tac =
               (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
             FStarC_TypeChecker_Env.unif_allow_ref_guards =
               (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
             FStarC_TypeChecker_Env.erase_erasable_args =
               (env1.FStarC_TypeChecker_Env.erase_erasable_args);
             FStarC_TypeChecker_Env.core_check =
               (env1.FStarC_TypeChecker_Env.core_check);
             FStarC_TypeChecker_Env.missing_decl =
               (env1.FStarC_TypeChecker_Env.missing_decl)
           }
         else env1 in
       (let uu___2 = FStarC_Compiler_Debug.any () in
        if uu___2
        then
          let uu___3 = FStarC_Syntax_Print.sigelt_to_string_short se in
          FStarC_Compiler_Util.print1 "Processing %s\n" uu___3
        else ());
       (let uu___3 = FStarC_Compiler_Debug.medium () in
        if uu___3
        then
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_bool
              env2.FStarC_TypeChecker_Env.admit in
          let uu___5 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt se in
          FStarC_Compiler_Util.print2 ">>>>>>>>>>>>>>tc_decl admit=%s %s\n"
            uu___4 uu___5
        else ());
       (let result =
          if
            (se.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_already_checked
          then ([se], [], env2)
          else
            if
              (se.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_admit
            then
              (let result1 =
                 tc_decl'
                   {
                     FStarC_TypeChecker_Env.solver =
                       (env2.FStarC_TypeChecker_Env.solver);
                     FStarC_TypeChecker_Env.range =
                       (env2.FStarC_TypeChecker_Env.range);
                     FStarC_TypeChecker_Env.curmodule =
                       (env2.FStarC_TypeChecker_Env.curmodule);
                     FStarC_TypeChecker_Env.gamma =
                       (env2.FStarC_TypeChecker_Env.gamma);
                     FStarC_TypeChecker_Env.gamma_sig =
                       (env2.FStarC_TypeChecker_Env.gamma_sig);
                     FStarC_TypeChecker_Env.gamma_cache =
                       (env2.FStarC_TypeChecker_Env.gamma_cache);
                     FStarC_TypeChecker_Env.modules =
                       (env2.FStarC_TypeChecker_Env.modules);
                     FStarC_TypeChecker_Env.expected_typ =
                       (env2.FStarC_TypeChecker_Env.expected_typ);
                     FStarC_TypeChecker_Env.sigtab =
                       (env2.FStarC_TypeChecker_Env.sigtab);
                     FStarC_TypeChecker_Env.attrtab =
                       (env2.FStarC_TypeChecker_Env.attrtab);
                     FStarC_TypeChecker_Env.instantiate_imp =
                       (env2.FStarC_TypeChecker_Env.instantiate_imp);
                     FStarC_TypeChecker_Env.effects =
                       (env2.FStarC_TypeChecker_Env.effects);
                     FStarC_TypeChecker_Env.generalize =
                       (env2.FStarC_TypeChecker_Env.generalize);
                     FStarC_TypeChecker_Env.letrecs =
                       (env2.FStarC_TypeChecker_Env.letrecs);
                     FStarC_TypeChecker_Env.top_level =
                       (env2.FStarC_TypeChecker_Env.top_level);
                     FStarC_TypeChecker_Env.check_uvars =
                       (env2.FStarC_TypeChecker_Env.check_uvars);
                     FStarC_TypeChecker_Env.use_eq_strict =
                       (env2.FStarC_TypeChecker_Env.use_eq_strict);
                     FStarC_TypeChecker_Env.is_iface =
                       (env2.FStarC_TypeChecker_Env.is_iface);
                     FStarC_TypeChecker_Env.admit = true;
                     FStarC_TypeChecker_Env.lax_universes =
                       (env2.FStarC_TypeChecker_Env.lax_universes);
                     FStarC_TypeChecker_Env.phase1 =
                       (env2.FStarC_TypeChecker_Env.phase1);
                     FStarC_TypeChecker_Env.failhard =
                       (env2.FStarC_TypeChecker_Env.failhard);
                     FStarC_TypeChecker_Env.flychecking =
                       (env2.FStarC_TypeChecker_Env.flychecking);
                     FStarC_TypeChecker_Env.uvar_subtyping =
                       (env2.FStarC_TypeChecker_Env.uvar_subtyping);
                     FStarC_TypeChecker_Env.intactics =
                       (env2.FStarC_TypeChecker_Env.intactics);
                     FStarC_TypeChecker_Env.nocoerce =
                       (env2.FStarC_TypeChecker_Env.nocoerce);
                     FStarC_TypeChecker_Env.tc_term =
                       (env2.FStarC_TypeChecker_Env.tc_term);
                     FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.universe_of =
                       (env2.FStarC_TypeChecker_Env.universe_of);
                     FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStarC_TypeChecker_Env.teq_nosmt_force =
                       (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
                     FStarC_TypeChecker_Env.subtype_nosmt_force =
                       (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                     FStarC_TypeChecker_Env.qtbl_name_and_index =
                       (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                     FStarC_TypeChecker_Env.normalized_eff_names =
                       (env2.FStarC_TypeChecker_Env.normalized_eff_names);
                     FStarC_TypeChecker_Env.fv_delta_depths =
                       (env2.FStarC_TypeChecker_Env.fv_delta_depths);
                     FStarC_TypeChecker_Env.proof_ns =
                       (env2.FStarC_TypeChecker_Env.proof_ns);
                     FStarC_TypeChecker_Env.synth_hook =
                       (env2.FStarC_TypeChecker_Env.synth_hook);
                     FStarC_TypeChecker_Env.try_solve_implicits_hook =
                       (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                     FStarC_TypeChecker_Env.splice =
                       (env2.FStarC_TypeChecker_Env.splice);
                     FStarC_TypeChecker_Env.mpreprocess =
                       (env2.FStarC_TypeChecker_Env.mpreprocess);
                     FStarC_TypeChecker_Env.postprocess =
                       (env2.FStarC_TypeChecker_Env.postprocess);
                     FStarC_TypeChecker_Env.identifier_info =
                       (env2.FStarC_TypeChecker_Env.identifier_info);
                     FStarC_TypeChecker_Env.tc_hooks =
                       (env2.FStarC_TypeChecker_Env.tc_hooks);
                     FStarC_TypeChecker_Env.dsenv =
                       (env2.FStarC_TypeChecker_Env.dsenv);
                     FStarC_TypeChecker_Env.nbe =
                       (env2.FStarC_TypeChecker_Env.nbe);
                     FStarC_TypeChecker_Env.strict_args_tab =
                       (env2.FStarC_TypeChecker_Env.strict_args_tab);
                     FStarC_TypeChecker_Env.erasable_types_tab =
                       (env2.FStarC_TypeChecker_Env.erasable_types_tab);
                     FStarC_TypeChecker_Env.enable_defer_to_tac =
                       (env2.FStarC_TypeChecker_Env.enable_defer_to_tac);
                     FStarC_TypeChecker_Env.unif_allow_ref_guards =
                       (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                     FStarC_TypeChecker_Env.erase_erasable_args =
                       (env2.FStarC_TypeChecker_Env.erase_erasable_args);
                     FStarC_TypeChecker_Env.core_check =
                       (env2.FStarC_TypeChecker_Env.core_check);
                     FStarC_TypeChecker_Env.missing_decl =
                       (env2.FStarC_TypeChecker_Env.missing_decl)
                   } se in
               result1)
            else tc_decl' env2 se in
        (let uu___4 = result in
         match uu___4 with
         | (ses, uu___5, uu___6) ->
             FStarC_Compiler_List.iter
               (FStarC_TypeChecker_Quals.check_sigelt_quals_post env2) ses);
        (match () with
         | () ->
             let result1 =
               let uu___4 = result in
               match uu___4 with
               | (ses, ses_e, env3) ->
                   (ses, ses_e,
                     {
                       FStarC_TypeChecker_Env.solver =
                         (env3.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (env3.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (env3.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (env3.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (env3.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (env3.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (env3.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (env3.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (env3.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (env3.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (env3.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (env3.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (env3.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (env3.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (env3.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (env3.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (env3.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (env3.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (env0.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (env3.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (env3.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (env3.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (env3.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (env3.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (env3.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (env3.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (env3.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env3.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (env3.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env3.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (env3.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (env3.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (env3.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (env3.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (env3.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns =
                         (env3.FStarC_TypeChecker_Env.proof_ns);
                       FStarC_TypeChecker_Env.synth_hook =
                         (env3.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (env3.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (env3.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (env3.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (env3.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (env3.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (env3.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (env3.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (env3.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (env3.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (env3.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (env3.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (env3.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (env3.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (env3.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (env3.FStarC_TypeChecker_Env.missing_decl)
                     }) in
             result1)))
let (add_sigelt_to_env :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt -> Prims.bool -> FStarC_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      fun from_cache ->
        (let uu___1 = FStarC_Compiler_Debug.low () in
         if uu___1
         then
           let uu___2 = FStarC_Syntax_Print.sigelt_to_string_short se in
           let uu___3 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_bool
               from_cache in
           FStarC_Compiler_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu___2 uu___3
         else ());
        (match se.FStarC_Syntax_Syntax.sigel with
         | FStarC_Syntax_Syntax.Sig_inductive_typ uu___1 ->
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt
                   se in
               FStarC_Compiler_Util.format1
                 "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                 uu___3 in
             FStarC_Errors.raise_error FStarC_Syntax_Syntax.has_range_sigelt
               se FStarC_Errors_Codes.Fatal_UnexpectedInductivetype ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___2)
         | FStarC_Syntax_Syntax.Sig_datacon uu___1 ->
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt
                   se in
               FStarC_Compiler_Util.format1
                 "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                 uu___3 in
             FStarC_Errors.raise_error FStarC_Syntax_Syntax.has_range_sigelt
               se FStarC_Errors_Codes.Fatal_UnexpectedInductivetype ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___2)
         | FStarC_Syntax_Syntax.Sig_declare_typ uu___1 when
             FStarC_Compiler_Util.for_some
               (fun uu___2 ->
                  match uu___2 with
                  | FStarC_Syntax_Syntax.OnlyName -> true
                  | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals
             -> env
         | FStarC_Syntax_Syntax.Sig_let uu___1 when
             FStarC_Compiler_Util.for_some
               (fun uu___2 ->
                  match uu___2 with
                  | FStarC_Syntax_Syntax.OnlyName -> true
                  | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals
             -> env
         | uu___1 ->
             let env1 = FStarC_TypeChecker_Env.push_sigelt env se in
             (match se.FStarC_Syntax_Syntax.sigel with
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.ShowOptions) ->
                  ((let uu___3 =
                      let uu___4 = FStarC_Errors_Msg.text "Option state:" in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStarC_Options.show_options () in
                          FStarC_Pprint.arbitrary_string uu___7 in
                        [uu___6] in
                      uu___4 :: uu___5 in
                    FStarC_Errors.info FStarC_Syntax_Syntax.has_range_sigelt
                      se ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                      (Obj.magic uu___3));
                   env1)
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.PushOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStarC_Options.using_facts_from () in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (env1.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (env1.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (env1.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (env1.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (env1.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (env1.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (env1.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (env1.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (env1.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (env1.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (env1.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (env1.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (env1.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (env1.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (env1.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (env1.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (env1.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (env1.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (env1.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (env1.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (env1.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (env1.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (env1.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (env1.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (env1.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (env1.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (env1.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns = uu___4;
                       FStarC_TypeChecker_Env.synth_hook =
                         (env1.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (env1.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (env1.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (env1.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (env1.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (env1.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (env1.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (env1.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (env1.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (env1.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (env1.FStarC_TypeChecker_Env.missing_decl)
                     })
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___3 = FStarC_Options.using_facts_from () in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (env1.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (env1.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (env1.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (env1.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (env1.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (env1.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (env1.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (env1.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (env1.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (env1.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (env1.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (env1.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (env1.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (env1.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (env1.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (env1.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (env1.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (env1.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (env1.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (env1.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (env1.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (env1.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (env1.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (env1.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (env1.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (env1.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (env1.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns = uu___3;
                       FStarC_TypeChecker_Env.synth_hook =
                         (env1.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (env1.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (env1.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (env1.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (env1.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (env1.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (env1.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (env1.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (env1.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (env1.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (env1.FStarC_TypeChecker_Env.missing_decl)
                     })
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.SetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStarC_Options.using_facts_from () in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (env1.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (env1.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (env1.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (env1.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (env1.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (env1.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (env1.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (env1.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (env1.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (env1.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (env1.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (env1.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (env1.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (env1.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (env1.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (env1.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (env1.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (env1.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (env1.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (env1.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (env1.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (env1.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (env1.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (env1.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (env1.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (env1.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (env1.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns = uu___4;
                       FStarC_TypeChecker_Env.synth_hook =
                         (env1.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (env1.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (env1.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (env1.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (env1.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (env1.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (env1.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (env1.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (env1.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (env1.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (env1.FStarC_TypeChecker_Env.missing_decl)
                     })
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.ResetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStarC_Options.using_facts_from () in
                     {
                       FStarC_TypeChecker_Env.solver =
                         (env1.FStarC_TypeChecker_Env.solver);
                       FStarC_TypeChecker_Env.range =
                         (env1.FStarC_TypeChecker_Env.range);
                       FStarC_TypeChecker_Env.curmodule =
                         (env1.FStarC_TypeChecker_Env.curmodule);
                       FStarC_TypeChecker_Env.gamma =
                         (env1.FStarC_TypeChecker_Env.gamma);
                       FStarC_TypeChecker_Env.gamma_sig =
                         (env1.FStarC_TypeChecker_Env.gamma_sig);
                       FStarC_TypeChecker_Env.gamma_cache =
                         (env1.FStarC_TypeChecker_Env.gamma_cache);
                       FStarC_TypeChecker_Env.modules =
                         (env1.FStarC_TypeChecker_Env.modules);
                       FStarC_TypeChecker_Env.expected_typ =
                         (env1.FStarC_TypeChecker_Env.expected_typ);
                       FStarC_TypeChecker_Env.sigtab =
                         (env1.FStarC_TypeChecker_Env.sigtab);
                       FStarC_TypeChecker_Env.attrtab =
                         (env1.FStarC_TypeChecker_Env.attrtab);
                       FStarC_TypeChecker_Env.instantiate_imp =
                         (env1.FStarC_TypeChecker_Env.instantiate_imp);
                       FStarC_TypeChecker_Env.effects =
                         (env1.FStarC_TypeChecker_Env.effects);
                       FStarC_TypeChecker_Env.generalize =
                         (env1.FStarC_TypeChecker_Env.generalize);
                       FStarC_TypeChecker_Env.letrecs =
                         (env1.FStarC_TypeChecker_Env.letrecs);
                       FStarC_TypeChecker_Env.top_level =
                         (env1.FStarC_TypeChecker_Env.top_level);
                       FStarC_TypeChecker_Env.check_uvars =
                         (env1.FStarC_TypeChecker_Env.check_uvars);
                       FStarC_TypeChecker_Env.use_eq_strict =
                         (env1.FStarC_TypeChecker_Env.use_eq_strict);
                       FStarC_TypeChecker_Env.is_iface =
                         (env1.FStarC_TypeChecker_Env.is_iface);
                       FStarC_TypeChecker_Env.admit =
                         (env1.FStarC_TypeChecker_Env.admit);
                       FStarC_TypeChecker_Env.lax_universes =
                         (env1.FStarC_TypeChecker_Env.lax_universes);
                       FStarC_TypeChecker_Env.phase1 =
                         (env1.FStarC_TypeChecker_Env.phase1);
                       FStarC_TypeChecker_Env.failhard =
                         (env1.FStarC_TypeChecker_Env.failhard);
                       FStarC_TypeChecker_Env.flychecking =
                         (env1.FStarC_TypeChecker_Env.flychecking);
                       FStarC_TypeChecker_Env.uvar_subtyping =
                         (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                       FStarC_TypeChecker_Env.intactics =
                         (env1.FStarC_TypeChecker_Env.intactics);
                       FStarC_TypeChecker_Env.nocoerce =
                         (env1.FStarC_TypeChecker_Env.nocoerce);
                       FStarC_TypeChecker_Env.tc_term =
                         (env1.FStarC_TypeChecker_Env.tc_term);
                       FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.universe_of =
                         (env1.FStarC_TypeChecker_Env.universe_of);
                       FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStarC_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                       FStarC_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                       FStarC_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                       FStarC_TypeChecker_Env.normalized_eff_names =
                         (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                       FStarC_TypeChecker_Env.fv_delta_depths =
                         (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                       FStarC_TypeChecker_Env.proof_ns = uu___4;
                       FStarC_TypeChecker_Env.synth_hook =
                         (env1.FStarC_TypeChecker_Env.synth_hook);
                       FStarC_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                       FStarC_TypeChecker_Env.splice =
                         (env1.FStarC_TypeChecker_Env.splice);
                       FStarC_TypeChecker_Env.mpreprocess =
                         (env1.FStarC_TypeChecker_Env.mpreprocess);
                       FStarC_TypeChecker_Env.postprocess =
                         (env1.FStarC_TypeChecker_Env.postprocess);
                       FStarC_TypeChecker_Env.identifier_info =
                         (env1.FStarC_TypeChecker_Env.identifier_info);
                       FStarC_TypeChecker_Env.tc_hooks =
                         (env1.FStarC_TypeChecker_Env.tc_hooks);
                       FStarC_TypeChecker_Env.dsenv =
                         (env1.FStarC_TypeChecker_Env.dsenv);
                       FStarC_TypeChecker_Env.nbe =
                         (env1.FStarC_TypeChecker_Env.nbe);
                       FStarC_TypeChecker_Env.strict_args_tab =
                         (env1.FStarC_TypeChecker_Env.strict_args_tab);
                       FStarC_TypeChecker_Env.erasable_types_tab =
                         (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                       FStarC_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                       FStarC_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                       FStarC_TypeChecker_Env.erase_erasable_args =
                         (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                       FStarC_TypeChecker_Env.core_check =
                         (env1.FStarC_TypeChecker_Env.core_check);
                       FStarC_TypeChecker_Env.missing_decl =
                         (env1.FStarC_TypeChecker_Env.missing_decl)
                     })
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.RestartSolver) ->
                  if from_cache || env1.FStarC_TypeChecker_Env.flychecking
                  then env1
                  else
                    ((env1.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.refresh
                       (FStar_Pervasives_Native.Some
                          (env1.FStarC_TypeChecker_Env.proof_ns));
                     env1)
              | FStarC_Syntax_Syntax.Sig_pragma
                  (FStarC_Syntax_Syntax.PrintEffectsGraph) ->
                  ((let uu___3 =
                      FStarC_TypeChecker_Env.print_effects_graph env1 in
                    FStarC_Compiler_Util.write_file "effects.graph" uu___3);
                   env1)
              | FStarC_Syntax_Syntax.Sig_new_effect ne ->
                  let env2 =
                    FStarC_TypeChecker_Env.push_new_effect env1
                      (ne, (se.FStarC_Syntax_Syntax.sigquals)) in
                  FStarC_Compiler_List.fold_left
                    (fun env3 ->
                       fun a ->
                         let uu___2 =
                           FStarC_Syntax_Util.action_as_lb
                             ne.FStarC_Syntax_Syntax.mname a
                             (a.FStarC_Syntax_Syntax.action_defn).FStarC_Syntax_Syntax.pos in
                         FStarC_TypeChecker_Env.push_sigelt env3 uu___2) env2
                    ne.FStarC_Syntax_Syntax.actions
              | FStarC_Syntax_Syntax.Sig_sub_effect sub ->
                  FStarC_TypeChecker_Util.update_env_sub_eff env1 sub
                    se.FStarC_Syntax_Syntax.sigrng
              | FStarC_Syntax_Syntax.Sig_polymonadic_bind
                  { FStarC_Syntax_Syntax.m_lid = m;
                    FStarC_Syntax_Syntax.n_lid = n;
                    FStarC_Syntax_Syntax.p_lid = p;
                    FStarC_Syntax_Syntax.tm3 = uu___2;
                    FStarC_Syntax_Syntax.typ = ty;
                    FStarC_Syntax_Syntax.kind1 = k;_}
                  ->
                  let uu___3 = FStarC_Compiler_Util.must k in
                  FStarC_TypeChecker_Util.update_env_polymonadic_bind env1 m
                    n p ty uu___3
              | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp
                  { FStarC_Syntax_Syntax.m_lid1 = m;
                    FStarC_Syntax_Syntax.n_lid1 = n;
                    FStarC_Syntax_Syntax.tm4 = uu___2;
                    FStarC_Syntax_Syntax.typ1 = ty;
                    FStarC_Syntax_Syntax.kind2 = k;_}
                  ->
                  let uu___3 =
                    let uu___4 = FStarC_Compiler_Util.must k in (ty, uu___4) in
                  FStarC_TypeChecker_Env.add_polymonadic_subcomp env1 m n
                    uu___3
              | uu___2 -> env1))
let (compress_and_norm :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t ->
      let uu___ = FStarC_Syntax_Compress.deep_compress_if_no_uvars t in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some t1 ->
          let uu___1 =
            FStarC_TypeChecker_Normalize.normalize
              [FStarC_TypeChecker_Env.AllowUnboundUniverses;
              FStarC_TypeChecker_Env.CheckNoUvars;
              FStarC_TypeChecker_Env.Beta;
              FStarC_TypeChecker_Env.DoNotUnfoldPureLets;
              FStarC_TypeChecker_Env.CompressUvars;
              FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
              FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Iota;
              FStarC_TypeChecker_Env.NoFullNorm] env t1 in
          FStar_Pervasives_Native.Some uu___1
let (tc_decls :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.sigelt Prims.list ->
      (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu___ se =
        match uu___ with
        | (ses1, env1) ->
            (FStarC_Compiler_Effect.op_Colon_Equals
               FStarC_Errors.fallback_range
               (FStar_Pervasives_Native.Some (se.FStarC_Syntax_Syntax.sigrng));
             (let uu___2 =
                env1.FStarC_TypeChecker_Env.flychecking &&
                  (FStarC_Compiler_Debug.any ()) in
              if uu___2
              then ((ses1, env1), [])
              else
                ((let uu___5 = FStarC_Compiler_Debug.low () in
                  if uu___5
                  then
                    let uu___6 =
                      FStarC_Class_Tagged.tag_of
                        FStarC_Syntax_Syntax.tagged_sigelt se in
                    let uu___7 =
                      FStarC_Syntax_Print.sigelt_to_string_short se in
                    FStarC_Compiler_Util.print2
                      ">>>>>>>>>>>>>>Checking top-level %s decl %s\n" uu___6
                      uu___7
                  else ());
                 (let uu___6 = FStarC_Options.ide_id_info_off () in
                  if uu___6
                  then FStarC_TypeChecker_Env.toggle_id_info env1 false
                  else ());
                 (let uu___7 = FStarC_Compiler_Effect.op_Bang dbg_IdInfoOn in
                  if uu___7
                  then FStarC_TypeChecker_Env.toggle_id_info env1 true
                  else ());
                 (let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        FStarC_Syntax_Print.sigelt_to_string_short se in
                      FStarC_Compiler_Util.format2
                        "While typechecking the %stop-level declaration `%s`"
                        (if
                           (se.FStarC_Syntax_Syntax.sigmeta).FStarC_Syntax_Syntax.sigmeta_spliced
                         then "(spliced) "
                         else "") uu___9 in
                    FStarC_Errors.with_ctx uu___8
                      (fun uu___9 -> tc_decl env1 se) in
                  match uu___7 with
                  | (ses', ses_elaborated, env2) ->
                      let ses'1 =
                        FStarC_Compiler_List.map
                          (fun se1 ->
                             (let uu___9 =
                                FStarC_Compiler_Effect.op_Bang dbg_UF in
                              if uu___9
                              then
                                let uu___10 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_sigelt se1 in
                                FStarC_Compiler_Util.print1
                                  "About to elim vars from %s\n" uu___10
                              else ());
                             FStarC_TypeChecker_Normalize.elim_uvars env2 se1)
                          ses' in
                      let ses_elaborated1 =
                        FStarC_Compiler_List.map
                          (fun se1 ->
                             (let uu___9 =
                                FStarC_Compiler_Effect.op_Bang dbg_UF in
                              if uu___9
                              then
                                let uu___10 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_sigelt se1 in
                                FStarC_Compiler_Util.print1
                                  "About to elim vars from (elaborated) %s\n"
                                  uu___10
                              else ());
                             FStarC_TypeChecker_Normalize.elim_uvars env2 se1)
                          ses_elaborated in
                      (FStarC_TypeChecker_Env.promote_id_info env2
                         (compress_and_norm env2);
                       (let ses'2 =
                          FStarC_Compiler_List.map
                            (FStarC_Syntax_Compress.deep_compress_se false
                               false) ses'1 in
                        let env3 =
                          FStarC_Compiler_List.fold_left
                            (fun env4 ->
                               fun se1 -> add_sigelt_to_env env4 se1 false)
                            env2 ses'2 in
                        FStarC_Syntax_Unionfind.reset ();
                        (let uu___11 =
                           ((FStarC_Options.log_types ()) ||
                              (FStarC_Compiler_Debug.medium ()))
                             || (FStarC_Compiler_Effect.op_Bang dbg_LogTypes) in
                         if uu___11
                         then
                           let uu___12 =
                             FStarC_Class_Show.show
                               (FStarC_Class_Show.show_list
                                  FStarC_Syntax_Print.showable_sigelt) ses'2 in
                           FStarC_Compiler_Util.print1 "Checked: %s\n"
                             uu___12
                         else ());
                        (let uu___12 =
                           let uu___13 =
                             let uu___14 =
                               FStarC_TypeChecker_Env.current_module env3 in
                             FStarC_Ident.string_of_lid uu___14 in
                           FStar_Pervasives_Native.Some uu___13 in
                         FStarC_Profiling.profile
                           (fun uu___13 ->
                              FStarC_Compiler_List.iter
                                (fun se1 ->
                                   (env3.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.encode_sig
                                     env3 se1) ses'2) uu___12
                           "FStarC.TypeChecker.Tc.encode_sig");
                        (((FStarC_Compiler_List.rev_append ses'2 ses1), env3),
                          ses_elaborated1))))))) in
      let process_one_decl_timed acc se =
        FStarC_TypeChecker_Core.clear_memo_table ();
        (let uu___1 = acc in
         match uu___1 with
         | (uu___2, env1) ->
             let r =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStarC_TypeChecker_Env.current_module env1 in
                   FStarC_Ident.string_of_lid uu___5 in
                 FStar_Pervasives_Native.Some uu___4 in
               FStarC_Profiling.profile
                 (fun uu___4 -> process_one_decl acc se) uu___3
                 "FStarC.TypeChecker.Tc.process_one_decl" in
             ((let uu___4 =
                 (FStarC_Options.profile_group_by_decl ()) ||
                   (FStarC_Options.timing ()) in
               if uu___4
               then
                 let tag =
                   match FStarC_Syntax_Util.lids_of_sigelt se with
                   | hd::uu___5 -> FStarC_Ident.string_of_lid hd
                   | uu___5 ->
                       FStarC_Compiler_Range_Ops.string_of_range
                         (FStarC_Syntax_Util.range_of_sigelt se) in
                 FStarC_Profiling.report_and_clear tag
               else ());
              r)) in
      let uu___ =
        FStarC_Syntax_Unionfind.with_uf_enabled
          (fun uu___1 ->
             FStarC_Compiler_Util.fold_flatten process_one_decl_timed
               ([], env) ses) in
      match uu___ with
      | (ses1, env1) -> ((FStarC_Compiler_List.rev_append ses1 []), env1)
let (uu___0 : unit) =
  FStarC_Compiler_Effect.op_Colon_Equals tc_decls_knot
    (FStar_Pervasives_Native.Some tc_decls)
let (snapshot_context :
  FStarC_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStarC_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun msg ->
      FStarC_Compiler_Util.atomically
        (fun uu___ -> FStarC_TypeChecker_Env.snapshot env msg)
let (rollback_context :
  FStarC_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStarC_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStarC_TypeChecker_Env.env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStarC_Compiler_Util.atomically
          (fun uu___ ->
             let env = FStarC_TypeChecker_Env.rollback solver msg depth in
             env)
let (push_context :
  FStarC_TypeChecker_Env.env -> Prims.string -> FStarC_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu___ = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu___
let (pop_context :
  FStarC_TypeChecker_Env.env -> Prims.string -> FStarC_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      rollback_context env.FStarC_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
let (tc_partial_modul :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul ->
      (FStarC_Syntax_Syntax.modul * FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      let verify =
        let uu___ =
          FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
        FStarC_Options.should_verify uu___ in
      let action = if verify then "verifying" else "lax-checking" in
      let label =
        if modul.FStarC_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu___1 = FStarC_Compiler_Debug.any () in
       if uu___1
       then
         let uu___2 =
           FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
         FStarC_Compiler_Util.print3 "Now %s %s of %s\n" action label uu___2
       else ());
      FStarC_Compiler_Debug.disable_all ();
      (let uu___3 =
         let uu___4 =
           FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
         FStarC_Options.should_check uu___4 in
       if uu___3
       then
         let uu___4 = FStarC_Options.debug_keys () in
         FStarC_Compiler_Debug.enable_toggles uu___4
       else ());
      (let name =
         let uu___3 =
           FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
         FStarC_Compiler_Util.format2 "%s %s"
           (if modul.FStarC_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu___3 in
       let env1 =
         {
           FStarC_TypeChecker_Env.solver =
             (env.FStarC_TypeChecker_Env.solver);
           FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
           FStarC_TypeChecker_Env.curmodule =
             (env.FStarC_TypeChecker_Env.curmodule);
           FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
           FStarC_TypeChecker_Env.gamma_sig =
             (env.FStarC_TypeChecker_Env.gamma_sig);
           FStarC_TypeChecker_Env.gamma_cache =
             (env.FStarC_TypeChecker_Env.gamma_cache);
           FStarC_TypeChecker_Env.modules =
             (env.FStarC_TypeChecker_Env.modules);
           FStarC_TypeChecker_Env.expected_typ =
             (env.FStarC_TypeChecker_Env.expected_typ);
           FStarC_TypeChecker_Env.sigtab =
             (env.FStarC_TypeChecker_Env.sigtab);
           FStarC_TypeChecker_Env.attrtab =
             (env.FStarC_TypeChecker_Env.attrtab);
           FStarC_TypeChecker_Env.instantiate_imp =
             (env.FStarC_TypeChecker_Env.instantiate_imp);
           FStarC_TypeChecker_Env.effects =
             (env.FStarC_TypeChecker_Env.effects);
           FStarC_TypeChecker_Env.generalize =
             (env.FStarC_TypeChecker_Env.generalize);
           FStarC_TypeChecker_Env.letrecs =
             (env.FStarC_TypeChecker_Env.letrecs);
           FStarC_TypeChecker_Env.top_level =
             (env.FStarC_TypeChecker_Env.top_level);
           FStarC_TypeChecker_Env.check_uvars =
             (env.FStarC_TypeChecker_Env.check_uvars);
           FStarC_TypeChecker_Env.use_eq_strict =
             (env.FStarC_TypeChecker_Env.use_eq_strict);
           FStarC_TypeChecker_Env.is_iface =
             (modul.FStarC_Syntax_Syntax.is_interface);
           FStarC_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStarC_TypeChecker_Env.lax_universes =
             (env.FStarC_TypeChecker_Env.lax_universes);
           FStarC_TypeChecker_Env.phase1 =
             (env.FStarC_TypeChecker_Env.phase1);
           FStarC_TypeChecker_Env.failhard =
             (env.FStarC_TypeChecker_Env.failhard);
           FStarC_TypeChecker_Env.flychecking =
             (env.FStarC_TypeChecker_Env.flychecking);
           FStarC_TypeChecker_Env.uvar_subtyping =
             (env.FStarC_TypeChecker_Env.uvar_subtyping);
           FStarC_TypeChecker_Env.intactics =
             (env.FStarC_TypeChecker_Env.intactics);
           FStarC_TypeChecker_Env.nocoerce =
             (env.FStarC_TypeChecker_Env.nocoerce);
           FStarC_TypeChecker_Env.tc_term =
             (env.FStarC_TypeChecker_Env.tc_term);
           FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
             (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
           FStarC_TypeChecker_Env.universe_of =
             (env.FStarC_TypeChecker_Env.universe_of);
           FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
             (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
           FStarC_TypeChecker_Env.teq_nosmt_force =
             (env.FStarC_TypeChecker_Env.teq_nosmt_force);
           FStarC_TypeChecker_Env.subtype_nosmt_force =
             (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
           FStarC_TypeChecker_Env.qtbl_name_and_index =
             (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
           FStarC_TypeChecker_Env.normalized_eff_names =
             (env.FStarC_TypeChecker_Env.normalized_eff_names);
           FStarC_TypeChecker_Env.fv_delta_depths =
             (env.FStarC_TypeChecker_Env.fv_delta_depths);
           FStarC_TypeChecker_Env.proof_ns =
             (env.FStarC_TypeChecker_Env.proof_ns);
           FStarC_TypeChecker_Env.synth_hook =
             (env.FStarC_TypeChecker_Env.synth_hook);
           FStarC_TypeChecker_Env.try_solve_implicits_hook =
             (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
           FStarC_TypeChecker_Env.splice =
             (env.FStarC_TypeChecker_Env.splice);
           FStarC_TypeChecker_Env.mpreprocess =
             (env.FStarC_TypeChecker_Env.mpreprocess);
           FStarC_TypeChecker_Env.postprocess =
             (env.FStarC_TypeChecker_Env.postprocess);
           FStarC_TypeChecker_Env.identifier_info =
             (env.FStarC_TypeChecker_Env.identifier_info);
           FStarC_TypeChecker_Env.tc_hooks =
             (env.FStarC_TypeChecker_Env.tc_hooks);
           FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
           FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
           FStarC_TypeChecker_Env.strict_args_tab =
             (env.FStarC_TypeChecker_Env.strict_args_tab);
           FStarC_TypeChecker_Env.erasable_types_tab =
             (env.FStarC_TypeChecker_Env.erasable_types_tab);
           FStarC_TypeChecker_Env.enable_defer_to_tac =
             (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
           FStarC_TypeChecker_Env.unif_allow_ref_guards =
             (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
           FStarC_TypeChecker_Env.erase_erasable_args =
             (env.FStarC_TypeChecker_Env.erase_erasable_args);
           FStarC_TypeChecker_Env.core_check =
             (env.FStarC_TypeChecker_Env.core_check);
           FStarC_TypeChecker_Env.missing_decl =
             (env.FStarC_TypeChecker_Env.missing_decl)
         } in
       let env2 =
         FStarC_TypeChecker_Env.set_current_module env1
           modul.FStarC_Syntax_Syntax.name in
       let uu___3 =
         let uu___4 =
           let uu___5 =
             FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
           FStarC_Options.should_check uu___5 in
         Prims.op_Negation uu___4 in
       let uu___4 =
         let uu___5 =
           FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
         FStarC_Compiler_Util.format2 "While loading dependency %s%s" uu___5
           (if modul.FStarC_Syntax_Syntax.is_interface
            then " (interface)"
            else "") in
       FStarC_Errors.with_ctx_if uu___3 uu___4
         (fun uu___5 ->
            let uu___6 =
              tc_decls env2 modul.FStarC_Syntax_Syntax.declarations in
            match uu___6 with
            | (ses, env3) ->
                ({
                   FStarC_Syntax_Syntax.name =
                     (modul.FStarC_Syntax_Syntax.name);
                   FStarC_Syntax_Syntax.declarations = ses;
                   FStarC_Syntax_Syntax.is_interface =
                     (modul.FStarC_Syntax_Syntax.is_interface)
                 }, env3)))
let (tc_more_partial_modul :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul ->
      FStarC_Syntax_Syntax.sigelt Prims.list ->
        (FStarC_Syntax_Syntax.modul * FStarC_Syntax_Syntax.sigelt Prims.list
          * FStarC_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      fun decls ->
        let uu___ = tc_decls env decls in
        match uu___ with
        | (ses, env1) ->
            let modul1 =
              {
                FStarC_Syntax_Syntax.name = (modul.FStarC_Syntax_Syntax.name);
                FStarC_Syntax_Syntax.declarations =
                  (FStarC_Compiler_List.op_At
                     modul.FStarC_Syntax_Syntax.declarations ses);
                FStarC_Syntax_Syntax.is_interface =
                  (modul.FStarC_Syntax_Syntax.is_interface)
              } in
            (modul1, ses, env1)
let (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStarC_TypeChecker_Env.env ->
        FStarC_Syntax_Syntax.modul ->
          (FStarC_Syntax_Syntax.modul * FStarC_TypeChecker_Env.env))
  =
  fun loading_from_cache ->
    fun iface_exists ->
      fun en ->
        fun m ->
          let env = FStarC_TypeChecker_Env.finish_module en m in
          if Prims.op_Negation loading_from_cache
          then
            (let missing = FStarC_TypeChecker_Env.missing_definition_list env in
             if Prims.uu___is_Cons missing
             then
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStarC_Ident.string_of_lid
                           m.FStarC_Syntax_Syntax.name in
                       FStarC_Compiler_Util.format1
                         "Missing definitions in module %s:" uu___5 in
                     FStarC_Errors_Msg.text uu___4 in
                   let uu___4 =
                     FStarC_Pprint.separate_map FStarC_Pprint.hardline
                       (fun l ->
                          let uu___5 = FStarC_Ident.ident_of_lid l in
                          FStarC_Class_PP.pp FStarC_Ident.pretty_ident uu___5)
                       missing in
                   FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                     uu___3 uu___4 in
                 [uu___2] in
               FStarC_Errors.log_issue FStarC_TypeChecker_Env.hasRange_env
                 env FStarC_Errors_Codes.Error_AdmitWithoutDefinition ()
                 (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                 (Obj.magic uu___1)
             else ())
          else ();
          FStarC_Compiler_Util.smap_clear
            (FStar_Pervasives_Native.snd
               env.FStarC_TypeChecker_Env.qtbl_name_and_index);
          (let uu___3 =
             let uu___4 =
               let uu___5 =
                 FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
               Prims.strcat "Ending modul " uu___5 in
             pop_context env uu___4 in
           ());
          (let uu___4 =
             let uu___5 = FStarC_Options.depth () in uu___5 > Prims.int_zero in
           if uu___4
           then
             let uu___5 =
               let uu___6 =
                 let uu___7 =
                   let uu___8 = FStarC_Options.depth () in
                   FStarC_Class_Show.show FStarC_Class_Show.showable_int
                     uu___8 in
                 Prims.strcat uu___7 "." in
               Prims.strcat
                 "Some #push-options have not been popped. Current depth is "
                 uu___6 in
             FStarC_Errors.log_issue FStarC_TypeChecker_Env.hasRange_env env
               FStarC_Errors_Codes.Error_MissingPopOptions ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___5)
           else ());
          (m, env)
let (deep_compress_modul :
  FStarC_Syntax_Syntax.modul -> FStarC_Syntax_Syntax.modul) =
  fun m ->
    let uu___ =
      FStarC_Compiler_List.map
        (FStarC_Syntax_Compress.deep_compress_se false false)
        m.FStarC_Syntax_Syntax.declarations in
    {
      FStarC_Syntax_Syntax.name = (m.FStarC_Syntax_Syntax.name);
      FStarC_Syntax_Syntax.declarations = uu___;
      FStarC_Syntax_Syntax.is_interface =
        (m.FStarC_Syntax_Syntax.is_interface)
    }
let (tc_modul :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul ->
      Prims.bool -> (FStarC_Syntax_Syntax.modul * FStarC_TypeChecker_Env.env))
  =
  fun env0 ->
    fun m ->
      fun iface_exists ->
        let msg =
          let uu___ = FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
          Prims.strcat "Internals for " uu___ in
        let env01 = push_context env0 msg in
        let uu___ = tc_partial_modul env01 m in
        match uu___ with
        | (modul, env) -> finish_partial_modul false iface_exists env modul
let (load_checked_module_sigelts :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul -> FStarC_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      let env =
        FStarC_TypeChecker_Env.set_current_module en
          m.FStarC_Syntax_Syntax.name in
      let env1 =
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
          Prims.strcat "Internals for " uu___1 in
        push_context env uu___ in
      let env2 =
        FStarC_Compiler_List.fold_left
          (fun env3 ->
             fun se ->
               let env4 = add_sigelt_to_env env3 se true in
               let lids = FStarC_Syntax_Util.lids_of_sigelt se in
               FStarC_Compiler_List.iter
                 (fun lid ->
                    let uu___1 =
                      FStarC_TypeChecker_Env.lookup_sigelt env4 lid in
                    ()) lids;
               env4) env1 m.FStarC_Syntax_Syntax.declarations in
      env2
let (load_checked_module :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul -> FStarC_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      (let uu___1 =
         (let uu___2 = FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
          FStarC_Options.should_check uu___2) ||
           (FStarC_Options.debug_all_modules ()) in
       if uu___1
       then
         let uu___2 = FStarC_Options.debug_keys () in
         FStarC_Compiler_Debug.enable_toggles uu___2
       else FStarC_Compiler_Debug.disable_all ());
      (let m1 = deep_compress_modul m in
       let env = load_checked_module_sigelts en m1 in
       let uu___1 = finish_partial_modul true true env m1 in
       match uu___1 with | (uu___2, env1) -> env1)
let (load_partial_checked_module :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul -> FStarC_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      let m1 = deep_compress_modul m in load_checked_module_sigelts en m1
let (check_module :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.modul ->
      Prims.bool -> (FStarC_Syntax_Syntax.modul * FStarC_TypeChecker_Env.env))
  =
  fun env0 ->
    fun m ->
      fun b ->
        (let uu___1 = FStarC_Compiler_Debug.any () in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Ident.showable_lident
               m.FStarC_Syntax_Syntax.name in
           FStarC_Compiler_Util.print2 "Checking %s: %s\n"
             (if m.FStarC_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu___2
         else ());
        (let uu___2 =
           let uu___3 =
             FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
           FStarC_Options.dump_module uu___3 in
         if uu___2
         then
           let uu___3 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_modul m in
           FStarC_Compiler_Util.print1 "Module before type checking:\n%s\n"
             uu___3
         else ());
        (let env =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
               FStarC_Options.should_verify uu___4 in
             Prims.op_Negation uu___3 in
           {
             FStarC_TypeChecker_Env.solver =
               (env0.FStarC_TypeChecker_Env.solver);
             FStarC_TypeChecker_Env.range =
               (env0.FStarC_TypeChecker_Env.range);
             FStarC_TypeChecker_Env.curmodule =
               (env0.FStarC_TypeChecker_Env.curmodule);
             FStarC_TypeChecker_Env.gamma =
               (env0.FStarC_TypeChecker_Env.gamma);
             FStarC_TypeChecker_Env.gamma_sig =
               (env0.FStarC_TypeChecker_Env.gamma_sig);
             FStarC_TypeChecker_Env.gamma_cache =
               (env0.FStarC_TypeChecker_Env.gamma_cache);
             FStarC_TypeChecker_Env.modules =
               (env0.FStarC_TypeChecker_Env.modules);
             FStarC_TypeChecker_Env.expected_typ =
               (env0.FStarC_TypeChecker_Env.expected_typ);
             FStarC_TypeChecker_Env.sigtab =
               (env0.FStarC_TypeChecker_Env.sigtab);
             FStarC_TypeChecker_Env.attrtab =
               (env0.FStarC_TypeChecker_Env.attrtab);
             FStarC_TypeChecker_Env.instantiate_imp =
               (env0.FStarC_TypeChecker_Env.instantiate_imp);
             FStarC_TypeChecker_Env.effects =
               (env0.FStarC_TypeChecker_Env.effects);
             FStarC_TypeChecker_Env.generalize =
               (env0.FStarC_TypeChecker_Env.generalize);
             FStarC_TypeChecker_Env.letrecs =
               (env0.FStarC_TypeChecker_Env.letrecs);
             FStarC_TypeChecker_Env.top_level =
               (env0.FStarC_TypeChecker_Env.top_level);
             FStarC_TypeChecker_Env.check_uvars =
               (env0.FStarC_TypeChecker_Env.check_uvars);
             FStarC_TypeChecker_Env.use_eq_strict =
               (env0.FStarC_TypeChecker_Env.use_eq_strict);
             FStarC_TypeChecker_Env.is_iface =
               (env0.FStarC_TypeChecker_Env.is_iface);
             FStarC_TypeChecker_Env.admit = uu___2;
             FStarC_TypeChecker_Env.lax_universes =
               (env0.FStarC_TypeChecker_Env.lax_universes);
             FStarC_TypeChecker_Env.phase1 =
               (env0.FStarC_TypeChecker_Env.phase1);
             FStarC_TypeChecker_Env.failhard =
               (env0.FStarC_TypeChecker_Env.failhard);
             FStarC_TypeChecker_Env.flychecking =
               (env0.FStarC_TypeChecker_Env.flychecking);
             FStarC_TypeChecker_Env.uvar_subtyping =
               (env0.FStarC_TypeChecker_Env.uvar_subtyping);
             FStarC_TypeChecker_Env.intactics =
               (env0.FStarC_TypeChecker_Env.intactics);
             FStarC_TypeChecker_Env.nocoerce =
               (env0.FStarC_TypeChecker_Env.nocoerce);
             FStarC_TypeChecker_Env.tc_term =
               (env0.FStarC_TypeChecker_Env.tc_term);
             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
               (env0.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
             FStarC_TypeChecker_Env.universe_of =
               (env0.FStarC_TypeChecker_Env.universe_of);
             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
               (env0.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
             FStarC_TypeChecker_Env.teq_nosmt_force =
               (env0.FStarC_TypeChecker_Env.teq_nosmt_force);
             FStarC_TypeChecker_Env.subtype_nosmt_force =
               (env0.FStarC_TypeChecker_Env.subtype_nosmt_force);
             FStarC_TypeChecker_Env.qtbl_name_and_index =
               (env0.FStarC_TypeChecker_Env.qtbl_name_and_index);
             FStarC_TypeChecker_Env.normalized_eff_names =
               (env0.FStarC_TypeChecker_Env.normalized_eff_names);
             FStarC_TypeChecker_Env.fv_delta_depths =
               (env0.FStarC_TypeChecker_Env.fv_delta_depths);
             FStarC_TypeChecker_Env.proof_ns =
               (env0.FStarC_TypeChecker_Env.proof_ns);
             FStarC_TypeChecker_Env.synth_hook =
               (env0.FStarC_TypeChecker_Env.synth_hook);
             FStarC_TypeChecker_Env.try_solve_implicits_hook =
               (env0.FStarC_TypeChecker_Env.try_solve_implicits_hook);
             FStarC_TypeChecker_Env.splice =
               (env0.FStarC_TypeChecker_Env.splice);
             FStarC_TypeChecker_Env.mpreprocess =
               (env0.FStarC_TypeChecker_Env.mpreprocess);
             FStarC_TypeChecker_Env.postprocess =
               (env0.FStarC_TypeChecker_Env.postprocess);
             FStarC_TypeChecker_Env.identifier_info =
               (env0.FStarC_TypeChecker_Env.identifier_info);
             FStarC_TypeChecker_Env.tc_hooks =
               (env0.FStarC_TypeChecker_Env.tc_hooks);
             FStarC_TypeChecker_Env.dsenv =
               (env0.FStarC_TypeChecker_Env.dsenv);
             FStarC_TypeChecker_Env.nbe = (env0.FStarC_TypeChecker_Env.nbe);
             FStarC_TypeChecker_Env.strict_args_tab =
               (env0.FStarC_TypeChecker_Env.strict_args_tab);
             FStarC_TypeChecker_Env.erasable_types_tab =
               (env0.FStarC_TypeChecker_Env.erasable_types_tab);
             FStarC_TypeChecker_Env.enable_defer_to_tac =
               (env0.FStarC_TypeChecker_Env.enable_defer_to_tac);
             FStarC_TypeChecker_Env.unif_allow_ref_guards =
               (env0.FStarC_TypeChecker_Env.unif_allow_ref_guards);
             FStarC_TypeChecker_Env.erase_erasable_args =
               (env0.FStarC_TypeChecker_Env.erase_erasable_args);
             FStarC_TypeChecker_Env.core_check =
               (env0.FStarC_TypeChecker_Env.core_check);
             FStarC_TypeChecker_Env.missing_decl =
               (env0.FStarC_TypeChecker_Env.missing_decl)
           } in
         let uu___2 = tc_modul env m b in
         match uu___2 with
         | (m1, env1) ->
             let env2 =
               {
                 FStarC_TypeChecker_Env.solver =
                   (env1.FStarC_TypeChecker_Env.solver);
                 FStarC_TypeChecker_Env.range =
                   (env1.FStarC_TypeChecker_Env.range);
                 FStarC_TypeChecker_Env.curmodule =
                   (env1.FStarC_TypeChecker_Env.curmodule);
                 FStarC_TypeChecker_Env.gamma =
                   (env1.FStarC_TypeChecker_Env.gamma);
                 FStarC_TypeChecker_Env.gamma_sig =
                   (env1.FStarC_TypeChecker_Env.gamma_sig);
                 FStarC_TypeChecker_Env.gamma_cache =
                   (env1.FStarC_TypeChecker_Env.gamma_cache);
                 FStarC_TypeChecker_Env.modules =
                   (env1.FStarC_TypeChecker_Env.modules);
                 FStarC_TypeChecker_Env.expected_typ =
                   (env1.FStarC_TypeChecker_Env.expected_typ);
                 FStarC_TypeChecker_Env.sigtab =
                   (env1.FStarC_TypeChecker_Env.sigtab);
                 FStarC_TypeChecker_Env.attrtab =
                   (env1.FStarC_TypeChecker_Env.attrtab);
                 FStarC_TypeChecker_Env.instantiate_imp =
                   (env1.FStarC_TypeChecker_Env.instantiate_imp);
                 FStarC_TypeChecker_Env.effects =
                   (env1.FStarC_TypeChecker_Env.effects);
                 FStarC_TypeChecker_Env.generalize =
                   (env1.FStarC_TypeChecker_Env.generalize);
                 FStarC_TypeChecker_Env.letrecs =
                   (env1.FStarC_TypeChecker_Env.letrecs);
                 FStarC_TypeChecker_Env.top_level =
                   (env1.FStarC_TypeChecker_Env.top_level);
                 FStarC_TypeChecker_Env.check_uvars =
                   (env1.FStarC_TypeChecker_Env.check_uvars);
                 FStarC_TypeChecker_Env.use_eq_strict =
                   (env1.FStarC_TypeChecker_Env.use_eq_strict);
                 FStarC_TypeChecker_Env.is_iface =
                   (env1.FStarC_TypeChecker_Env.is_iface);
                 FStarC_TypeChecker_Env.admit =
                   (env0.FStarC_TypeChecker_Env.admit);
                 FStarC_TypeChecker_Env.lax_universes =
                   (env1.FStarC_TypeChecker_Env.lax_universes);
                 FStarC_TypeChecker_Env.phase1 =
                   (env1.FStarC_TypeChecker_Env.phase1);
                 FStarC_TypeChecker_Env.failhard =
                   (env1.FStarC_TypeChecker_Env.failhard);
                 FStarC_TypeChecker_Env.flychecking =
                   (env1.FStarC_TypeChecker_Env.flychecking);
                 FStarC_TypeChecker_Env.uvar_subtyping =
                   (env1.FStarC_TypeChecker_Env.uvar_subtyping);
                 FStarC_TypeChecker_Env.intactics =
                   (env1.FStarC_TypeChecker_Env.intactics);
                 FStarC_TypeChecker_Env.nocoerce =
                   (env1.FStarC_TypeChecker_Env.nocoerce);
                 FStarC_TypeChecker_Env.tc_term =
                   (env1.FStarC_TypeChecker_Env.tc_term);
                 FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                   (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                 FStarC_TypeChecker_Env.universe_of =
                   (env1.FStarC_TypeChecker_Env.universe_of);
                 FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                   (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                 FStarC_TypeChecker_Env.teq_nosmt_force =
                   (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
                 FStarC_TypeChecker_Env.subtype_nosmt_force =
                   (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
                 FStarC_TypeChecker_Env.qtbl_name_and_index =
                   (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
                 FStarC_TypeChecker_Env.normalized_eff_names =
                   (env1.FStarC_TypeChecker_Env.normalized_eff_names);
                 FStarC_TypeChecker_Env.fv_delta_depths =
                   (env1.FStarC_TypeChecker_Env.fv_delta_depths);
                 FStarC_TypeChecker_Env.proof_ns =
                   (env1.FStarC_TypeChecker_Env.proof_ns);
                 FStarC_TypeChecker_Env.synth_hook =
                   (env1.FStarC_TypeChecker_Env.synth_hook);
                 FStarC_TypeChecker_Env.try_solve_implicits_hook =
                   (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                 FStarC_TypeChecker_Env.splice =
                   (env1.FStarC_TypeChecker_Env.splice);
                 FStarC_TypeChecker_Env.mpreprocess =
                   (env1.FStarC_TypeChecker_Env.mpreprocess);
                 FStarC_TypeChecker_Env.postprocess =
                   (env1.FStarC_TypeChecker_Env.postprocess);
                 FStarC_TypeChecker_Env.identifier_info =
                   (env1.FStarC_TypeChecker_Env.identifier_info);
                 FStarC_TypeChecker_Env.tc_hooks =
                   (env1.FStarC_TypeChecker_Env.tc_hooks);
                 FStarC_TypeChecker_Env.dsenv =
                   (env1.FStarC_TypeChecker_Env.dsenv);
                 FStarC_TypeChecker_Env.nbe =
                   (env1.FStarC_TypeChecker_Env.nbe);
                 FStarC_TypeChecker_Env.strict_args_tab =
                   (env1.FStarC_TypeChecker_Env.strict_args_tab);
                 FStarC_TypeChecker_Env.erasable_types_tab =
                   (env1.FStarC_TypeChecker_Env.erasable_types_tab);
                 FStarC_TypeChecker_Env.enable_defer_to_tac =
                   (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
                 FStarC_TypeChecker_Env.unif_allow_ref_guards =
                   (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                 FStarC_TypeChecker_Env.erase_erasable_args =
                   (env1.FStarC_TypeChecker_Env.erase_erasable_args);
                 FStarC_TypeChecker_Env.core_check =
                   (env1.FStarC_TypeChecker_Env.core_check);
                 FStarC_TypeChecker_Env.missing_decl =
                   (env1.FStarC_TypeChecker_Env.missing_decl)
               } in
             ((let uu___4 =
                 let uu___5 =
                   FStarC_Ident.string_of_lid m1.FStarC_Syntax_Syntax.name in
                 FStarC_Options.dump_module uu___5 in
               if uu___4
               then
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_modul
                     m1 in
                 FStarC_Compiler_Util.print1
                   "Module after type checking:\n%s\n" uu___5
               else ());
              (let uu___5 =
                 (let uu___6 =
                    FStarC_Ident.string_of_lid m1.FStarC_Syntax_Syntax.name in
                  FStarC_Options.dump_module uu___6) &&
                   (FStarC_Compiler_Effect.op_Bang dbg_Normalize) in
               if uu___5
               then
                 let normalize_toplevel_lets se =
                   match se.FStarC_Syntax_Syntax.sigel with
                   | FStarC_Syntax_Syntax.Sig_let
                       { FStarC_Syntax_Syntax.lbs1 = (b1, lbs);
                         FStarC_Syntax_Syntax.lids1 = ids;_}
                       ->
                       let n =
                         FStarC_TypeChecker_Normalize.normalize
                           [FStarC_TypeChecker_Env.Beta;
                           FStarC_TypeChecker_Env.Eager_unfolding;
                           FStarC_TypeChecker_Env.Reify;
                           FStarC_TypeChecker_Env.Inlining;
                           FStarC_TypeChecker_Env.Primops;
                           FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant;
                           FStarC_TypeChecker_Env.AllowUnboundUniverses] in
                       let update lb =
                         let uu___6 =
                           FStarC_Syntax_Subst.open_univ_vars
                             lb.FStarC_Syntax_Syntax.lbunivs
                             lb.FStarC_Syntax_Syntax.lbdef in
                         match uu___6 with
                         | (univnames, e) ->
                             let uu___7 =
                               let uu___8 =
                                 FStarC_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu___8 e in
                             {
                               FStarC_Syntax_Syntax.lbname =
                                 (lb.FStarC_Syntax_Syntax.lbname);
                               FStarC_Syntax_Syntax.lbunivs =
                                 (lb.FStarC_Syntax_Syntax.lbunivs);
                               FStarC_Syntax_Syntax.lbtyp =
                                 (lb.FStarC_Syntax_Syntax.lbtyp);
                               FStarC_Syntax_Syntax.lbeff =
                                 (lb.FStarC_Syntax_Syntax.lbeff);
                               FStarC_Syntax_Syntax.lbdef = uu___7;
                               FStarC_Syntax_Syntax.lbattrs =
                                 (lb.FStarC_Syntax_Syntax.lbattrs);
                               FStarC_Syntax_Syntax.lbpos =
                                 (lb.FStarC_Syntax_Syntax.lbpos)
                             } in
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = FStarC_Compiler_List.map update lbs in
                             (b1, uu___9) in
                           {
                             FStarC_Syntax_Syntax.lbs1 = uu___8;
                             FStarC_Syntax_Syntax.lids1 = ids
                           } in
                         FStarC_Syntax_Syntax.Sig_let uu___7 in
                       {
                         FStarC_Syntax_Syntax.sigel = uu___6;
                         FStarC_Syntax_Syntax.sigrng =
                           (se.FStarC_Syntax_Syntax.sigrng);
                         FStarC_Syntax_Syntax.sigquals =
                           (se.FStarC_Syntax_Syntax.sigquals);
                         FStarC_Syntax_Syntax.sigmeta =
                           (se.FStarC_Syntax_Syntax.sigmeta);
                         FStarC_Syntax_Syntax.sigattrs =
                           (se.FStarC_Syntax_Syntax.sigattrs);
                         FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                           (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                         FStarC_Syntax_Syntax.sigopts =
                           (se.FStarC_Syntax_Syntax.sigopts)
                       }
                   | uu___6 -> se in
                 let normalized_module =
                   let uu___6 =
                     FStarC_Compiler_List.map normalize_toplevel_lets
                       m1.FStarC_Syntax_Syntax.declarations in
                   {
                     FStarC_Syntax_Syntax.name =
                       (m1.FStarC_Syntax_Syntax.name);
                     FStarC_Syntax_Syntax.declarations = uu___6;
                     FStarC_Syntax_Syntax.is_interface =
                       (m1.FStarC_Syntax_Syntax.is_interface)
                   } in
                 let uu___6 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_modul
                     normalized_module in
                 FStarC_Compiler_Util.print1 "%s\n" uu___6
               else ());
              (m1, env2)))