open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      let tbl =
        FStar_Compiler_Effect.op_Bar_Greater
          env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst in
      let get_n lid =
        let n_opt =
          let uu___ = FStar_Ident.string_of_lid lid in
          FStar_Compiler_Util.smap_try_find tbl uu___ in
        if FStar_Compiler_Util.is_some n_opt
        then
          FStar_Compiler_Effect.op_Bar_Greater n_opt FStar_Compiler_Util.must
        else Prims.int_zero in
      let uu___ = FStar_Options.reuse_hint_for () in
      match uu___ with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu___1 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu___1 l in
          let uu___1 =
            let uu___2 =
              let uu___3 = let uu___4 = get_n lid in (lid, uu___4) in
              FStar_Pervasives_Native.Some uu___3 in
            (tbl, uu___2) in
          {
            FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.tc_term =
              (env.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu___1;
            FStar_TypeChecker_Env.normalized_eff_names =
              (env.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env.FStar_TypeChecker_Env.core_check)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu___1 = FStar_TypeChecker_Env.current_module env in
                let uu___2 =
                  let uu___3 = FStar_GenSym.next_id () in
                  FStar_Compiler_Effect.op_Bar_Greater uu___3
                    FStar_Compiler_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu___1 uu___2
            | l::uu___1 -> l in
          let uu___1 =
            let uu___2 =
              let uu___3 = let uu___4 = get_n lid in (lid, uu___4) in
              FStar_Pervasives_Native.Some uu___3 in
            (tbl, uu___2) in
          {
            FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.intactics =
              (env.FStar_TypeChecker_Env.intactics);
            FStar_TypeChecker_Env.tc_term =
              (env.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu___1;
            FStar_TypeChecker_Env.normalized_eff_names =
              (env.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env.FStar_TypeChecker_Env.core_check)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu___ =
         let uu___1 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu___1 in
       Prims.op_Negation uu___)
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Compiler_Range_Type.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun uu___ ->
      fun expected_typ ->
        fun r ->
          match uu___ with
          | (uvs, t) ->
              let uu___1 = FStar_Syntax_Subst.open_univ_vars uvs t in
              (match uu___1 with
               | (uvs1, t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                   let t2 =
                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t1
                       expected_typ in
                   if uvs1 = []
                   then
                     let uu___2 =
                       FStar_TypeChecker_Generalize.generalize_universes env1
                         t2 in
                     (match uu___2 with
                      | (uvs2, t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu___3 =
                        let uu___4 =
                          FStar_Compiler_Effect.op_Bar_Greater t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1) in
                        FStar_Compiler_Effect.op_Bar_Greater uu___4
                          (FStar_Syntax_Subst.close_univ_vars uvs1) in
                      (uvs1, uu___3)))
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Compiler_Range_Type.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStar_Syntax_Util.type_u () in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            FStar_Pervasives_Native.fst in
        tc_type_common env ts uu___ r
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Compiler_Range_Type.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStar_Syntax_Util.type_u () in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            FStar_Pervasives_Native.fst in
        tc_type_common env ts uu___ r
let (tc_decl_attributes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env ->
    fun se ->
      let uu___ =
        let uu___1 =
          FStar_TypeChecker_Env.lid_exists env
            FStar_Parser_Const.attr_substitute_lid in
        if uu___1
        then ([], (se.FStar_Syntax_Syntax.sigattrs))
        else
          FStar_Compiler_List.partition
            ((=) FStar_Syntax_Util.attr_substitute)
            se.FStar_Syntax_Syntax.sigattrs in
      match uu___ with
      | (blacklisted_attrs, other_attrs) ->
          let uu___1 =
            let uu___2 =
              FStar_TypeChecker_TcTerm.tc_attributes env other_attrs in
            FStar_Compiler_List.op_At blacklisted_attrs uu___2 in
          {
            FStar_Syntax_Syntax.sigel = (se.FStar_Syntax_Syntax.sigel);
            FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals = (se.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs = uu___1;
            FStar_Syntax_Syntax.sigopts = (se.FStar_Syntax_Syntax.sigopts)
          }
let (tc_inductive' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Ident.lident Prims.list ->
            (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
              Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          fun lids ->
            (let uu___1 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
             if uu___1
             then
               let uu___2 =
                 (FStar_Common.string_of_list ())
                   FStar_Syntax_Print.sigelt_to_string ses in
               FStar_Compiler_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n"
                 uu___2
             else ());
            (let ses1 = FStar_Compiler_List.map (tc_decl_attributes env) ses in
             let uu___1 =
               FStar_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses1 quals lids in
             match uu___1 with
             | (sig_bndle, tcs, datas) ->
                 let sig_bndle1 =
                   FStar_TypeChecker_Positivity.mark_uniform_type_parameters
                     env sig_bndle in
                 let attrs' =
                   FStar_Syntax_Util.remove_attr
                     FStar_Parser_Const.erasable_attr attrs in
                 let data_ops_ses =
                   let uu___2 =
                     FStar_Compiler_List.map
                       (FStar_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas in
                   FStar_Compiler_Effect.op_Bar_Greater uu___2
                     FStar_Compiler_List.flatten in
                 ((let uu___3 =
                     (FStar_Options.no_positivity ()) ||
                       (let uu___4 = FStar_TypeChecker_Env.should_verify env in
                        Prims.op_Negation uu___4) in
                   if uu___3
                   then ()
                   else
                     (let env1 =
                        FStar_TypeChecker_Env.push_sigelt env sig_bndle1 in
                      FStar_Compiler_List.iter
                        (fun ty ->
                           let b =
                             FStar_TypeChecker_Positivity.check_strict_positivity
                               env1 lids ty in
                           if Prims.op_Negation b
                           then
                             let uu___6 =
                               match ty.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   { FStar_Syntax_Syntax.lid = lid;
                                     FStar_Syntax_Syntax.us = uu___7;
                                     FStar_Syntax_Syntax.params = uu___8;
                                     FStar_Syntax_Syntax.num_uniform_params =
                                       uu___9;
                                     FStar_Syntax_Syntax.t = uu___10;
                                     FStar_Syntax_Syntax.mutuals = uu___11;
                                     FStar_Syntax_Syntax.ds = uu___12;_}
                                   -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                               | uu___7 -> failwith "Impossible!" in
                             match uu___6 with
                             | (lid, r) ->
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         FStar_Ident.string_of_lid lid in
                                       Prims.op_Hat uu___10
                                         " does not satisfy the strict positivity condition" in
                                     Prims.op_Hat "Inductive type " uu___9 in
                                   (FStar_Errors_Codes.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu___8) in
                                 FStar_Errors.log_issue r uu___7
                           else ()) tcs;
                      FStar_Compiler_List.iter
                        (fun d ->
                           let uu___6 =
                             match d.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 { FStar_Syntax_Syntax.lid1 = data_lid;
                                   FStar_Syntax_Syntax.us1 = uu___7;
                                   FStar_Syntax_Syntax.t1 = uu___8;
                                   FStar_Syntax_Syntax.ty_lid = ty_lid;
                                   FStar_Syntax_Syntax.num_ty_params = uu___9;
                                   FStar_Syntax_Syntax.mutuals1 = uu___10;_}
                                 -> (data_lid, ty_lid)
                             | uu___7 -> failwith "Impossible" in
                           match uu___6 with
                           | (data_lid, ty_lid) ->
                               let uu___7 =
                                 (FStar_Ident.lid_equals ty_lid
                                    FStar_Parser_Const.exn_lid)
                                   &&
                                   (let uu___8 =
                                      FStar_TypeChecker_Positivity.check_exn_strict_positivity
                                        env1 data_lid in
                                    Prims.op_Negation uu___8) in
                               if uu___7
                               then
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 =
                                         FStar_Ident.string_of_lid data_lid in
                                       Prims.op_Hat uu___11
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Exception " uu___10 in
                                   (FStar_Errors_Codes.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu___9) in
                                 FStar_Errors.log_issue
                                   d.FStar_Syntax_Syntax.sigrng uu___8
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu___3 =
                       let lid =
                         let ty = FStar_Compiler_List.hd tcs in
                         match ty.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             { FStar_Syntax_Syntax.lid = lid1;
                               FStar_Syntax_Syntax.us = uu___4;
                               FStar_Syntax_Syntax.params = uu___5;
                               FStar_Syntax_Syntax.num_uniform_params =
                                 uu___6;
                               FStar_Syntax_Syntax.t = uu___7;
                               FStar_Syntax_Syntax.mutuals = uu___8;
                               FStar_Syntax_Syntax.ds = uu___9;_}
                             -> lid1
                         | uu___4 -> failwith "Impossible" in
                       FStar_Compiler_List.existsb
                         (fun s ->
                            let uu___4 =
                              let uu___5 = FStar_Ident.ident_of_lid lid in
                              FStar_Ident.string_of_id uu___5 in
                            s = uu___4)
                         FStar_TypeChecker_TcInductive.early_prims_inductives in
                     let is_noeq =
                       FStar_Compiler_List.existsb
                         (fun q -> q = FStar_Syntax_Syntax.Noeq) quals in
                     let is_erasable uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_Compiler_List.hd tcs in
                         uu___5.FStar_Syntax_Syntax.sigattrs in
                       FStar_Syntax_Util.has_attribute uu___4
                         FStar_Parser_Const.erasable_attr in
                     ((((FStar_Compiler_List.length tcs) = Prims.int_zero) ||
                         ((FStar_Ident.lid_equals
                             env.FStar_TypeChecker_Env.curmodule
                             FStar_Parser_Const.prims_lid)
                            && (skip_prims_type ())))
                        || is_noeq)
                       || (is_erasable ()) in
                   let res =
                     if skip_haseq
                     then (sig_bndle1, data_ops_ses)
                     else
                       (let is_unopteq =
                          FStar_Compiler_List.existsb
                            (fun q -> q = FStar_Syntax_Syntax.Unopteq) quals in
                        let ses2 =
                          if is_unopteq
                          then
                            FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                              sig_bndle1 tcs datas env
                          else
                            FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                              sig_bndle1 tcs datas env in
                        (sig_bndle1,
                          (FStar_Compiler_List.op_At ses2 data_ops_ses))) in
                   res)))
let (tc_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Ident.lident Prims.list ->
            (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.sigelt
              Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun attrs ->
          fun lids ->
            let env1 = FStar_TypeChecker_Env.push env "tc_inductive" in
            let pop uu___ =
              let uu___1 = FStar_TypeChecker_Env.pop env1 "tc_inductive" in
              () in
            let uu___ = FStar_Options.trace_error () in
            if uu___
            then
              let r = tc_inductive' env1 ses quals attrs lids in (pop (); r)
            else
              (try
                 (fun uu___2 ->
                    match () with
                    | () ->
                        let uu___3 = tc_inductive' env1 ses quals attrs lids in
                        FStar_Compiler_Effect.op_Bar_Greater uu___3
                          (fun r -> pop (); r)) ()
               with | uu___2 -> (pop (); FStar_Compiler_Effect.raise uu___2))
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let
          { FStar_Syntax_Syntax.lbs1 = lbs; FStar_Syntax_Syntax.lids1 = l;_}
          ->
          let uu___ =
            let uu___1 = FStar_Options.ide () in Prims.op_Negation uu___1 in
          if uu___
          then
            let uu___1 =
              let uu___2 = FStar_TypeChecker_Env.dsenv env in
              let uu___3 = FStar_TypeChecker_Env.current_module env in
              FStar_Syntax_DsEnv.iface_decls uu___2 uu___3 in
            (match uu___1 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some iface_decls ->
                 FStar_Compiler_Effect.op_Bar_Greater
                   (FStar_Pervasives_Native.snd lbs)
                   (FStar_Compiler_List.iter
                      (fun lb ->
                         let lbname =
                           FStar_Compiler_Util.right
                             lb.FStar_Syntax_Syntax.lbname in
                         let has_iface_val =
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 FStar_Ident.ident_of_lid
                                   (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               FStar_Parser_AST.decl_is_val uu___4 in
                             FStar_Compiler_Util.for_some uu___3 in
                           FStar_Compiler_Effect.op_Bar_Greater iface_decls
                             uu___2 in
                         if has_iface_val
                         then
                           let must_erase =
                             FStar_TypeChecker_Util.must_erase_for_extraction
                               env lb.FStar_Syntax_Syntax.lbdef in
                           let has_attr =
                             FStar_TypeChecker_Env.fv_has_attr env lbname
                               FStar_Parser_Const.must_erase_for_extraction_attr in
                           (if must_erase && (Prims.op_Negation has_attr)
                            then
                              let uu___2 =
                                FStar_Syntax_Syntax.range_of_fv lbname in
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  let uu___6 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  FStar_Compiler_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu___5 uu___6 in
                                (FStar_Errors_Codes.Error_MustEraseMissing,
                                  uu___4) in
                              FStar_Errors.log_issue uu___2 uu___3
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu___3 =
                                   FStar_Syntax_Syntax.range_of_fv lbname in
                                 let uu___4 =
                                   let uu___5 =
                                     let uu___6 =
                                       FStar_Syntax_Print.fv_to_string lbname in
                                     FStar_Compiler_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu___6 in
                                   (FStar_Errors_Codes.Error_MustEraseMissing,
                                     uu___5) in
                                 FStar_Errors.log_issue uu___3 uu___4)
                              else ())
                         else ())))
          else ()
      | uu___ -> ()
let (check_typeclass_instance_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      let is_tc_instance =
        FStar_Compiler_Effect.op_Bar_Greater se.FStar_Syntax_Syntax.sigattrs
          (FStar_Compiler_Util.for_some
             (fun t ->
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.tcinstance_lid
                | uu___ -> false)) in
      if Prims.op_Negation is_tc_instance
      then ()
      else
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_let
             { FStar_Syntax_Syntax.lbs1 = (false, lb::[]);
               FStar_Syntax_Syntax.lids1 = uu___1;_}
             ->
             let uu___2 =
               FStar_Syntax_Util.arrow_formals_comp
                 lb.FStar_Syntax_Syntax.lbtyp in
             (match uu___2 with
              | (uu___3, res) ->
                  let uu___4 = FStar_Syntax_Util.is_total_comp res in
                  if uu___4
                  then
                    let t = FStar_Syntax_Util.comp_result res in
                    let uu___5 = FStar_Syntax_Util.head_and_args t in
                    (match uu___5 with
                     | (head, uu___6) ->
                         let err uu___7 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 FStar_Syntax_Print.term_to_string t in
                               FStar_Compiler_Util.format1
                                 "Instances must define instances of `class` types. Type %s is not a class"
                                 uu___10 in
                             (FStar_Errors_Codes.Error_UnexpectedTypeclassInstance,
                               uu___9) in
                           FStar_Errors.log_issue
                             (FStar_Syntax_Util.range_of_sigelt se) uu___8 in
                         let uu___7 =
                           let uu___8 = FStar_Syntax_Util.un_uinst head in
                           uu___8.FStar_Syntax_Syntax.n in
                         (match uu___7 with
                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                              let uu___8 =
                                let uu___9 =
                                  FStar_TypeChecker_Env.fv_has_attr env fv
                                    FStar_Parser_Const.tcclass_lid in
                                Prims.op_Negation uu___9 in
                              if uu___8 then err () else ()
                          | uu___8 -> err ()))
                  else
                    (let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_Ident.string_of_lid
                             (FStar_Syntax_Util.comp_effect_name res) in
                         FStar_Compiler_Util.format1
                           "Instances are expected to be total. This instance has effect %s"
                           uu___8 in
                       (FStar_Errors_Codes.Error_UnexpectedTypeclassInstance,
                         uu___7) in
                     FStar_Errors.log_issue
                       (FStar_Syntax_Util.range_of_sigelt se) uu___6))
         | uu___1 ->
             FStar_Errors.log_issue (FStar_Syntax_Util.range_of_sigelt se)
               (FStar_Errors_Codes.Error_UnexpectedTypeclassInstance,
                 "An `instance` is expected to be a non-recursive definition whose type is an instance of a `class`"))
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs ->
    fun kont ->
      let uu___ =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs in
      match uu___ with
      | FStar_Pervasives_Native.None -> kont ()
      | FStar_Pervasives_Native.Some ((a1, FStar_Pervasives_Native.None)::[])
          ->
          let uu___1 =
            FStar_Syntax_Embeddings_Base.unembed
              FStar_Syntax_Embeddings.e_vconfig a1
              FStar_Syntax_Embeddings_Base.id_norm_cb in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> failwith "nah"
           | FStar_Pervasives_Native.Some vcfg ->
               FStar_Options.with_saved_options
                 (fun uu___2 -> FStar_Options.set_vconfig vcfg; kont ())
           | uu___2 -> failwith "ill-formed `check_with`")
let (handle_postprocess_with_attr :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      (FStar_Syntax_Syntax.attribute Prims.list * FStar_Syntax_Syntax.term
        FStar_Pervasives_Native.option))
  =
  fun env ->
    fun ats ->
      let uu___ =
        FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_with
          ats in
      match uu___ with
      | FStar_Pervasives_Native.None -> (ats, FStar_Pervasives_Native.None)
      | FStar_Pervasives_Native.Some
          (ats1, (tau, FStar_Pervasives_Native.None)::[]) ->
          (ats1, (FStar_Pervasives_Native.Some tau))
      | FStar_Pervasives_Native.Some (ats1, args) ->
          ((let uu___2 = FStar_TypeChecker_Env.get_range env in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Ident.string_of_lid
                    FStar_Parser_Const.postprocess_with in
                FStar_Compiler_Util.format1 "Ill-formed application of `%s`"
                  uu___5 in
              (FStar_Errors_Codes.Warning_UnrecognizedAttribute, uu___4) in
            FStar_Errors.log_issue uu___2 uu___3);
           (ats1, FStar_Pervasives_Native.None))
let (store_sigopts :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ =
      let uu___1 = FStar_Options.get_vconfig () in
      FStar_Pervasives_Native.Some uu___1 in
    {
      FStar_Syntax_Syntax.sigel = (se.FStar_Syntax_Syntax.sigel);
      FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
      FStar_Syntax_Syntax.sigquals = (se.FStar_Syntax_Syntax.sigquals);
      FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
      FStar_Syntax_Syntax.sigattrs = (se.FStar_Syntax_Syntax.sigattrs);
      FStar_Syntax_Syntax.sigopts = uu___
    }
let (tc_decls_knot :
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.sigelt Prims.list ->
       (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env))
    FStar_Pervasives_Native.option FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (do_two_phases : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env -> FStar_TypeChecker_Env.should_verify env
let run_phase1 : 'a . (unit -> 'a) -> 'a =
  fun f ->
    FStar_TypeChecker_Core.clear_memo_table ();
    (let r = f () in FStar_TypeChecker_Core.clear_memo_table (); r)
let (tc_sig_let :
  FStar_TypeChecker_Env.env ->
    FStar_Compiler_Range_Type.range ->
      FStar_Syntax_Syntax.sigelt ->
        (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
          FStar_Ident.lident Prims.list ->
            (FStar_Syntax_Syntax.sigelt Prims.list *
              FStar_Syntax_Syntax.sigelt Prims.list *
              FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun r ->
      fun se ->
        fun lbs ->
          fun lids ->
            let env0 = env in
            let env1 = FStar_TypeChecker_Env.set_range env r in
            let check_quals_eq l qopt val_q =
              match qopt with
              | FStar_Pervasives_Native.None ->
                  FStar_Pervasives_Native.Some val_q
              | FStar_Pervasives_Native.Some q' ->
                  let drop_logic_and_irreducible =
                    FStar_Compiler_List.filter
                      (fun x ->
                         Prims.op_Negation
                           ((x = FStar_Syntax_Syntax.Logic) ||
                              (x = FStar_Syntax_Syntax.Irreducible))) in
                  let uu___ =
                    let uu___1 =
                      let uu___2 = drop_logic_and_irreducible val_q in
                      let uu___3 = drop_logic_and_irreducible q' in
                      (uu___2, uu___3) in
                    match uu___1 with
                    | (val_q1, q'1) ->
                        ((FStar_Compiler_List.length val_q1) =
                           (FStar_Compiler_List.length q'1))
                          &&
                          (FStar_Compiler_List.forall2
                             FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                  if uu___
                  then FStar_Pervasives_Native.Some q'
                  else
                    (let uu___2 =
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Print.lid_to_string l in
                         let uu___5 =
                           FStar_Syntax_Print.quals_to_string val_q in
                         let uu___6 = FStar_Syntax_Print.quals_to_string q' in
                         FStar_Compiler_Util.format3
                           "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                           uu___4 uu___5 uu___6 in
                       (FStar_Errors_Codes.Fatal_InconsistentQualifierAnnotation,
                         uu___3) in
                     FStar_Errors.raise_error uu___2 r) in
            let rename_parameters lb =
              let rename_in_typ def typ =
                let typ1 = FStar_Syntax_Subst.compress typ in
                let def_bs =
                  let uu___ =
                    let uu___1 = FStar_Syntax_Subst.compress def in
                    uu___1.FStar_Syntax_Syntax.n in
                  match uu___ with
                  | FStar_Syntax_Syntax.Tm_abs
                      { FStar_Syntax_Syntax.bs = binders;
                        FStar_Syntax_Syntax.body = uu___1;
                        FStar_Syntax_Syntax.rc_opt = uu___2;_}
                      -> binders
                  | uu___1 -> [] in
                match typ1 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                      { FStar_Syntax_Syntax.bs1 = val_bs;
                        FStar_Syntax_Syntax.comp = c;_};
                    FStar_Syntax_Syntax.pos = r1;
                    FStar_Syntax_Syntax.vars = uu___;
                    FStar_Syntax_Syntax.hash_code = uu___1;_} ->
                    let has_auto_name bv =
                      let uu___2 =
                        FStar_Ident.string_of_id
                          bv.FStar_Syntax_Syntax.ppname in
                      FStar_Compiler_Util.starts_with uu___2
                        FStar_Ident.reserved_prefix in
                    let rec rename_binders def_bs1 val_bs1 =
                      match (def_bs1, val_bs1) with
                      | ([], uu___2) -> val_bs1
                      | (uu___2, []) -> val_bs1
                      | ({ FStar_Syntax_Syntax.binder_bv = body_bv;
                           FStar_Syntax_Syntax.binder_qual = uu___2;
                           FStar_Syntax_Syntax.binder_positivity = uu___3;
                           FStar_Syntax_Syntax.binder_attrs = uu___4;_}::bt,
                         val_b::vt) ->
                          let uu___5 =
                            let uu___6 =
                              let uu___7 = has_auto_name body_bv in
                              let uu___8 =
                                has_auto_name
                                  val_b.FStar_Syntax_Syntax.binder_bv in
                              (uu___7, uu___8) in
                            match uu___6 with
                            | (true, uu___7) -> val_b
                            | (false, true) ->
                                let uu___7 =
                                  let uu___8 =
                                    val_b.FStar_Syntax_Syntax.binder_bv in
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStar_Ident.string_of_id
                                          body_bv.FStar_Syntax_Syntax.ppname in
                                      let uu___12 =
                                        FStar_Ident.range_of_id
                                          (val_b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                                      (uu___11, uu___12) in
                                    FStar_Ident.mk_ident uu___10 in
                                  {
                                    FStar_Syntax_Syntax.ppname = uu___9;
                                    FStar_Syntax_Syntax.index =
                                      (uu___8.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort =
                                      (uu___8.FStar_Syntax_Syntax.sort)
                                  } in
                                {
                                  FStar_Syntax_Syntax.binder_bv = uu___7;
                                  FStar_Syntax_Syntax.binder_qual =
                                    (val_b.FStar_Syntax_Syntax.binder_qual);
                                  FStar_Syntax_Syntax.binder_positivity =
                                    (val_b.FStar_Syntax_Syntax.binder_positivity);
                                  FStar_Syntax_Syntax.binder_attrs =
                                    (val_b.FStar_Syntax_Syntax.binder_attrs)
                                }
                            | (false, false) -> val_b in
                          let uu___6 = rename_binders bt vt in uu___5 ::
                            uu___6 in
                    let uu___2 =
                      let uu___3 =
                        let uu___4 = rename_binders def_bs val_bs in
                        {
                          FStar_Syntax_Syntax.bs1 = uu___4;
                          FStar_Syntax_Syntax.comp = c
                        } in
                      FStar_Syntax_Syntax.Tm_arrow uu___3 in
                    FStar_Syntax_Syntax.mk uu___2 r1
                | uu___ -> typ1 in
              let uu___ =
                rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                  lb.FStar_Syntax_Syntax.lbtyp in
              {
                FStar_Syntax_Syntax.lbname = (lb.FStar_Syntax_Syntax.lbname);
                FStar_Syntax_Syntax.lbunivs =
                  (lb.FStar_Syntax_Syntax.lbunivs);
                FStar_Syntax_Syntax.lbtyp = uu___;
                FStar_Syntax_Syntax.lbeff = (lb.FStar_Syntax_Syntax.lbeff);
                FStar_Syntax_Syntax.lbdef = (lb.FStar_Syntax_Syntax.lbdef);
                FStar_Syntax_Syntax.lbattrs =
                  (lb.FStar_Syntax_Syntax.lbattrs);
                FStar_Syntax_Syntax.lbpos = (lb.FStar_Syntax_Syntax.lbpos)
              } in
            let uu___ =
              FStar_Compiler_Effect.op_Bar_Greater
                (FStar_Pervasives_Native.snd lbs)
                (FStar_Compiler_List.fold_left
                   (fun uu___1 ->
                      fun lb ->
                        match uu___1 with
                        | (gen, lbs1, quals_opt) ->
                            let lbname =
                              FStar_Compiler_Util.right
                                lb.FStar_Syntax_Syntax.lbname in
                            let uu___2 =
                              let uu___3 =
                                FStar_TypeChecker_Env.try_lookup_val_decl
                                  env1
                                  (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              match uu___3 with
                              | FStar_Pervasives_Native.None ->
                                  (gen, lb, quals_opt)
                              | FStar_Pervasives_Native.Some
                                  ((uvs, tval), quals) ->
                                  let quals_opt1 =
                                    check_quals_eq
                                      (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      quals_opt quals in
                                  let def =
                                    match (lb.FStar_Syntax_Syntax.lbtyp).FStar_Syntax_Syntax.n
                                    with
                                    | FStar_Syntax_Syntax.Tm_unknown ->
                                        lb.FStar_Syntax_Syntax.lbdef
                                    | uu___4 ->
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             {
                                               FStar_Syntax_Syntax.tm =
                                                 (lb.FStar_Syntax_Syntax.lbdef);
                                               FStar_Syntax_Syntax.asc =
                                                 ((FStar_Pervasives.Inl
                                                     (lb.FStar_Syntax_Syntax.lbtyp)),
                                                   FStar_Pervasives_Native.None,
                                                   false);
                                               FStar_Syntax_Syntax.eff_opt =
                                                 FStar_Pervasives_Native.None
                                             })
                                          (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                  (if
                                     (lb.FStar_Syntax_Syntax.lbunivs <> [])
                                       &&
                                       ((FStar_Compiler_List.length
                                           lb.FStar_Syntax_Syntax.lbunivs)
                                          <> (FStar_Compiler_List.length uvs))
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors_Codes.Fatal_IncoherentInlineUniverse,
                                         "Inline universes are incoherent with annotation from val declaration")
                                       r
                                   else ();
                                   (let uu___5 =
                                      FStar_Syntax_Syntax.mk_lb
                                        ((FStar_Pervasives.Inr lbname), uvs,
                                          FStar_Parser_Const.effect_Tot_lid,
                                          tval, def,
                                          (lb.FStar_Syntax_Syntax.lbattrs),
                                          (lb.FStar_Syntax_Syntax.lbpos)) in
                                    (false, uu___5, quals_opt1))) in
                            (match uu___2 with
                             | (gen1, lb1, quals_opt1) ->
                                 (gen1, (lb1 :: lbs1), quals_opt1)))
                   (true, [],
                     (if se.FStar_Syntax_Syntax.sigquals = []
                      then FStar_Pervasives_Native.None
                      else
                        FStar_Pervasives_Native.Some
                          (se.FStar_Syntax_Syntax.sigquals)))) in
            match uu___ with
            | (should_generalize, lbs', quals_opt) ->
                (FStar_Syntax_Util.check_mutual_universes lbs';
                 (let quals =
                    match quals_opt with
                    | FStar_Pervasives_Native.None ->
                        [FStar_Syntax_Syntax.Visible_default]
                    | FStar_Pervasives_Native.Some q ->
                        let uu___2 =
                          FStar_Compiler_Effect.op_Bar_Greater q
                            (FStar_Compiler_Util.for_some
                               (fun uu___3 ->
                                  match uu___3 with
                                  | FStar_Syntax_Syntax.Irreducible -> true
                                  | FStar_Syntax_Syntax.Visible_default ->
                                      true
                                  | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                      -> true
                                  | uu___4 -> false)) in
                        if uu___2
                        then q
                        else FStar_Syntax_Syntax.Visible_default :: q in
                  let lbs'1 = FStar_Compiler_List.rev lbs' in
                  let uu___2 =
                    let uu___3 =
                      FStar_Syntax_Util.extract_attr'
                        FStar_Parser_Const.preprocess_with
                        se.FStar_Syntax_Syntax.sigattrs in
                    match uu___3 with
                    | FStar_Pervasives_Native.None ->
                        ((se.FStar_Syntax_Syntax.sigattrs),
                          FStar_Pervasives_Native.None)
                    | FStar_Pervasives_Native.Some
                        (ats, (tau, FStar_Pervasives_Native.None)::[]) ->
                        (ats, (FStar_Pervasives_Native.Some tau))
                    | FStar_Pervasives_Native.Some (ats, args) ->
                        (FStar_Errors.log_issue r
                           (FStar_Errors_Codes.Warning_UnrecognizedAttribute,
                             "Ill-formed application of `preprocess_with`");
                         ((se.FStar_Syntax_Syntax.sigattrs),
                           FStar_Pervasives_Native.None)) in
                  match uu___2 with
                  | (attrs, pre_tau) ->
                      let se1 =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (se.FStar_Syntax_Syntax.sigel);
                          FStar_Syntax_Syntax.sigrng =
                            (se.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (se.FStar_Syntax_Syntax.sigquals);
                          FStar_Syntax_Syntax.sigmeta =
                            (se.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs = attrs;
                          FStar_Syntax_Syntax.sigopts =
                            (se.FStar_Syntax_Syntax.sigopts)
                        } in
                      let preprocess_lb tau lb =
                        let lbdef =
                          FStar_TypeChecker_Env.preprocess env1 tau
                            lb.FStar_Syntax_Syntax.lbdef in
                        (let uu___4 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases") in
                         if uu___4
                         then
                           let uu___5 =
                             FStar_Syntax_Print.term_to_string lbdef in
                           FStar_Compiler_Util.print1
                             "lb preprocessed into: %s\n" uu___5
                         else ());
                        {
                          FStar_Syntax_Syntax.lbname =
                            (lb.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs =
                            (lb.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (lb.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (lb.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (lb.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (lb.FStar_Syntax_Syntax.lbpos)
                        } in
                      let lbs'2 =
                        match pre_tau with
                        | FStar_Pervasives_Native.Some tau ->
                            FStar_Compiler_List.map (preprocess_lb tau) lbs'1
                        | FStar_Pervasives_Native.None -> lbs'1 in
                      let e =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_constant
                                   FStar_Const.Const_unit) r in
                            {
                              FStar_Syntax_Syntax.lbs =
                                ((FStar_Pervasives_Native.fst lbs), lbs'2);
                              FStar_Syntax_Syntax.body1 = uu___5
                            } in
                          FStar_Syntax_Syntax.Tm_let uu___4 in
                        FStar_Syntax_Syntax.mk uu___3 r in
                      let env' =
                        {
                          FStar_TypeChecker_Env.solver =
                            (env1.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (env1.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (env1.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (env1.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (env1.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (env1.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (env1.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (env1.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (env1.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (env1.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (env1.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (env1.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            should_generalize;
                          FStar_TypeChecker_Env.letrecs =
                            (env1.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = true;
                          FStar_TypeChecker_Env.check_uvars =
                            (env1.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq_strict =
                            (env1.FStar_TypeChecker_Env.use_eq_strict);
                          FStar_TypeChecker_Env.is_iface =
                            (env1.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (env1.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (env1.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (env1.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (env1.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (env1.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (env1.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (env1.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.intactics =
                            (env1.FStar_TypeChecker_Env.intactics);
                          FStar_TypeChecker_Env.tc_term =
                            (env1.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                            (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                          FStar_TypeChecker_Env.universe_of =
                            (env1.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                            =
                            (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                          FStar_TypeChecker_Env.teq_nosmt_force =
                            (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                          FStar_TypeChecker_Env.subtype_nosmt_force =
                            (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (env1.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (env1.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (env1.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (env1.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (env1.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.mpreprocess =
                            (env1.FStar_TypeChecker_Env.mpreprocess);
                          FStar_TypeChecker_Env.postprocess =
                            (env1.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.identifier_info =
                            (env1.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (env1.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (env1.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (env1.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (env1.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (env1.FStar_TypeChecker_Env.erasable_types_tab);
                          FStar_TypeChecker_Env.enable_defer_to_tac =
                            (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                          FStar_TypeChecker_Env.unif_allow_ref_guards =
                            (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                          FStar_TypeChecker_Env.erase_erasable_args =
                            (env1.FStar_TypeChecker_Env.erase_erasable_args);
                          FStar_TypeChecker_Env.core_check =
                            (env1.FStar_TypeChecker_Env.core_check)
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
                                     FStar_Syntax_Subst.compress e_lax in
                                   uu___6.FStar_Syntax_Syntax.n in
                                 match uu___5 with
                                 | FStar_Syntax_Syntax.Tm_let
                                     {
                                       FStar_Syntax_Syntax.lbs =
                                         (false, lb::[]);
                                       FStar_Syntax_Syntax.body1 = e2;_}
                                     ->
                                     let lb_unannotated =
                                       let uu___6 =
                                         let uu___7 =
                                           FStar_Syntax_Subst.compress e in
                                         uu___7.FStar_Syntax_Syntax.n in
                                       match uu___6 with
                                       | FStar_Syntax_Syntax.Tm_let
                                           {
                                             FStar_Syntax_Syntax.lbs =
                                               (uu___7, lb1::[]);
                                             FStar_Syntax_Syntax.body1 =
                                               uu___8;_}
                                           ->
                                           let uu___9 =
                                             let uu___10 =
                                               FStar_Syntax_Subst.compress
                                                 lb1.FStar_Syntax_Syntax.lbtyp in
                                             uu___10.FStar_Syntax_Syntax.n in
                                           (match uu___9 with
                                            | FStar_Syntax_Syntax.Tm_unknown
                                                -> true
                                            | uu___10 -> false)
                                       | uu___7 ->
                                           failwith
                                             "Impossible: first phase lb and second phase lb differ in structure!" in
                                     if lb_unannotated
                                     then
                                       {
                                         FStar_Syntax_Syntax.n =
                                           (FStar_Syntax_Syntax.Tm_let
                                              {
                                                FStar_Syntax_Syntax.lbs =
                                                  (false,
                                                    [{
                                                       FStar_Syntax_Syntax.lbname
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbname);
                                                       FStar_Syntax_Syntax.lbunivs
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbunivs);
                                                       FStar_Syntax_Syntax.lbtyp
                                                         =
                                                         FStar_Syntax_Syntax.tun;
                                                       FStar_Syntax_Syntax.lbeff
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbeff);
                                                       FStar_Syntax_Syntax.lbdef
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbdef);
                                                       FStar_Syntax_Syntax.lbattrs
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbattrs);
                                                       FStar_Syntax_Syntax.lbpos
                                                         =
                                                         (lb.FStar_Syntax_Syntax.lbpos)
                                                     }]);
                                                FStar_Syntax_Syntax.body1 =
                                                  e2
                                              });
                                         FStar_Syntax_Syntax.pos =
                                           (e_lax.FStar_Syntax_Syntax.pos);
                                         FStar_Syntax_Syntax.vars =
                                           (e_lax.FStar_Syntax_Syntax.vars);
                                         FStar_Syntax_Syntax.hash_code =
                                           (e_lax.FStar_Syntax_Syntax.hash_code)
                                       }
                                     else e_lax
                                 | FStar_Syntax_Syntax.Tm_let
                                     {
                                       FStar_Syntax_Syntax.lbs = (true, lbs1);
                                       FStar_Syntax_Syntax.body1 = uu___6;_}
                                     ->
                                     (FStar_Syntax_Util.check_mutual_universes
                                        lbs1;
                                      e_lax) in
                               let e2 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_TypeChecker_Env.current_module
                                         env1 in
                                     FStar_Ident.string_of_lid uu___7 in
                                   FStar_Pervasives_Native.Some uu___6 in
                                 FStar_Profiling.profile
                                   (fun uu___6 ->
                                      let uu___7 =
                                        FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                          {
                                            FStar_TypeChecker_Env.solver =
                                              (env'.FStar_TypeChecker_Env.solver);
                                            FStar_TypeChecker_Env.range =
                                              (env'.FStar_TypeChecker_Env.range);
                                            FStar_TypeChecker_Env.curmodule =
                                              (env'.FStar_TypeChecker_Env.curmodule);
                                            FStar_TypeChecker_Env.gamma =
                                              (env'.FStar_TypeChecker_Env.gamma);
                                            FStar_TypeChecker_Env.gamma_sig =
                                              (env'.FStar_TypeChecker_Env.gamma_sig);
                                            FStar_TypeChecker_Env.gamma_cache
                                              =
                                              (env'.FStar_TypeChecker_Env.gamma_cache);
                                            FStar_TypeChecker_Env.modules =
                                              (env'.FStar_TypeChecker_Env.modules);
                                            FStar_TypeChecker_Env.expected_typ
                                              =
                                              (env'.FStar_TypeChecker_Env.expected_typ);
                                            FStar_TypeChecker_Env.sigtab =
                                              (env'.FStar_TypeChecker_Env.sigtab);
                                            FStar_TypeChecker_Env.attrtab =
                                              (env'.FStar_TypeChecker_Env.attrtab);
                                            FStar_TypeChecker_Env.instantiate_imp
                                              =
                                              (env'.FStar_TypeChecker_Env.instantiate_imp);
                                            FStar_TypeChecker_Env.effects =
                                              (env'.FStar_TypeChecker_Env.effects);
                                            FStar_TypeChecker_Env.generalize
                                              =
                                              (env'.FStar_TypeChecker_Env.generalize);
                                            FStar_TypeChecker_Env.letrecs =
                                              (env'.FStar_TypeChecker_Env.letrecs);
                                            FStar_TypeChecker_Env.top_level =
                                              (env'.FStar_TypeChecker_Env.top_level);
                                            FStar_TypeChecker_Env.check_uvars
                                              =
                                              (env'.FStar_TypeChecker_Env.check_uvars);
                                            FStar_TypeChecker_Env.use_eq_strict
                                              =
                                              (env'.FStar_TypeChecker_Env.use_eq_strict);
                                            FStar_TypeChecker_Env.is_iface =
                                              (env'.FStar_TypeChecker_Env.is_iface);
                                            FStar_TypeChecker_Env.admit =
                                              (env'.FStar_TypeChecker_Env.admit);
                                            FStar_TypeChecker_Env.lax = true;
                                            FStar_TypeChecker_Env.lax_universes
                                              =
                                              (env'.FStar_TypeChecker_Env.lax_universes);
                                            FStar_TypeChecker_Env.phase1 =
                                              true;
                                            FStar_TypeChecker_Env.failhard =
                                              (env'.FStar_TypeChecker_Env.failhard);
                                            FStar_TypeChecker_Env.nosynth =
                                              (env'.FStar_TypeChecker_Env.nosynth);
                                            FStar_TypeChecker_Env.uvar_subtyping
                                              =
                                              (env'.FStar_TypeChecker_Env.uvar_subtyping);
                                            FStar_TypeChecker_Env.intactics =
                                              (env'.FStar_TypeChecker_Env.intactics);
                                            FStar_TypeChecker_Env.tc_term =
                                              (env'.FStar_TypeChecker_Env.tc_term);
                                            FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                              =
                                              (env'.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                            FStar_TypeChecker_Env.universe_of
                                              =
                                              (env'.FStar_TypeChecker_Env.universe_of);
                                            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                              =
                                              (env'.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                            FStar_TypeChecker_Env.teq_nosmt_force
                                              =
                                              (env'.FStar_TypeChecker_Env.teq_nosmt_force);
                                            FStar_TypeChecker_Env.subtype_nosmt_force
                                              =
                                              (env'.FStar_TypeChecker_Env.subtype_nosmt_force);
                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                              =
                                              (env'.FStar_TypeChecker_Env.qtbl_name_and_index);
                                            FStar_TypeChecker_Env.normalized_eff_names
                                              =
                                              (env'.FStar_TypeChecker_Env.normalized_eff_names);
                                            FStar_TypeChecker_Env.fv_delta_depths
                                              =
                                              (env'.FStar_TypeChecker_Env.fv_delta_depths);
                                            FStar_TypeChecker_Env.proof_ns =
                                              (env'.FStar_TypeChecker_Env.proof_ns);
                                            FStar_TypeChecker_Env.synth_hook
                                              =
                                              (env'.FStar_TypeChecker_Env.synth_hook);
                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                              =
                                              (env'.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                            FStar_TypeChecker_Env.splice =
                                              (env'.FStar_TypeChecker_Env.splice);
                                            FStar_TypeChecker_Env.mpreprocess
                                              =
                                              (env'.FStar_TypeChecker_Env.mpreprocess);
                                            FStar_TypeChecker_Env.postprocess
                                              =
                                              (env'.FStar_TypeChecker_Env.postprocess);
                                            FStar_TypeChecker_Env.identifier_info
                                              =
                                              (env'.FStar_TypeChecker_Env.identifier_info);
                                            FStar_TypeChecker_Env.tc_hooks =
                                              (env'.FStar_TypeChecker_Env.tc_hooks);
                                            FStar_TypeChecker_Env.dsenv =
                                              (env'.FStar_TypeChecker_Env.dsenv);
                                            FStar_TypeChecker_Env.nbe =
                                              (env'.FStar_TypeChecker_Env.nbe);
                                            FStar_TypeChecker_Env.strict_args_tab
                                              =
                                              (env'.FStar_TypeChecker_Env.strict_args_tab);
                                            FStar_TypeChecker_Env.erasable_types_tab
                                              =
                                              (env'.FStar_TypeChecker_Env.erasable_types_tab);
                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                              =
                                              (env'.FStar_TypeChecker_Env.enable_defer_to_tac);
                                            FStar_TypeChecker_Env.unif_allow_ref_guards
                                              =
                                              (env'.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                            FStar_TypeChecker_Env.erase_erasable_args
                                              =
                                              (env'.FStar_TypeChecker_Env.erase_erasable_args);
                                            FStar_TypeChecker_Env.core_check
                                              =
                                              (env'.FStar_TypeChecker_Env.core_check)
                                          } e in
                                      match uu___7 with
                                      | (e3, uu___8, uu___9) -> e3) uu___5
                                   "FStar.TypeChecker.Tc.tc_sig_let-tc-phase1" in
                               (let uu___6 =
                                  FStar_Compiler_Effect.op_Less_Bar
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "TwoPhases") in
                                if uu___6
                                then
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string e2 in
                                  FStar_Compiler_Util.print1
                                    "Let binding after phase 1, before removing uvars: %s\n"
                                    uu___7
                                else ());
                               (let e3 =
                                  let uu___6 =
                                    FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env' e2 in
                                  FStar_Compiler_Effect.op_Bar_Greater uu___6
                                    drop_lbtyp in
                                (let uu___7 =
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "TwoPhases") in
                                 if uu___7
                                 then
                                   let uu___8 =
                                     FStar_Syntax_Print.term_to_string e3 in
                                   FStar_Compiler_Util.print1
                                     "Let binding after phase 1, uvars removed: %s\n"
                                     uu___8
                                 else ());
                                e3))
                        else e in
                      let uu___3 =
                        handle_postprocess_with_attr env1
                          se1.FStar_Syntax_Syntax.sigattrs in
                      (match uu___3 with
                       | (attrs1, post_tau) ->
                           let se2 =
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (se1.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (se1.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (se1.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (se1.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = attrs1;
                               FStar_Syntax_Syntax.sigopts =
                                 (se1.FStar_Syntax_Syntax.sigopts)
                             } in
                           let postprocess_lb tau lb =
                             let uu___4 =
                               FStar_Syntax_Subst.univ_var_opening
                                 lb.FStar_Syntax_Syntax.lbunivs in
                             match uu___4 with
                             | (s, univnames) ->
                                 let lbdef =
                                   FStar_Syntax_Subst.subst s
                                     lb.FStar_Syntax_Syntax.lbdef in
                                 let lbtyp =
                                   FStar_Syntax_Subst.subst s
                                     lb.FStar_Syntax_Syntax.lbtyp in
                                 let env2 =
                                   FStar_TypeChecker_Env.push_univ_vars env1
                                     univnames in
                                 let lbdef1 =
                                   FStar_TypeChecker_Env.postprocess env2 tau
                                     lbtyp lbdef in
                                 let lbdef2 =
                                   FStar_Syntax_Subst.close_univ_vars
                                     univnames lbdef1 in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (lb.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs =
                                     (lb.FStar_Syntax_Syntax.lbunivs);
                                   FStar_Syntax_Syntax.lbtyp =
                                     (lb.FStar_Syntax_Syntax.lbtyp);
                                   FStar_Syntax_Syntax.lbeff =
                                     (lb.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = lbdef2;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (lb.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (lb.FStar_Syntax_Syntax.lbpos)
                                 } in
                           let r1 =
                             let should_generalize1 =
                               let uu___4 = do_two_phases env' in
                               Prims.op_Negation uu___4 in
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 =
                                   FStar_TypeChecker_Env.current_module env1 in
                                 FStar_Ident.string_of_lid uu___6 in
                               FStar_Pervasives_Native.Some uu___5 in
                             FStar_Profiling.profile
                               (fun uu___5 ->
                                  FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (env'.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (env'.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (env'.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (env'.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (env'.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (env'.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (env'.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (env'.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (env'.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (env'.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (env'.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (env'.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        should_generalize1;
                                      FStar_TypeChecker_Env.letrecs =
                                        (env'.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (env'.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (env'.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (env'.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (env'.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (env'.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (env'.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (env'.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (env'.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (env'.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (env'.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (env'.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.intactics =
                                        (env'.FStar_TypeChecker_Env.intactics);
                                      FStar_TypeChecker_Env.tc_term =
                                        (env'.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                        =
                                        (env'.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                      FStar_TypeChecker_Env.universe_of =
                                        (env'.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                        =
                                        (env'.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                      FStar_TypeChecker_Env.teq_nosmt_force =
                                        (env'.FStar_TypeChecker_Env.teq_nosmt_force);
                                      FStar_TypeChecker_Env.subtype_nosmt_force
                                        =
                                        (env'.FStar_TypeChecker_Env.subtype_nosmt_force);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (env'.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (env'.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (env'.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (env'.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (env'.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (env'.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (env'.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (env'.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (env'.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (env'.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (env'.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (env'.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (env'.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (env'.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (env'.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (env'.FStar_TypeChecker_Env.enable_defer_to_tac);
                                      FStar_TypeChecker_Env.unif_allow_ref_guards
                                        =
                                        (env'.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                      FStar_TypeChecker_Env.erase_erasable_args
                                        =
                                        (env'.FStar_TypeChecker_Env.erase_erasable_args);
                                      FStar_TypeChecker_Env.core_check =
                                        (env'.FStar_TypeChecker_Env.core_check)
                                    } e1) uu___4
                               "FStar.TypeChecker.Tc.tc_sig_let-tc-phase2" in
                           let uu___4 =
                             match r1 with
                             | ({
                                  FStar_Syntax_Syntax.n =
                                    FStar_Syntax_Syntax.Tm_let
                                    { FStar_Syntax_Syntax.lbs = lbs1;
                                      FStar_Syntax_Syntax.body1 = e2;_};
                                  FStar_Syntax_Syntax.pos = uu___5;
                                  FStar_Syntax_Syntax.vars = uu___6;
                                  FStar_Syntax_Syntax.hash_code = uu___7;_},
                                uu___8, g) when
                                 FStar_TypeChecker_Env.is_trivial g ->
                                 (FStar_Syntax_Util.check_mutual_universes
                                    (FStar_Pervasives_Native.snd lbs1);
                                  (let lbs2 =
                                     let uu___10 =
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         (FStar_Pervasives_Native.snd lbs1)
                                         (FStar_Compiler_List.map
                                            rename_parameters) in
                                     ((FStar_Pervasives_Native.fst lbs1),
                                       uu___10) in
                                   let lbs3 =
                                     let uu___10 =
                                       match post_tau with
                                       | FStar_Pervasives_Native.Some tau ->
                                           FStar_Compiler_List.map
                                             (postprocess_lb tau)
                                             (FStar_Pervasives_Native.snd
                                                lbs2)
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Pervasives_Native.snd lbs2 in
                                     ((FStar_Pervasives_Native.fst lbs2),
                                       uu___10) in
                                   let quals1 =
                                     match e2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_meta
                                         { FStar_Syntax_Syntax.tm2 = uu___10;
                                           FStar_Syntax_Syntax.meta =
                                             FStar_Syntax_Syntax.Meta_desugared
                                             (FStar_Syntax_Syntax.Masked_effect);_}
                                         ->
                                         FStar_Syntax_Syntax.HasMaskedEffect
                                         :: quals
                                     | uu___10 -> quals in
                                   ({
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_let
                                           {
                                             FStar_Syntax_Syntax.lbs1 = lbs3;
                                             FStar_Syntax_Syntax.lids1 = lids
                                           });
                                      FStar_Syntax_Syntax.sigrng =
                                        (se2.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals = quals1;
                                      FStar_Syntax_Syntax.sigmeta =
                                        (se2.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (se2.FStar_Syntax_Syntax.sigattrs);
                                      FStar_Syntax_Syntax.sigopts =
                                        (se2.FStar_Syntax_Syntax.sigopts)
                                    }, lbs3)))
                             | uu___5 ->
                                 failwith
                                   "impossible (typechecking should preserve Tm_let)" in
                           (match uu___4 with
                            | (se3, lbs1) ->
                                ((let uu___6 =
                                    FStar_Syntax_Util.has_attribute
                                      se3.FStar_Syntax_Syntax.sigattrs
                                      FStar_Parser_Const.no_subtping_attr_lid in
                                  if uu___6
                                  then
                                    let env'1 =
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (env'.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (env'.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (env'.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (env'.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (env'.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (env'.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (env'.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (env'.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (env'.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (env'.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (env'.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (env'.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (env'.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (env'.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (env'.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (env'.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          true;
                                        FStar_TypeChecker_Env.is_iface =
                                          (env'.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (env'.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (env'.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (env'.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (env'.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (env'.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (env'.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (env'.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.intactics =
                                          (env'.FStar_TypeChecker_Env.intactics);
                                        FStar_TypeChecker_Env.tc_term =
                                          (env'.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                          =
                                          (env'.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                        FStar_TypeChecker_Env.universe_of =
                                          (env'.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                          =
                                          (env'.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                        FStar_TypeChecker_Env.teq_nosmt_force
                                          =
                                          (env'.FStar_TypeChecker_Env.teq_nosmt_force);
                                        FStar_TypeChecker_Env.subtype_nosmt_force
                                          =
                                          (env'.FStar_TypeChecker_Env.subtype_nosmt_force);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (env'.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (env'.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (env'.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (env'.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (env'.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (env'.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (env'.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (env'.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (env'.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (env'.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (env'.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (env'.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (env'.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (env'.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (env'.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (env'.FStar_TypeChecker_Env.enable_defer_to_tac);
                                        FStar_TypeChecker_Env.unif_allow_ref_guards
                                          =
                                          (env'.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                        FStar_TypeChecker_Env.erase_erasable_args
                                          =
                                          (env'.FStar_TypeChecker_Env.erase_erasable_args);
                                        FStar_TypeChecker_Env.core_check =
                                          (env'.FStar_TypeChecker_Env.core_check)
                                      } in
                                    let err s pos =
                                      FStar_Errors.raise_error
                                        (FStar_Errors_Codes.Fatal_InconsistentQualifierAnnotation,
                                          s) pos in
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      (FStar_Pervasives_Native.snd lbs1)
                                      (FStar_Compiler_List.iter
                                         (fun lb ->
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_Syntax_Util.is_lemma
                                                  lb.FStar_Syntax_Syntax.lbtyp in
                                              Prims.op_Negation uu___8 in
                                            if uu___7
                                            then
                                              err
                                                "no_subtype annotation on a non-lemma"
                                                lb.FStar_Syntax_Syntax.lbpos
                                            else
                                              (let lid_opt =
                                                 let uu___9 =
                                                   let uu___10 =
                                                     FStar_Syntax_Free.fvars
                                                       lb.FStar_Syntax_Syntax.lbtyp in
                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                     uu___10
                                                     FStar_Compiler_Util.set_elements in
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   uu___9
                                                   (FStar_Compiler_List.tryFind
                                                      (fun lid ->
                                                         let uu___10 =
                                                           (let uu___11 =
                                                              let uu___12 =
                                                                FStar_Compiler_Effect.op_Bar_Greater
                                                                  lid
                                                                  FStar_Ident.path_of_lid in
                                                              FStar_Compiler_Effect.op_Bar_Greater
                                                                uu___12
                                                                FStar_Compiler_List.hd in
                                                            uu___11 = "Prims")
                                                             ||
                                                             (FStar_Ident.lid_equals
                                                                lid
                                                                FStar_Parser_Const.pattern_lid) in
                                                         Prims.op_Negation
                                                           uu___10)) in
                                               let uu___9 =
                                                 FStar_Compiler_Effect.op_Bar_Greater
                                                   lid_opt
                                                   FStar_Compiler_Util.is_some in
                                               if uu___9
                                               then
                                                 let uu___10 =
                                                   let uu___11 =
                                                     let uu___12 =
                                                       FStar_Compiler_Effect.op_Bar_Greater
                                                         lid_opt
                                                         FStar_Compiler_Util.must in
                                                     FStar_Compiler_Effect.op_Bar_Greater
                                                       uu___12
                                                       FStar_Ident.string_of_lid in
                                                   FStar_Compiler_Util.format1
                                                     "%s is not allowed in no_subtyping lemmas (only prims symbols)"
                                                     uu___11 in
                                                 err uu___10
                                                   lb.FStar_Syntax_Syntax.lbpos
                                               else
                                                 (let uu___11 =
                                                    FStar_Syntax_Util.type_u
                                                      () in
                                                  match uu___11 with
                                                  | (t, uu___12) ->
                                                      let uu___13 =
                                                        FStar_Syntax_Subst.open_univ_vars
                                                          lb.FStar_Syntax_Syntax.lbunivs
                                                          lb.FStar_Syntax_Syntax.lbtyp in
                                                      (match uu___13 with
                                                       | (uvs, lbtyp) ->
                                                           let uu___14 =
                                                             let uu___15 =
                                                               FStar_TypeChecker_Env.push_univ_vars
                                                                 env'1 uvs in
                                                             FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term
                                                               uu___15 lbtyp
                                                               t
                                                               "checking no_subtype annotation" in
                                                           (match uu___14
                                                            with
                                                            | (uu___15,
                                                               uu___16, g) ->
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env'1 g))))))
                                  else ());
                                 FStar_Compiler_Effect.op_Bar_Greater
                                   (FStar_Pervasives_Native.snd lbs1)
                                   (FStar_Compiler_List.iter
                                      (fun lb ->
                                         let fv =
                                           FStar_Compiler_Util.right
                                             lb.FStar_Syntax_Syntax.lbname in
                                         FStar_TypeChecker_Env.insert_fv_info
                                           env1 fv
                                           lb.FStar_Syntax_Syntax.lbtyp));
                                 (let uu___8 = log env1 in
                                  if uu___8
                                  then
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          (FStar_Pervasives_Native.snd lbs1)
                                          (FStar_Compiler_List.map
                                             (fun lb ->
                                                let should_log =
                                                  let uu___11 =
                                                    let uu___12 =
                                                      let uu___13 =
                                                        let uu___14 =
                                                          FStar_Compiler_Util.right
                                                            lb.FStar_Syntax_Syntax.lbname in
                                                        uu___14.FStar_Syntax_Syntax.fv_name in
                                                      uu___13.FStar_Syntax_Syntax.v in
                                                    FStar_TypeChecker_Env.try_lookup_val_decl
                                                      env1 uu___12 in
                                                  match uu___11 with
                                                  | FStar_Pervasives_Native.None
                                                      -> true
                                                  | uu___12 -> false in
                                                if should_log
                                                then
                                                  let uu___11 =
                                                    FStar_Syntax_Print.lbname_to_string
                                                      lb.FStar_Syntax_Syntax.lbname in
                                                  let uu___12 =
                                                    FStar_Syntax_Print.term_to_string
                                                      lb.FStar_Syntax_Syntax.lbtyp in
                                                  FStar_Compiler_Util.format2
                                                    "let %s : %s" uu___11
                                                    uu___12
                                                else "")) in
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        uu___10 (FStar_String.concat "\n") in
                                    FStar_Compiler_Util.print1 "%s\n" uu___9
                                  else ());
                                 check_must_erase_attribute env0 se3;
                                 check_typeclass_instance_attribute env0 se3;
                                 ([se3], [], env0))))))
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun se ->
      let env = env0 in
      let se1 =
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_fail uu___ -> se
        | uu___ -> tc_decl_attributes env se in
      FStar_TypeChecker_Util.check_sigelt_quals env se1;
      proc_check_with se1.FStar_Syntax_Syntax.sigattrs
        (fun uu___1 ->
           let r = se1.FStar_Syntax_Syntax.sigrng in
           let se2 =
             let uu___2 = FStar_Options.record_options () in
             if uu___2 then store_sigopts se1 else se1 in
           match se2.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail
               { FStar_Syntax_Syntax.errs = uu___2;
                 FStar_Syntax_Syntax.fail_in_lax = false;
                 FStar_Syntax_Syntax.ses1 = uu___3;_}
               when
               (let uu___4 = FStar_TypeChecker_Env.should_verify env in
                Prims.op_Negation uu___4) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail
               { FStar_Syntax_Syntax.errs = expected_errors;
                 FStar_Syntax_Syntax.fail_in_lax = lax;
                 FStar_Syntax_Syntax.ses1 = ses;_}
               ->
               let env' =
                 if lax
                 then
                   {
                     FStar_TypeChecker_Env.solver =
                       (env.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (env.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (env.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (env.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (env.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (env.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (env.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (env.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (env.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (env.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (env.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (env.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (env.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (env.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (env.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (env.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (env.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (env.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (env.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (env.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (env.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (env.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (env.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (env.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.intactics =
                       (env.FStar_TypeChecker_Env.intactics);
                     FStar_TypeChecker_Env.tc_term =
                       (env.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStar_TypeChecker_Env.universe_of =
                       (env.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStar_TypeChecker_Env.teq_nosmt_force =
                       (env.FStar_TypeChecker_Env.teq_nosmt_force);
                     FStar_TypeChecker_Env.subtype_nosmt_force =
                       (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (env.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (env.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (env.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (env.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (env.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (env.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (env.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (env.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (env.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (env.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (env.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (env.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (env.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                     FStar_TypeChecker_Env.unif_allow_ref_guards =
                       (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                     FStar_TypeChecker_Env.erase_erasable_args =
                       (env.FStar_TypeChecker_Env.erase_erasable_args);
                     FStar_TypeChecker_Env.core_check =
                       (env.FStar_TypeChecker_Env.core_check)
                   }
                 else env in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure" in
               ((let uu___3 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       FStar_Compiler_List.map
                         FStar_Compiler_Util.string_of_int expected_errors in
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_String.concat "; ") uu___5 in
                   FStar_Compiler_Util.print1 ">> Expecting errors: [%s]\n"
                     uu___4
                 else ());
                (let uu___3 =
                   FStar_Errors.catch_errors
                     (fun uu___4 ->
                        FStar_Options.with_saved_options
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 FStar_Compiler_Effect.op_Bang tc_decls_knot in
                               FStar_Compiler_Util.must uu___7 in
                             uu___6 env'1 ses)) in
                 match uu___3 with
                 | (errs, uu___4) ->
                     ((let uu___6 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low) in
                       if uu___6
                       then
                         (FStar_Compiler_Util.print_string
                            ">> Got issues: [\n";
                          FStar_Compiler_List.iter FStar_Errors.print_issue
                            errs;
                          FStar_Compiler_Util.print_string ">>]\n")
                       else ());
                      (let uu___6 =
                         FStar_TypeChecker_Env.pop env'1 "expect_failure" in
                       let actual_errors =
                         FStar_Compiler_List.concatMap
                           (fun i ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs in
                       (match errs with
                        | [] ->
                            (FStar_Compiler_List.iter
                               FStar_Errors.print_issue errs;
                             FStar_Errors.log_issue
                               se2.FStar_Syntax_Syntax.sigrng
                               (FStar_Errors_Codes.Error_DidNotFail,
                                 "This top-level definition was expected to fail, but it succeeded"))
                        | uu___8 ->
                            if expected_errors <> []
                            then
                              let uu___9 =
                                FStar_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors in
                              (match uu___9 with
                               | FStar_Pervasives_Native.None -> ()
                               | FStar_Pervasives_Native.Some (e, n1, n2) ->
                                   (FStar_Compiler_List.iter
                                      FStar_Errors.print_issue errs;
                                    (let uu___11 =
                                       let uu___12 =
                                         let uu___13 =
                                           (FStar_Common.string_of_list ())
                                             FStar_Compiler_Util.string_of_int
                                             expected_errors in
                                         let uu___14 =
                                           (FStar_Common.string_of_list ())
                                             FStar_Compiler_Util.string_of_int
                                             actual_errors in
                                         let uu___15 =
                                           FStar_Compiler_Util.string_of_int
                                             e in
                                         let uu___16 =
                                           FStar_Compiler_Util.string_of_int
                                             n2 in
                                         let uu___17 =
                                           FStar_Compiler_Util.string_of_int
                                             n1 in
                                         FStar_Compiler_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu___13 uu___14 uu___15 uu___16
                                           uu___17 in
                                       (FStar_Errors_Codes.Error_DidNotFail,
                                         uu___12) in
                                     FStar_Errors.log_issue
                                       se2.FStar_Syntax_Syntax.sigrng uu___11)))
                            else ());
                       ([], [], env)))))
           | FStar_Syntax_Syntax.Sig_bundle
               { FStar_Syntax_Syntax.ses = ses;
                 FStar_Syntax_Syntax.lids = lids;_}
               ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
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
                                    FStar_TypeChecker_Env.solver =
                                      (env1.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (env1.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (env1.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (env1.FStar_TypeChecker_Env.gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (env1.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (env1.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (env1.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (env1.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (env1.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (env1.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (env1.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (env1.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (env1.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (env1.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (env1.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (env1.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (env1.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (env1.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (env1.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax = true;
                                    FStar_TypeChecker_Env.lax_universes =
                                      (env1.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 = true;
                                    FStar_TypeChecker_Env.failhard =
                                      (env1.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (env1.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (env1.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.tc_term =
                                      (env1.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (env1.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (env1.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (env1.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (env1.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (env1.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (env1.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (env1.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (env1.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (env1.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (env1.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (env1.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (env1.FStar_TypeChecker_Env.core_check)
                                  } ses se2.FStar_Syntax_Syntax.sigquals
                                  se2.FStar_Syntax_Syntax.sigattrs lids in
                              FStar_Compiler_Effect.op_Bar_Greater uu___6
                                FStar_Pervasives_Native.fst in
                            FStar_Compiler_Effect.op_Bar_Greater uu___5
                              (FStar_TypeChecker_Normalize.elim_uvars env1) in
                          FStar_Compiler_Effect.op_Bar_Greater uu___4
                            FStar_Syntax_Util.ses_of_sigbundle in
                        (let uu___5 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "TwoPhases") in
                         if uu___5
                         then
                           let uu___6 =
                             FStar_Syntax_Print.sigelt_to_string
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_bundle
                                      {
                                        FStar_Syntax_Syntax.ses = ses2;
                                        FStar_Syntax_Syntax.lids = lids
                                      });
                                 FStar_Syntax_Syntax.sigrng =
                                   (se2.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (se2.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (se2.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (se2.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (se2.FStar_Syntax_Syntax.sigopts)
                               } in
                           FStar_Compiler_Util.print1
                             "Inductive after phase 1: %s\n" uu___6
                         else ());
                        ses2)
                 else ses in
               let uu___2 =
                 tc_inductive env1 ses1 se2.FStar_Syntax_Syntax.sigquals
                   se2.FStar_Syntax_Syntax.sigattrs lids in
               (match uu___2 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      {
                        FStar_Syntax_Syntax.sigel =
                          (sigbndle.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (sigbndle.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (sigbndle.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (sigbndle.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se2.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (sigbndle.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu___2 =
                       let uu___3 =
                         FStar_Compiler_Effect.op_Bar_Greater
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd in
                       FStar_Compiler_Effect.op_Bar_Greater uu___3
                         FStar_Syntax_Subst.compress in
                     (match uu___2 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown;
                          FStar_Syntax_Syntax.pos = uu___3;
                          FStar_Syntax_Syntax.vars = uu___4;
                          FStar_Syntax_Syntax.hash_code = uu___5;_} -> true
                      | uu___3 -> false)
                 | uu___2 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu___2 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu___2 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [{
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (se2.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (se2.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (se2.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (se2.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (se2.FStar_Syntax_Syntax.sigopts)
                             };
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [{
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_new_effect ne1);
                               FStar_Syntax_Syntax.sigrng =
                                 (se2.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (se2.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (se2.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (se2.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (se2.FStar_Syntax_Syntax.sigopts)
                             }] in
                      let effect_and_lift_ses1 =
                        FStar_Compiler_Effect.op_Bar_Greater
                          effect_and_lift_ses
                          (FStar_Compiler_List.map
                             (fun sigelt ->
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (sigelt.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (sigelt.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (sigelt.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (let uu___3 =
                                       sigelt.FStar_Syntax_Syntax.sigmeta in
                                     {
                                       FStar_Syntax_Syntax.sigmeta_active =
                                         (uu___3.FStar_Syntax_Syntax.sigmeta_active);
                                       FStar_Syntax_Syntax.sigmeta_fact_db_ids
                                         =
                                         (uu___3.FStar_Syntax_Syntax.sigmeta_fact_db_ids);
                                       FStar_Syntax_Syntax.sigmeta_admit =
                                         true
                                     });
                                  FStar_Syntax_Syntax.sigattrs =
                                    (sigelt.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (sigelt.FStar_Syntax_Syntax.sigopts)
                                })) in
                      ([],
                        (FStar_Compiler_List.op_At ses effect_and_lift_ses1),
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
                                   FStar_TypeChecker_TcEffect.tc_eff_decl
                                     {
                                       FStar_TypeChecker_Env.solver =
                                         (env.FStar_TypeChecker_Env.solver);
                                       FStar_TypeChecker_Env.range =
                                         (env.FStar_TypeChecker_Env.range);
                                       FStar_TypeChecker_Env.curmodule =
                                         (env.FStar_TypeChecker_Env.curmodule);
                                       FStar_TypeChecker_Env.gamma =
                                         (env.FStar_TypeChecker_Env.gamma);
                                       FStar_TypeChecker_Env.gamma_sig =
                                         (env.FStar_TypeChecker_Env.gamma_sig);
                                       FStar_TypeChecker_Env.gamma_cache =
                                         (env.FStar_TypeChecker_Env.gamma_cache);
                                       FStar_TypeChecker_Env.modules =
                                         (env.FStar_TypeChecker_Env.modules);
                                       FStar_TypeChecker_Env.expected_typ =
                                         (env.FStar_TypeChecker_Env.expected_typ);
                                       FStar_TypeChecker_Env.sigtab =
                                         (env.FStar_TypeChecker_Env.sigtab);
                                       FStar_TypeChecker_Env.attrtab =
                                         (env.FStar_TypeChecker_Env.attrtab);
                                       FStar_TypeChecker_Env.instantiate_imp
                                         =
                                         (env.FStar_TypeChecker_Env.instantiate_imp);
                                       FStar_TypeChecker_Env.effects =
                                         (env.FStar_TypeChecker_Env.effects);
                                       FStar_TypeChecker_Env.generalize =
                                         (env.FStar_TypeChecker_Env.generalize);
                                       FStar_TypeChecker_Env.letrecs =
                                         (env.FStar_TypeChecker_Env.letrecs);
                                       FStar_TypeChecker_Env.top_level =
                                         (env.FStar_TypeChecker_Env.top_level);
                                       FStar_TypeChecker_Env.check_uvars =
                                         (env.FStar_TypeChecker_Env.check_uvars);
                                       FStar_TypeChecker_Env.use_eq_strict =
                                         (env.FStar_TypeChecker_Env.use_eq_strict);
                                       FStar_TypeChecker_Env.is_iface =
                                         (env.FStar_TypeChecker_Env.is_iface);
                                       FStar_TypeChecker_Env.admit =
                                         (env.FStar_TypeChecker_Env.admit);
                                       FStar_TypeChecker_Env.lax = true;
                                       FStar_TypeChecker_Env.lax_universes =
                                         (env.FStar_TypeChecker_Env.lax_universes);
                                       FStar_TypeChecker_Env.phase1 = true;
                                       FStar_TypeChecker_Env.failhard =
                                         (env.FStar_TypeChecker_Env.failhard);
                                       FStar_TypeChecker_Env.nosynth =
                                         (env.FStar_TypeChecker_Env.nosynth);
                                       FStar_TypeChecker_Env.uvar_subtyping =
                                         (env.FStar_TypeChecker_Env.uvar_subtyping);
                                       FStar_TypeChecker_Env.intactics =
                                         (env.FStar_TypeChecker_Env.intactics);
                                       FStar_TypeChecker_Env.tc_term =
                                         (env.FStar_TypeChecker_Env.tc_term);
                                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                         =
                                         (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                       FStar_TypeChecker_Env.universe_of =
                                         (env.FStar_TypeChecker_Env.universe_of);
                                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                         =
                                         (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                       FStar_TypeChecker_Env.teq_nosmt_force
                                         =
                                         (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                       FStar_TypeChecker_Env.subtype_nosmt_force
                                         =
                                         (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                         =
                                         (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                       FStar_TypeChecker_Env.normalized_eff_names
                                         =
                                         (env.FStar_TypeChecker_Env.normalized_eff_names);
                                       FStar_TypeChecker_Env.fv_delta_depths
                                         =
                                         (env.FStar_TypeChecker_Env.fv_delta_depths);
                                       FStar_TypeChecker_Env.proof_ns =
                                         (env.FStar_TypeChecker_Env.proof_ns);
                                       FStar_TypeChecker_Env.synth_hook =
                                         (env.FStar_TypeChecker_Env.synth_hook);
                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                         =
                                         (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                       FStar_TypeChecker_Env.splice =
                                         (env.FStar_TypeChecker_Env.splice);
                                       FStar_TypeChecker_Env.mpreprocess =
                                         (env.FStar_TypeChecker_Env.mpreprocess);
                                       FStar_TypeChecker_Env.postprocess =
                                         (env.FStar_TypeChecker_Env.postprocess);
                                       FStar_TypeChecker_Env.identifier_info
                                         =
                                         (env.FStar_TypeChecker_Env.identifier_info);
                                       FStar_TypeChecker_Env.tc_hooks =
                                         (env.FStar_TypeChecker_Env.tc_hooks);
                                       FStar_TypeChecker_Env.dsenv =
                                         (env.FStar_TypeChecker_Env.dsenv);
                                       FStar_TypeChecker_Env.nbe =
                                         (env.FStar_TypeChecker_Env.nbe);
                                       FStar_TypeChecker_Env.strict_args_tab
                                         =
                                         (env.FStar_TypeChecker_Env.strict_args_tab);
                                       FStar_TypeChecker_Env.erasable_types_tab
                                         =
                                         (env.FStar_TypeChecker_Env.erasable_types_tab);
                                       FStar_TypeChecker_Env.enable_defer_to_tac
                                         =
                                         (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                       FStar_TypeChecker_Env.unif_allow_ref_guards
                                         =
                                         (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                       FStar_TypeChecker_Env.erase_erasable_args
                                         =
                                         (env.FStar_TypeChecker_Env.erase_erasable_args);
                                       FStar_TypeChecker_Env.core_check =
                                         (env.FStar_TypeChecker_Env.core_check)
                                     } ne se2.FStar_Syntax_Syntax.sigquals
                                     se2.FStar_Syntax_Syntax.sigattrs in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___7
                                   (fun ne3 ->
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          (FStar_Syntax_Syntax.Sig_new_effect
                                             ne3);
                                        FStar_Syntax_Syntax.sigrng =
                                          (se2.FStar_Syntax_Syntax.sigrng);
                                        FStar_Syntax_Syntax.sigquals =
                                          (se2.FStar_Syntax_Syntax.sigquals);
                                        FStar_Syntax_Syntax.sigmeta =
                                          (se2.FStar_Syntax_Syntax.sigmeta);
                                        FStar_Syntax_Syntax.sigattrs =
                                          (se2.FStar_Syntax_Syntax.sigattrs);
                                        FStar_Syntax_Syntax.sigopts =
                                          (se2.FStar_Syntax_Syntax.sigopts)
                                      }) in
                               FStar_Compiler_Effect.op_Bar_Greater uu___6
                                 (FStar_TypeChecker_Normalize.elim_uvars env) in
                             FStar_Compiler_Effect.op_Bar_Greater uu___5
                               FStar_Syntax_Util.eff_decl_of_new_effect in
                           (let uu___6 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "TwoPhases") in
                            if uu___6
                            then
                              let uu___7 =
                                FStar_Syntax_Print.sigelt_to_string
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_new_effect ne2);
                                    FStar_Syntax_Syntax.sigrng =
                                      (se2.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (se2.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (se2.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (se2.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (se2.FStar_Syntax_Syntax.sigopts)
                                  } in
                              FStar_Compiler_Util.print1
                                "Effect decl after phase 1: %s\n" uu___7
                            else ());
                           ne2)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se2.FStar_Syntax_Syntax.sigquals
                      se2.FStar_Syntax_Syntax.sigattrs in
                  let se3 =
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (se2.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (se2.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (se2.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (se2.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (se2.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se3], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se3 =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (se2.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (se2.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (se2.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (se2.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (se2.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se3], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev
               { FStar_Syntax_Syntax.lid4 = lid;
                 FStar_Syntax_Syntax.us4 = uvs;
                 FStar_Syntax_Syntax.bs2 = tps;
                 FStar_Syntax_Syntax.comp1 = c;
                 FStar_Syntax_Syntax.cflags = flags;_}
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
                              FStar_TypeChecker_TcEffect.tc_effect_abbrev
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (env.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (env.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (env.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (env.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (env.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (env.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (env.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (env.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (env.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (env.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (env.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (env.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (env.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (env.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (env.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (env.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (env.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (env.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (env.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax = true;
                                  FStar_TypeChecker_Env.lax_universes =
                                    (env.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 = true;
                                  FStar_TypeChecker_Env.failhard =
                                    (env.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (env.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (env.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.intactics =
                                    (env.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.tc_term =
                                    (env.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (env.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (env.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (env.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (env.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (env.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (env.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (env.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (env.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (env.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (env.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (env.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (env.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (env.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (env.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (env.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (env.FStar_TypeChecker_Env.core_check)
                                } (lid, uvs, tps, c) r in
                            FStar_Compiler_Effect.op_Bar_Greater uu___7
                              (fun uu___8 ->
                                 match uu___8 with
                                 | (lid1, uvs1, tps1, c1) ->
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_effect_abbrev
                                            {
                                              FStar_Syntax_Syntax.lid4 = lid1;
                                              FStar_Syntax_Syntax.us4 = uvs1;
                                              FStar_Syntax_Syntax.bs2 = tps1;
                                              FStar_Syntax_Syntax.comp1 = c1;
                                              FStar_Syntax_Syntax.cflags =
                                                flags
                                            });
                                       FStar_Syntax_Syntax.sigrng =
                                         (se2.FStar_Syntax_Syntax.sigrng);
                                       FStar_Syntax_Syntax.sigquals =
                                         (se2.FStar_Syntax_Syntax.sigquals);
                                       FStar_Syntax_Syntax.sigmeta =
                                         (se2.FStar_Syntax_Syntax.sigmeta);
                                       FStar_Syntax_Syntax.sigattrs =
                                         (se2.FStar_Syntax_Syntax.sigattrs);
                                       FStar_Syntax_Syntax.sigopts =
                                         (se2.FStar_Syntax_Syntax.sigopts)
                                     }) in
                          FStar_Compiler_Effect.op_Bar_Greater uu___6
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_Compiler_Effect.op_Bar_Greater uu___5
                          (fun se3 ->
                             match se3.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_effect_abbrev
                                 { FStar_Syntax_Syntax.lid4 = lid1;
                                   FStar_Syntax_Syntax.us4 = uvs1;
                                   FStar_Syntax_Syntax.bs2 = tps1;
                                   FStar_Syntax_Syntax.comp1 = c1;
                                   FStar_Syntax_Syntax.cflags = uu___6;_}
                                 -> (lid1, uvs1, tps1, c1)
                             | uu___6 ->
                                 failwith
                                   "Did not expect Sig_effect_abbrev to not be one after phase 1"))
                 else (lid, uvs, tps, c) in
               (match uu___2 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu___3 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu___3 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se3 =
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  {
                                    FStar_Syntax_Syntax.lid4 = lid2;
                                    FStar_Syntax_Syntax.us4 = uvs2;
                                    FStar_Syntax_Syntax.bs2 = tps2;
                                    FStar_Syntax_Syntax.comp1 = c2;
                                    FStar_Syntax_Syntax.cflags = flags
                                  });
                             FStar_Syntax_Syntax.sigrng =
                               (se2.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (se2.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (se2.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (se2.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (se2.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se3], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ uu___2 when
               FStar_Compiler_Effect.op_Bar_Greater
                 se2.FStar_Syntax_Syntax.sigquals
                 (FStar_Compiler_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu___4 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let uu___2 when
               FStar_Compiler_Effect.op_Bar_Greater
                 se2.FStar_Syntax_Syntax.sigquals
                 (FStar_Compiler_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu___4 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ
               { FStar_Syntax_Syntax.lid2 = lid;
                 FStar_Syntax_Syntax.us2 = uvs; FStar_Syntax_Syntax.t2 = t;_}
               ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu___3 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_Ident.string_of_lid lid in
                       FStar_Compiler_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu___6 in
                     (FStar_Errors_Codes.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu___5) in
                   FStar_Errors.raise_error uu___4 r
                 else ());
                (let uu___3 =
                   let uu___4 = do_two_phases env1 in
                   if uu___4
                   then
                     run_phase1
                       (fun uu___5 ->
                          let uu___6 =
                            tc_declare_typ
                              {
                                FStar_TypeChecker_Env.solver =
                                  (env1.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (env1.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (env1.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (env1.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (env1.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (env1.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (env1.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (env1.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (env1.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (env1.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (env1.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (env1.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (env1.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (env1.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (env1.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (env1.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (env1.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (env1.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (env1.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (env1.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (env1.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (env1.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.intactics =
                                  (env1.FStar_TypeChecker_Env.intactics);
                                FStar_TypeChecker_Env.tc_term =
                                  (env1.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                  =
                                  (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                FStar_TypeChecker_Env.universe_of =
                                  (env1.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                  =
                                  (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                FStar_TypeChecker_Env.teq_nosmt_force =
                                  (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                FStar_TypeChecker_Env.subtype_nosmt_force =
                                  (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (env1.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (env1.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (env1.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (env1.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (env1.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (env1.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (env1.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (env1.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (env1.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (env1.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                FStar_TypeChecker_Env.unif_allow_ref_guards =
                                  (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                FStar_TypeChecker_Env.erase_erasable_args =
                                  (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                FStar_TypeChecker_Env.core_check =
                                  (env1.FStar_TypeChecker_Env.core_check)
                              } (uvs, t) se2.FStar_Syntax_Syntax.sigrng in
                          match uu___6 with
                          | (uvs1, t1) ->
                              ((let uu___8 =
                                  FStar_Compiler_Effect.op_Less_Bar
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "TwoPhases") in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu___10 =
                                    FStar_Syntax_Print.univ_names_to_string
                                      uvs1 in
                                  FStar_Compiler_Util.print2
                                    "Val declaration after phase 1: %s and uvs: %s\n"
                                    uu___9 uu___10
                                else ());
                               (uvs1, t1)))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_declare_typ env1 (uvs1, t1)
                         se2.FStar_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([{
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_declare_typ
                                   {
                                     FStar_Syntax_Syntax.lid2 = lid;
                                     FStar_Syntax_Syntax.us2 = uvs2;
                                     FStar_Syntax_Syntax.t2 = t2
                                   });
                              FStar_Syntax_Syntax.sigrng =
                                (se2.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (se2.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (se2.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (se2.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (se2.FStar_Syntax_Syntax.sigopts)
                            }], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume
               { FStar_Syntax_Syntax.lid3 = lid;
                 FStar_Syntax_Syntax.us3 = uvs;
                 FStar_Syntax_Syntax.phi1 = t;_}
               ->
               (if
                  Prims.op_Negation
                    (FStar_Compiler_List.contains
                       FStar_Syntax_Syntax.InternalAssumption
                       se2.FStar_Syntax_Syntax.sigquals)
                then
                  (let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Print.lid_to_string lid in
                       FStar_Compiler_Util.format1
                         "Admitting a top-level assumption %s" uu___5 in
                     (FStar_Errors_Codes.Warning_WarnOnUse, uu___4) in
                   FStar_Errors.log_issue r uu___3)
                else ();
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu___3 =
                   let uu___4 = do_two_phases env1 in
                   if uu___4
                   then
                     run_phase1
                       (fun uu___5 ->
                          let uu___6 =
                            tc_assume
                              {
                                FStar_TypeChecker_Env.solver =
                                  (env1.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (env1.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (env1.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (env1.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (env1.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (env1.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (env1.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (env1.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (env1.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (env1.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (env1.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (env1.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (env1.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (env1.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (env1.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (env1.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (env1.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (env1.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (env1.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (env1.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (env1.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (env1.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.intactics =
                                  (env1.FStar_TypeChecker_Env.intactics);
                                FStar_TypeChecker_Env.tc_term =
                                  (env1.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                  =
                                  (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                FStar_TypeChecker_Env.universe_of =
                                  (env1.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                  =
                                  (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                FStar_TypeChecker_Env.teq_nosmt_force =
                                  (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                FStar_TypeChecker_Env.subtype_nosmt_force =
                                  (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (env1.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (env1.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (env1.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (env1.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (env1.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (env1.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (env1.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (env1.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (env1.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (env1.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                FStar_TypeChecker_Env.unif_allow_ref_guards =
                                  (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                FStar_TypeChecker_Env.erase_erasable_args =
                                  (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                FStar_TypeChecker_Env.core_check =
                                  (env1.FStar_TypeChecker_Env.core_check)
                              } (uvs, t) se2.FStar_Syntax_Syntax.sigrng in
                          match uu___6 with
                          | (uvs1, t1) ->
                              ((let uu___8 =
                                  FStar_Compiler_Effect.op_Less_Bar
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "TwoPhases") in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  let uu___10 =
                                    FStar_Syntax_Print.univ_names_to_string
                                      uvs1 in
                                  FStar_Compiler_Util.print2
                                    "Assume after phase 1: %s and uvs: %s\n"
                                    uu___9 uu___10
                                else ());
                               (uvs1, t1)))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_assume env1 (uvs1, t1)
                         se2.FStar_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([{
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_assume
                                   {
                                     FStar_Syntax_Syntax.lid3 = lid;
                                     FStar_Syntax_Syntax.us3 = uvs2;
                                     FStar_Syntax_Syntax.phi1 = t2
                                   });
                              FStar_Syntax_Syntax.sigrng =
                                (se2.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (se2.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (se2.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (se2.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (se2.FStar_Syntax_Syntax.sigopts)
                            }], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice
               { FStar_Syntax_Syntax.is_typed = is_typed;
                 FStar_Syntax_Syntax.lids2 = lids;
                 FStar_Syntax_Syntax.tac = t;_}
               ->
               ((let uu___3 = FStar_Options.debug_any () in
                 if uu___3
                 then
                   let uu___4 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu___5 = FStar_Syntax_Print.term_to_string t in
                   let uu___6 = FStar_Compiler_Util.string_of_bool is_typed in
                   FStar_Compiler_Util.print3
                     "%s: Found splice of (%s) with is_typed: %s\n" uu___4
                     uu___5 uu___6
                 else ());
                (let ses =
                   env.FStar_TypeChecker_Env.splice env is_typed lids t
                     se2.FStar_Syntax_Syntax.sigrng in
                 let ses1 =
                   if is_typed
                   then
                     let sigquals =
                       match se2.FStar_Syntax_Syntax.sigquals with
                       | [] -> [FStar_Syntax_Syntax.Visible_default]
                       | qs -> qs in
                     FStar_Compiler_List.map
                       (fun sp ->
                          {
                            FStar_Syntax_Syntax.sigel =
                              (sp.FStar_Syntax_Syntax.sigel);
                            FStar_Syntax_Syntax.sigrng =
                              (sp.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals = sigquals;
                            FStar_Syntax_Syntax.sigmeta =
                              (sp.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (se2.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (sp.FStar_Syntax_Syntax.sigopts)
                          }) ses
                   else ses in
                 let dsenv =
                   FStar_Compiler_List.fold_left
                     FStar_Syntax_DsEnv.push_sigelt_force
                     env.FStar_TypeChecker_Env.dsenv ses1 in
                 let env1 =
                   {
                     FStar_TypeChecker_Env.solver =
                       (env.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (env.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (env.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (env.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (env.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (env.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (env.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (env.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (env.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (env.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (env.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (env.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (env.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (env.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (env.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (env.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (env.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (env.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (env.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax =
                       (env.FStar_TypeChecker_Env.lax);
                     FStar_TypeChecker_Env.lax_universes =
                       (env.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (env.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (env.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (env.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (env.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.intactics =
                       (env.FStar_TypeChecker_Env.intactics);
                     FStar_TypeChecker_Env.tc_term =
                       (env.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                       (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                     FStar_TypeChecker_Env.universe_of =
                       (env.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                       =
                       (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                     FStar_TypeChecker_Env.teq_nosmt_force =
                       (env.FStar_TypeChecker_Env.teq_nosmt_force);
                     FStar_TypeChecker_Env.subtype_nosmt_force =
                       (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (env.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (env.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (env.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (env.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (env.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (env.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (env.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (env.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (env.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv = dsenv;
                     FStar_TypeChecker_Env.nbe =
                       (env.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (env.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (env.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                     FStar_TypeChecker_Env.unif_allow_ref_guards =
                       (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                     FStar_TypeChecker_Env.erase_erasable_args =
                       (env.FStar_TypeChecker_Env.erase_erasable_args);
                     FStar_TypeChecker_Env.core_check =
                       (env.FStar_TypeChecker_Env.core_check)
                   } in
                 (let uu___4 =
                    FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                  if uu___4
                  then
                    let uu___5 =
                      let uu___6 =
                        FStar_Compiler_List.map
                          FStar_Syntax_Print.sigelt_to_string ses1 in
                      FStar_Compiler_Effect.op_Less_Bar
                        (FStar_String.concat "\n") uu___6 in
                    FStar_Compiler_Util.print1
                      "Splice returned sigelts {\n%s\n}\n" uu___5
                  else ());
                 if is_typed then (ses1, [], env1) else ([], ses1, env1)))
           | FStar_Syntax_Syntax.Sig_let
               { FStar_Syntax_Syntax.lbs1 = lbs;
                 FStar_Syntax_Syntax.lids1 = lids;_}
               ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStar_TypeChecker_Env.current_module env in
                   FStar_Ident.string_of_lid uu___4 in
                 FStar_Pervasives_Native.Some uu___3 in
               FStar_Profiling.profile
                 (fun uu___3 -> tc_sig_let env r se2 lbs lids) uu___2
                 "FStar.TypeChecker.Tc.tc_sig_let"
           | FStar_Syntax_Syntax.Sig_polymonadic_bind
               { FStar_Syntax_Syntax.m_lid = m;
                 FStar_Syntax_Syntax.n_lid = n;
                 FStar_Syntax_Syntax.p_lid = p; FStar_Syntax_Syntax.tm3 = t;
                 FStar_Syntax_Syntax.typ = uu___2;
                 FStar_Syntax_Syntax.kind1 = uu___3;_}
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
                                FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (env.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (env.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (env.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (env.FStar_TypeChecker_Env.gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (env.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (env.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (env.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (env.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (env.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (env.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (env.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (env.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (env.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (env.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (env.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (env.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (env.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (env.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (env.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax = true;
                                    FStar_TypeChecker_Env.lax_universes =
                                      (env.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 = true;
                                    FStar_TypeChecker_Env.failhard =
                                      (env.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (env.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (env.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (env.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.tc_term =
                                      (env.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (env.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (env.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (env.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (env.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (env.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (env.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (env.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (env.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (env.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (env.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (env.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (env.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (env.FStar_TypeChecker_Env.core_check)
                                  } m n p t in
                              FStar_Compiler_Effect.op_Bar_Greater uu___9
                                (fun uu___10 ->
                                   match uu___10 with
                                   | (t2, ty, uu___11) ->
                                       {
                                         FStar_Syntax_Syntax.sigel =
                                           (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                              {
                                                FStar_Syntax_Syntax.m_lid = m;
                                                FStar_Syntax_Syntax.n_lid = n;
                                                FStar_Syntax_Syntax.p_lid = p;
                                                FStar_Syntax_Syntax.tm3 = t2;
                                                FStar_Syntax_Syntax.typ = ty;
                                                FStar_Syntax_Syntax.kind1 =
                                                  FStar_Pervasives_Native.None
                                              });
                                         FStar_Syntax_Syntax.sigrng =
                                           (se2.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           (se2.FStar_Syntax_Syntax.sigquals);
                                         FStar_Syntax_Syntax.sigmeta =
                                           (se2.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (se2.FStar_Syntax_Syntax.sigattrs);
                                         FStar_Syntax_Syntax.sigopts =
                                           (se2.FStar_Syntax_Syntax.sigopts)
                                       }) in
                            FStar_Compiler_Effect.op_Bar_Greater uu___8
                              (FStar_TypeChecker_Normalize.elim_uvars env) in
                          FStar_Compiler_Effect.op_Bar_Greater uu___7
                            (fun se3 ->
                               match se3.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_polymonadic_bind
                                   { FStar_Syntax_Syntax.m_lid = uu___8;
                                     FStar_Syntax_Syntax.n_lid = uu___9;
                                     FStar_Syntax_Syntax.p_lid = uu___10;
                                     FStar_Syntax_Syntax.tm3 = t2;
                                     FStar_Syntax_Syntax.typ = ty;
                                     FStar_Syntax_Syntax.kind1 = uu___11;_}
                                   -> (t2, ty)
                               | uu___8 ->
                                   failwith
                                     "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                        match uu___6 with
                        | (t2, ty) ->
                            ((let uu___8 =
                                FStar_Compiler_Effect.op_Less_Bar
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "TwoPhases") in
                              if uu___8
                              then
                                let uu___9 =
                                  FStar_Syntax_Print.sigelt_to_string
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                           {
                                             FStar_Syntax_Syntax.m_lid = m;
                                             FStar_Syntax_Syntax.n_lid = n;
                                             FStar_Syntax_Syntax.p_lid = p;
                                             FStar_Syntax_Syntax.tm3 = t2;
                                             FStar_Syntax_Syntax.typ = ty;
                                             FStar_Syntax_Syntax.kind1 =
                                               FStar_Pervasives_Native.None
                                           });
                                      FStar_Syntax_Syntax.sigrng =
                                        (se2.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals =
                                        (se2.FStar_Syntax_Syntax.sigquals);
                                      FStar_Syntax_Syntax.sigmeta =
                                        (se2.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (se2.FStar_Syntax_Syntax.sigattrs);
                                      FStar_Syntax_Syntax.sigopts =
                                        (se2.FStar_Syntax_Syntax.sigopts)
                                    } in
                                FStar_Compiler_Util.print1
                                  "Polymonadic bind after phase 1: %s\n"
                                  uu___9
                              else ());
                             t2))
                 else t in
               let uu___4 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu___4 with
                | (t2, ty, k) ->
                    let se3 =
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             {
                               FStar_Syntax_Syntax.m_lid = m;
                               FStar_Syntax_Syntax.n_lid = n;
                               FStar_Syntax_Syntax.p_lid = p;
                               FStar_Syntax_Syntax.tm3 = t2;
                               FStar_Syntax_Syntax.typ = ty;
                               FStar_Syntax_Syntax.kind1 =
                                 (FStar_Pervasives_Native.Some k)
                             });
                        FStar_Syntax_Syntax.sigrng =
                          (se2.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (se2.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (se2.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se2.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (se2.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se3], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
               { FStar_Syntax_Syntax.m_lid1 = m;
                 FStar_Syntax_Syntax.n_lid1 = n; FStar_Syntax_Syntax.tm4 = t;
                 FStar_Syntax_Syntax.typ1 = uu___2;
                 FStar_Syntax_Syntax.kind2 = uu___3;_}
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
                                FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (env.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (env.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (env.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      (env.FStar_TypeChecker_Env.gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (env.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (env.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (env.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (env.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (env.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (env.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (env.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (env.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (env.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (env.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (env.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (env.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (env.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (env.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (env.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax = true;
                                    FStar_TypeChecker_Env.lax_universes =
                                      (env.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 = true;
                                    FStar_TypeChecker_Env.failhard =
                                      (env.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (env.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (env.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (env.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.tc_term =
                                      (env.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (env.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (env.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (env.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (env.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (env.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (env.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (env.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (env.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (env.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (env.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (env.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (env.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (env.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (env.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (env.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (env.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (env.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (env.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (env.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (env.FStar_TypeChecker_Env.core_check)
                                  } m n t in
                              FStar_Compiler_Effect.op_Bar_Greater uu___9
                                (fun uu___10 ->
                                   match uu___10 with
                                   | (t2, ty, uu___11) ->
                                       {
                                         FStar_Syntax_Syntax.sigel =
                                           (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                              {
                                                FStar_Syntax_Syntax.m_lid1 =
                                                  m;
                                                FStar_Syntax_Syntax.n_lid1 =
                                                  n;
                                                FStar_Syntax_Syntax.tm4 = t2;
                                                FStar_Syntax_Syntax.typ1 = ty;
                                                FStar_Syntax_Syntax.kind2 =
                                                  FStar_Pervasives_Native.None
                                              });
                                         FStar_Syntax_Syntax.sigrng =
                                           (se2.FStar_Syntax_Syntax.sigrng);
                                         FStar_Syntax_Syntax.sigquals =
                                           (se2.FStar_Syntax_Syntax.sigquals);
                                         FStar_Syntax_Syntax.sigmeta =
                                           (se2.FStar_Syntax_Syntax.sigmeta);
                                         FStar_Syntax_Syntax.sigattrs =
                                           (se2.FStar_Syntax_Syntax.sigattrs);
                                         FStar_Syntax_Syntax.sigopts =
                                           (se2.FStar_Syntax_Syntax.sigopts)
                                       }) in
                            FStar_Compiler_Effect.op_Bar_Greater uu___8
                              (FStar_TypeChecker_Normalize.elim_uvars env) in
                          FStar_Compiler_Effect.op_Bar_Greater uu___7
                            (fun se3 ->
                               match se3.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                   { FStar_Syntax_Syntax.m_lid1 = uu___8;
                                     FStar_Syntax_Syntax.n_lid1 = uu___9;
                                     FStar_Syntax_Syntax.tm4 = t2;
                                     FStar_Syntax_Syntax.typ1 = ty;
                                     FStar_Syntax_Syntax.kind2 = uu___10;_}
                                   -> (t2, ty)
                               | uu___8 ->
                                   failwith
                                     "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                        match uu___6 with
                        | (t2, ty) ->
                            ((let uu___8 =
                                FStar_Compiler_Effect.op_Less_Bar
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "TwoPhases") in
                              if uu___8
                              then
                                let uu___9 =
                                  FStar_Syntax_Print.sigelt_to_string
                                    {
                                      FStar_Syntax_Syntax.sigel =
                                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                           {
                                             FStar_Syntax_Syntax.m_lid1 = m;
                                             FStar_Syntax_Syntax.n_lid1 = n;
                                             FStar_Syntax_Syntax.tm4 = t2;
                                             FStar_Syntax_Syntax.typ1 = ty;
                                             FStar_Syntax_Syntax.kind2 =
                                               FStar_Pervasives_Native.None
                                           });
                                      FStar_Syntax_Syntax.sigrng =
                                        (se2.FStar_Syntax_Syntax.sigrng);
                                      FStar_Syntax_Syntax.sigquals =
                                        (se2.FStar_Syntax_Syntax.sigquals);
                                      FStar_Syntax_Syntax.sigmeta =
                                        (se2.FStar_Syntax_Syntax.sigmeta);
                                      FStar_Syntax_Syntax.sigattrs =
                                        (se2.FStar_Syntax_Syntax.sigattrs);
                                      FStar_Syntax_Syntax.sigopts =
                                        (se2.FStar_Syntax_Syntax.sigopts)
                                    } in
                                FStar_Compiler_Util.print1
                                  "Polymonadic subcomp after phase 1: %s\n"
                                  uu___9
                              else ());
                             t2))
                 else t in
               let uu___4 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu___4 with
                | (t2, ty, k) ->
                    let se3 =
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             {
                               FStar_Syntax_Syntax.m_lid1 = m;
                               FStar_Syntax_Syntax.n_lid1 = n;
                               FStar_Syntax_Syntax.tm4 = t2;
                               FStar_Syntax_Syntax.typ1 = ty;
                               FStar_Syntax_Syntax.kind2 =
                                 (FStar_Pervasives_Native.Some k)
                             });
                        FStar_Syntax_Syntax.sigrng =
                          (se2.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (se2.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (se2.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se2.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (se2.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se3], [], env0)))
let (tc_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun se ->
      let env1 = set_hint_correlator env se in
      (let uu___1 =
         let uu___2 =
           FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule in
         FStar_Options.debug_module uu___2 in
       if uu___1
       then
         let uu___2 = FStar_Syntax_Print.sigelt_to_string_short se in
         FStar_Compiler_Util.print1 "Processing %s\n" uu___2
       else ());
      (let uu___2 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu___2
       then
         let uu___3 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Compiler_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu___3
       else ());
      if (se.FStar_Syntax_Syntax.sigmeta).FStar_Syntax_Syntax.sigmeta_admit
      then
        (let old = FStar_Options.admit_smt_queries () in
         FStar_Options.set_admit_smt_queries true;
         (let result = tc_decl' env1 se in
          FStar_Options.set_admit_smt_queries old; result))
      else tc_decl' env1 se
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      fun from_cache ->
        (let uu___1 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.sigelt_to_string se in
           let uu___3 = FStar_Compiler_Util.string_of_bool from_cache in
           FStar_Compiler_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu___2 uu___3
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Compiler_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu___4 in
               (FStar_Errors_Codes.Fatal_UnexpectedInductivetype, uu___3) in
             FStar_Errors.raise_error uu___2 se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Compiler_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu___4 in
               (FStar_Errors_Codes.Fatal_UnexpectedInductivetype, uu___3) in
             FStar_Errors.raise_error uu___2 se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ uu___1 when
             FStar_Compiler_Effect.op_Bar_Greater
               se.FStar_Syntax_Syntax.sigquals
               (FStar_Compiler_Util.for_some
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu___3 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let uu___1 when
             FStar_Compiler_Effect.op_Bar_Greater
               se.FStar_Syntax_Syntax.sigquals
               (FStar_Compiler_Util.for_some
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu___3 -> false))
             -> env
         | uu___1 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (env1.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (env1.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (env1.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (env1.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (env1.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (env1.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (env1.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (env1.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (env1.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (env1.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (env1.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (env1.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (env1.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (env1.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (env1.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (env1.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (env1.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (env1.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (env1.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (env1.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (env1.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (env1.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (env1.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (env1.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (env1.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics =
                         (env1.FStar_TypeChecker_Env.intactics);
                       FStar_TypeChecker_Env.tc_term =
                         (env1.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (env1.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (env1.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (env1.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___4;
                       FStar_TypeChecker_Env.synth_hook =
                         (env1.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (env1.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (env1.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (env1.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (env1.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (env1.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (env1.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (env1.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (env1.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (env1.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (env1.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (env1.FStar_TypeChecker_Env.core_check)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___3 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (env1.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (env1.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (env1.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (env1.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (env1.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (env1.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (env1.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (env1.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (env1.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (env1.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (env1.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (env1.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (env1.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (env1.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (env1.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (env1.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (env1.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (env1.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (env1.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (env1.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (env1.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (env1.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (env1.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (env1.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (env1.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics =
                         (env1.FStar_TypeChecker_Env.intactics);
                       FStar_TypeChecker_Env.tc_term =
                         (env1.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (env1.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (env1.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (env1.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___3;
                       FStar_TypeChecker_Env.synth_hook =
                         (env1.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (env1.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (env1.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (env1.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (env1.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (env1.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (env1.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (env1.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (env1.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (env1.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (env1.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (env1.FStar_TypeChecker_Env.core_check)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (env1.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (env1.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (env1.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (env1.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (env1.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (env1.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (env1.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (env1.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (env1.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (env1.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (env1.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (env1.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (env1.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (env1.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (env1.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (env1.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (env1.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (env1.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (env1.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (env1.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (env1.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (env1.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (env1.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (env1.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (env1.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics =
                         (env1.FStar_TypeChecker_Env.intactics);
                       FStar_TypeChecker_Env.tc_term =
                         (env1.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (env1.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (env1.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (env1.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___4;
                       FStar_TypeChecker_Env.synth_hook =
                         (env1.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (env1.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (env1.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (env1.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (env1.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (env1.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (env1.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (env1.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (env1.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (env1.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (env1.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (env1.FStar_TypeChecker_Env.core_check)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (env1.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (env1.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (env1.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (env1.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (env1.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (env1.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (env1.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (env1.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (env1.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (env1.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (env1.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (env1.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (env1.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (env1.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (env1.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (env1.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (env1.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (env1.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (env1.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (env1.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (env1.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (env1.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (env1.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (env1.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (env1.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.intactics =
                         (env1.FStar_TypeChecker_Env.intactics);
                       FStar_TypeChecker_Env.tc_term =
                         (env1.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                         (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                       FStar_TypeChecker_Env.universe_of =
                         (env1.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                         =
                         (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                       FStar_TypeChecker_Env.teq_nosmt_force =
                         (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                       FStar_TypeChecker_Env.subtype_nosmt_force =
                         (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (env1.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (env1.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___4;
                       FStar_TypeChecker_Env.synth_hook =
                         (env1.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (env1.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (env1.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (env1.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (env1.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (env1.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (env1.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (env1.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (env1.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (env1.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                       FStar_TypeChecker_Env.erase_erasable_args =
                         (env1.FStar_TypeChecker_Env.erase_erasable_args);
                       FStar_TypeChecker_Env.core_check =
                         (env1.FStar_TypeChecker_Env.core_check)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.RestartSolver) ->
                  if from_cache || env1.FStar_TypeChecker_Env.nosynth
                  then env1
                  else
                    ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                       ();
                     env1)
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PrintEffectsGraph) ->
                  ((let uu___3 =
                      FStar_TypeChecker_Env.print_effects_graph env1 in
                    FStar_Compiler_Util.write_file "effects.graph" uu___3);
                   env1)
              | FStar_Syntax_Syntax.Sig_new_effect ne ->
                  let env2 =
                    FStar_TypeChecker_Env.push_new_effect env1
                      (ne, (se.FStar_Syntax_Syntax.sigquals)) in
                  FStar_Compiler_Effect.op_Bar_Greater
                    ne.FStar_Syntax_Syntax.actions
                    (FStar_Compiler_List.fold_left
                       (fun env3 ->
                          fun a ->
                            let uu___2 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Env.push_sigelt env3 uu___2)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
                    se.FStar_Syntax_Syntax.sigrng
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  { FStar_Syntax_Syntax.m_lid = m;
                    FStar_Syntax_Syntax.n_lid = n;
                    FStar_Syntax_Syntax.p_lid = p;
                    FStar_Syntax_Syntax.tm3 = uu___2;
                    FStar_Syntax_Syntax.typ = ty;
                    FStar_Syntax_Syntax.kind1 = k;_}
                  ->
                  let uu___3 =
                    FStar_Compiler_Effect.op_Bar_Greater k
                      FStar_Compiler_Util.must in
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty uu___3
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  { FStar_Syntax_Syntax.m_lid1 = m;
                    FStar_Syntax_Syntax.n_lid1 = n;
                    FStar_Syntax_Syntax.tm4 = uu___2;
                    FStar_Syntax_Syntax.typ1 = ty;
                    FStar_Syntax_Syntax.kind2 = k;_}
                  ->
                  let uu___3 =
                    let uu___4 =
                      FStar_Compiler_Effect.op_Bar_Greater k
                        FStar_Compiler_Util.must in
                    (ty, uu___4) in
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n
                    uu___3
              | uu___2 -> env1))
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu___ se =
        match uu___ with
        | (ses1, env1) ->
            let uu___1 =
              env1.FStar_TypeChecker_Env.nosynth &&
                (FStar_Options.debug_any ()) in
            if uu___1
            then ((ses1, env1), [])
            else
              ((let uu___4 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                if uu___4
                then
                  let uu___5 = FStar_Syntax_Print.tag_of_sigelt se in
                  let uu___6 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Compiler_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n" uu___5
                    uu___6
                else ());
               (let uu___5 = FStar_Options.ide_id_info_off () in
                if uu___5
                then FStar_TypeChecker_Env.toggle_id_info env1 false
                else ());
               (let uu___6 =
                  FStar_TypeChecker_Env.debug env1
                    (FStar_Options.Other "IdInfoOn") in
                if uu___6
                then FStar_TypeChecker_Env.toggle_id_info env1 true
                else ());
               (let uu___6 =
                  let uu___7 =
                    let uu___8 = FStar_Syntax_Print.sigelt_to_string_short se in
                    FStar_Compiler_Util.format1
                      "While typechecking the top-level declaration `%s`"
                      uu___8 in
                  FStar_Errors.with_ctx uu___7
                    (fun uu___8 -> tc_decl env1 se) in
                match uu___6 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_Compiler_Effect.op_Bar_Greater ses'
                        (FStar_Compiler_List.map
                           (fun se1 ->
                              (let uu___8 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu___8
                               then
                                 let uu___9 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Compiler_Util.print1
                                   "About to elim vars from %s\n" uu___9
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_Compiler_Effect.op_Bar_Greater ses_elaborated
                        (FStar_Compiler_List.map
                           (fun se1 ->
                              (let uu___8 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu___8
                               then
                                 let uu___9 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Compiler_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu___9
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    ((let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            FStar_TypeChecker_Env.current_module env2 in
                          FStar_Ident.string_of_lid uu___10 in
                        FStar_Pervasives_Native.Some uu___9 in
                      FStar_Profiling.profile
                        (fun uu___9 ->
                           FStar_TypeChecker_Env.promote_id_info env2
                             (fun t ->
                                (let uu___11 =
                                   FStar_TypeChecker_Env.debug env2
                                     (FStar_Options.Other "UF") in
                                 if uu___11
                                 then
                                   let uu___12 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Compiler_Util.print1
                                     "check uvars %s\n" uu___12
                                 else ());
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                  FStar_TypeChecker_Env.CheckNoUvars;
                                  FStar_TypeChecker_Env.Beta;
                                  FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                  FStar_TypeChecker_Env.CompressUvars;
                                  FStar_TypeChecker_Env.Exclude
                                    FStar_TypeChecker_Env.Zeta;
                                  FStar_TypeChecker_Env.Exclude
                                    FStar_TypeChecker_Env.Iota;
                                  FStar_TypeChecker_Env.NoFullNorm] env2 t))
                        uu___8 "FStar.TypeChecker.Tc.chec_uvars");
                     (let ses'2 =
                        FStar_Compiler_Effect.op_Bar_Greater ses'1
                          (FStar_Compiler_List.map
                             (FStar_Syntax_Compress.deep_compress_se false)) in
                      let env3 =
                        FStar_Compiler_Effect.op_Bar_Greater ses'2
                          (FStar_Compiler_List.fold_left
                             (fun env4 ->
                                fun se1 -> add_sigelt_to_env env4 se1 false)
                             env2) in
                      FStar_Syntax_Unionfind.reset ();
                      (let uu___10 =
                         (FStar_Options.log_types ()) ||
                           (FStar_Compiler_Effect.op_Less_Bar
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu___10
                       then
                         let uu___11 =
                           FStar_Compiler_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu___12 =
                                    let uu___13 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu___13 "\n" in
                                  Prims.op_Hat s uu___12) "" ses'2 in
                         FStar_Compiler_Util.print1 "Checked: %s\n" uu___11
                       else ());
                      (let uu___11 =
                         let uu___12 =
                           let uu___13 =
                             FStar_TypeChecker_Env.current_module env3 in
                           FStar_Ident.string_of_lid uu___13 in
                         FStar_Pervasives_Native.Some uu___12 in
                       FStar_Profiling.profile
                         (fun uu___12 ->
                            FStar_Compiler_List.iter
                              (fun se1 ->
                                 (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                                   env3 se1) ses'2) uu___11
                         "FStar.TypeChecker.Tc.encode_sig");
                      (((FStar_Compiler_List.rev_append ses'2 ses1), env3),
                        ses_elaborated1))))) in
      let process_one_decl_timed acc se =
        FStar_TypeChecker_Core.clear_memo_table ();
        (let uu___1 = acc in
         match uu___1 with
         | (uu___2, env1) ->
             let r =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.sigelt_to_string_short se in
                 FStar_Pervasives_Native.Some uu___4 in
               FStar_Profiling.profile
                 (fun uu___4 -> process_one_decl acc se) uu___3
                 "FStar.TypeChecker.Tc.process_one_decl" in
             ((let uu___4 =
                 (FStar_Options.profile_group_by_decls ()) ||
                   (FStar_Options.timing ()) in
               if uu___4
               then
                 let tag =
                   match FStar_Syntax_Util.lids_of_sigelt se with
                   | hd::uu___5 -> FStar_Ident.string_of_lid hd
                   | uu___5 ->
                       FStar_Compiler_Range_Ops.string_of_range
                         (FStar_Syntax_Util.range_of_sigelt se) in
                 FStar_Profiling.report_and_clear tag
               else ());
              r)) in
      let uu___ =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu___1 ->
             FStar_Compiler_Util.fold_flatten process_one_decl_timed
               ([], env) ses) in
      match uu___ with
      | (ses1, env1) -> ((FStar_Compiler_List.rev_append ses1 []), env1)
let (uu___875 : unit) =
  FStar_Compiler_Effect.op_Colon_Equals tc_decls_knot
    (FStar_Pervasives_Native.Some tc_decls)
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun msg ->
      FStar_Compiler_Util.atomically
        (fun uu___ -> FStar_TypeChecker_Env.snapshot env msg)
let (rollback_context :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env)
  =
  fun solver ->
    fun msg ->
      fun depth ->
        FStar_Compiler_Util.atomically
          (fun uu___ ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu___ = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu___
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      let verify =
        let uu___ = FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
        FStar_Options.should_verify uu___ in
      let action = if verify then "verifying" else "lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu___1 = FStar_Options.debug_any () in
       if uu___1
       then
         let uu___2 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Compiler_Util.print3 "Now %s %s of %s\n" action label uu___2
       else ());
      (let name =
         let uu___1 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Compiler_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu___1 in
       let env1 =
         {
           FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (env.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (env.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (env.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (env.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (env.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (env.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (env.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (env.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (env.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (env.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (env.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (env.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq_strict =
             (env.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (env.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (env.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (env.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (env.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.intactics =
             (env.FStar_TypeChecker_Env.intactics);
           FStar_TypeChecker_Env.tc_term =
             (env.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
             (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
           FStar_TypeChecker_Env.universe_of =
             (env.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
             (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
           FStar_TypeChecker_Env.teq_nosmt_force =
             (env.FStar_TypeChecker_Env.teq_nosmt_force);
           FStar_TypeChecker_Env.subtype_nosmt_force =
             (env.FStar_TypeChecker_Env.subtype_nosmt_force);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (env.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (env.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (env.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (env.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (env.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (env.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (env.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (env.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (env.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (env.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (env.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (env.FStar_TypeChecker_Env.enable_defer_to_tac);
           FStar_TypeChecker_Env.unif_allow_ref_guards =
             (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
           FStar_TypeChecker_Env.erase_erasable_args =
             (env.FStar_TypeChecker_Env.erase_erasable_args);
           FStar_TypeChecker_Env.core_check =
             (env.FStar_TypeChecker_Env.core_check)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu___1 =
         let uu___2 =
           let uu___3 =
             FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
           FStar_Options.should_check uu___3 in
         Prims.op_Negation uu___2 in
       let uu___2 =
         let uu___3 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Compiler_Util.format2 "While loading dependency %s%s" uu___3
           (if modul.FStar_Syntax_Syntax.is_interface
            then " (interface)"
            else "") in
       FStar_Errors.with_ctx_if uu___1 uu___2
         (fun uu___3 ->
            let uu___4 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
            match uu___4 with
            | (ses, env3) ->
                ({
                   FStar_Syntax_Syntax.name =
                     (modul.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = ses;
                   FStar_Syntax_Syntax.is_interface =
                     (modul.FStar_Syntax_Syntax.is_interface)
                 }, env3)))
let (tc_more_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      fun decls ->
        let uu___ = tc_decls env decls in
        match uu___ with
        | (ses, env1) ->
            let modul1 =
              {
                FStar_Syntax_Syntax.name = (modul.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_Compiler_List.op_At
                     modul.FStar_Syntax_Syntax.declarations ses);
                FStar_Syntax_Syntax.is_interface =
                  (modul.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, ses, env1)
let (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun loading_from_cache ->
    fun iface_exists ->
      fun en ->
        fun m ->
          let env = FStar_TypeChecker_Env.finish_module en m in
          (let uu___1 =
             FStar_Compiler_Effect.op_Bar_Greater
               env.FStar_TypeChecker_Env.qtbl_name_and_index
               FStar_Pervasives_Native.fst in
           FStar_Compiler_Effect.op_Bar_Greater uu___1
             FStar_Compiler_Util.smap_clear);
          (let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               Prims.op_Hat "Ending modul " uu___4 in
             pop_context env uu___3 in
           FStar_Compiler_Effect.op_Bar_Greater uu___2 (fun uu___3 -> ()));
          (m, env)
let (deep_compress_modul :
  FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul) =
  fun m ->
    let uu___ =
      FStar_Compiler_List.map (FStar_Syntax_Compress.deep_compress_se false)
        m.FStar_Syntax_Syntax.declarations in
    {
      FStar_Syntax_Syntax.name = (m.FStar_Syntax_Syntax.name);
      FStar_Syntax_Syntax.declarations = uu___;
      FStar_Syntax_Syntax.is_interface = (m.FStar_Syntax_Syntax.is_interface)
    }
let (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun m ->
      fun iface_exists ->
        let msg =
          let uu___ = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu___ in
        let env01 = push_context env0 msg in
        let uu___ = tc_partial_modul env01 m in
        match uu___ with
        | (modul, env) -> finish_partial_modul false iface_exists env modul
let (load_checked_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_TypeChecker_Env.env)
  =
  fun en ->
    fun m ->
      let m1 = deep_compress_modul m in
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m1.FStar_Syntax_Syntax.name in
      let env1 =
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu___1 in
        push_context env uu___ in
      let env2 =
        FStar_Compiler_List.fold_left
          (fun env3 ->
             fun se ->
               let env4 = add_sigelt_to_env env3 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_Compiler_Effect.op_Bar_Greater lids
                 (FStar_Compiler_List.iter
                    (fun lid ->
                       let uu___1 =
                         FStar_TypeChecker_Env.lookup_sigelt env4 lid in
                       ()));
               env4) env1 m1.FStar_Syntax_Syntax.declarations in
      let uu___ = finish_partial_modul true true env2 m1 in
      match uu___ with | (uu___1, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu___1 = FStar_Options.debug_any () in
         if uu___1
         then
           let uu___2 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Compiler_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu___2
         else ());
        (let uu___2 =
           let uu___3 = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.dump_module uu___3 in
         if uu___2
         then
           let uu___3 = FStar_Syntax_Print.modul_to_string m in
           FStar_Compiler_Util.print1 "Module before type checking:\n%s\n"
             uu___3
         else ());
        (let env1 =
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu___4 in
             Prims.op_Negation uu___3 in
           {
             FStar_TypeChecker_Env.solver =
               (env.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (env.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (env.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (env.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (env.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (env.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (env.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (env.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (env.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (env.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (env.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (env.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (env.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (env.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq_strict =
               (env.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (env.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu___2;
             FStar_TypeChecker_Env.lax_universes =
               (env.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (env.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (env.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (env.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (env.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.intactics =
               (env.FStar_TypeChecker_Env.intactics);
             FStar_TypeChecker_Env.tc_term =
               (env.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
               (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
             FStar_TypeChecker_Env.universe_of =
               (env.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
               (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
             FStar_TypeChecker_Env.teq_nosmt_force =
               (env.FStar_TypeChecker_Env.teq_nosmt_force);
             FStar_TypeChecker_Env.subtype_nosmt_force =
               (env.FStar_TypeChecker_Env.subtype_nosmt_force);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (env.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (env.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (env.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (env.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (env.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (env.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (env.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (env.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (env.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (env.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (env.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (env.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (env.FStar_TypeChecker_Env.enable_defer_to_tac);
             FStar_TypeChecker_Env.unif_allow_ref_guards =
               (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
             FStar_TypeChecker_Env.erase_erasable_args =
               (env.FStar_TypeChecker_Env.erase_erasable_args);
             FStar_TypeChecker_Env.core_check =
               (env.FStar_TypeChecker_Env.core_check)
           } in
         let uu___2 = tc_modul env1 m b in
         match uu___2 with
         | (m1, env2) ->
             ((let uu___4 =
                 let uu___5 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                 FStar_Options.dump_module uu___5 in
               if uu___4
               then
                 let uu___5 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Compiler_Util.print1
                   "Module after type checking:\n%s\n" uu___5
               else ());
              (let uu___5 =
                 (let uu___6 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                  FStar_Options.dump_module uu___6) &&
                   (let uu___6 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                    FStar_Options.debug_at_level uu___6
                      (FStar_Options.Other "Normalize")) in
               if uu___5
               then
                 let normalize_toplevel_lets se =
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_let
                       { FStar_Syntax_Syntax.lbs1 = (b1, lbs);
                         FStar_Syntax_Syntax.lids1 = ids;_}
                       ->
                       let n =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.Beta;
                           FStar_TypeChecker_Env.Eager_unfolding;
                           FStar_TypeChecker_Env.Reify;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.Primops;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                           FStar_TypeChecker_Env.AllowUnboundUniverses] in
                       let update lb =
                         let uu___6 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu___6 with
                         | (univnames, e) ->
                             let uu___7 =
                               let uu___8 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu___8 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (lb.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (lb.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (lb.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (lb.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu___7;
                               FStar_Syntax_Syntax.lbattrs =
                                 (lb.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (lb.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = FStar_Compiler_List.map update lbs in
                             (b1, uu___9) in
                           {
                             FStar_Syntax_Syntax.lbs1 = uu___8;
                             FStar_Syntax_Syntax.lids1 = ids
                           } in
                         FStar_Syntax_Syntax.Sig_let uu___7 in
                       {
                         FStar_Syntax_Syntax.sigel = uu___6;
                         FStar_Syntax_Syntax.sigrng =
                           (se.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (se.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (se.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (se.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (se.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu___6 -> se in
                 let normalized_module =
                   let uu___6 =
                     FStar_Compiler_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name = (m1.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu___6;
                     FStar_Syntax_Syntax.is_interface =
                       (m1.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu___6 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Compiler_Util.print1 "%s\n" uu___6
               else ());
              (m1, env2)))