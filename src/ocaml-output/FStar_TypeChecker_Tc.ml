open Prims
let (set_hint_correlator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      let tbl =
        FStar_All.pipe_right env.FStar_TypeChecker_Env.qtbl_name_and_index
          FStar_Pervasives_Native.fst in
      let get_n lid =
        let n_opt =
          let uu___ = FStar_Ident.string_of_lid lid in
          FStar_Util.smap_try_find tbl uu___ in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero in
      let uu___ = FStar_Options.reuse_hint_for () in
      match uu___ with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu___1 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu___1 l in
          let uu___1 = env in
          let uu___2 =
            let uu___3 =
              let uu___4 = let uu___5 = get_n lid in (lid, uu___5) in
              FStar_Pervasives_Native.Some uu___4 in
            (tbl, uu___3) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.type_of_well_typed =
              (uu___1.FStar_TypeChecker_Env.type_of_well_typed);
            FStar_TypeChecker_Env.universe_of =
              (uu___1.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu___2;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu___1 = FStar_TypeChecker_Env.current_module env in
                let uu___2 =
                  let uu___3 = FStar_Ident.next_id () in
                  FStar_All.pipe_right uu___3 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu___1 uu___2
            | l::uu___1 -> l in
          let uu___1 = env in
          let uu___2 =
            let uu___3 =
              let uu___4 = let uu___5 = get_n lid in (lid, uu___5) in
              FStar_Pervasives_Native.Some uu___4 in
            (tbl, uu___3) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___1.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___1.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___1.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___1.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.type_of_well_typed =
              (uu___1.FStar_TypeChecker_Env.type_of_well_typed);
            FStar_TypeChecker_Env.universe_of =
              (uu___1.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu___2;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu___ =
         let uu___1 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu___1 in
       Prims.op_Negation uu___)
let tc_lex_t :
  'uuuuu .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'uuuuu Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let err_range =
            let uu___1 = FStar_List.hd ses in
            uu___1.FStar_Syntax_Syntax.sigrng in
          (match lids with
           | lex_t::lex_top::lex_cons::[] when
               ((FStar_Ident.lid_equals lex_t FStar_Parser_Const.lex_t_lid)
                  &&
                  (FStar_Ident.lid_equals lex_top
                     FStar_Parser_Const.lextop_lid))
                 &&
                 (FStar_Ident.lid_equals lex_cons
                    FStar_Parser_Const.lexcons_lid)
               -> ()
           | uu___2 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t, uu___2, [], t, uu___3, uu___4);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu___5;
               FStar_Syntax_Syntax.sigattrs = uu___6;
               FStar_Syntax_Syntax.sigopts = uu___7;_}::{
                                                          FStar_Syntax_Syntax.sigel
                                                            =
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                            (lex_top, uu___8,
                                                             _t_top,
                                                             _lex_t_top,
                                                             uu___9, uu___10);
                                                          FStar_Syntax_Syntax.sigrng
                                                            = r1;
                                                          FStar_Syntax_Syntax.sigquals
                                                            = [];
                                                          FStar_Syntax_Syntax.sigmeta
                                                            = uu___11;
                                                          FStar_Syntax_Syntax.sigattrs
                                                            = uu___12;
                                                          FStar_Syntax_Syntax.sigopts
                                                            = uu___13;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons, uu___14, _t_cons, _lex_t_cons, uu___15,
                    uu___16);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu___17;
                 FStar_Syntax_Syntax.sigattrs = uu___18;
                 FStar_Syntax_Syntax.sigopts = uu___19;_}::[]
               when
               ((uu___9 = Prims.int_zero) && (uu___15 = Prims.int_zero)) &&
                 (((FStar_Ident.lid_equals lex_t FStar_Parser_Const.lex_t_lid)
                     &&
                     (FStar_Ident.lid_equals lex_top
                        FStar_Parser_Const.lextop_lid))
                    &&
                    (FStar_Ident.lid_equals lex_cons
                       FStar_Parser_Const.lexcons_lid))
               ->
               let u =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r) in
               let t1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_type
                      (FStar_Syntax_Syntax.U_name u)) r in
               let t2 = FStar_Syntax_Subst.close_univ_vars [u] t1 in
               let tc =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_inductive_typ
                        (lex_t, [u], [], t2, [],
                          [FStar_Parser_Const.lextop_lid;
                          FStar_Parser_Const.lexcons_lid]));
                   FStar_Syntax_Syntax.sigrng = r;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               let lex_top_t =
                 let uu___20 =
                   let uu___21 =
                     let uu___22 =
                       let uu___23 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.lex_t_lid r1 in
                       FStar_Syntax_Syntax.fvar uu___23
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     (uu___22, [FStar_Syntax_Syntax.U_zero]) in
                   FStar_Syntax_Syntax.Tm_uinst uu___21 in
                 FStar_Syntax_Syntax.mk uu___20 r1 in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top, [], lex_top_t,
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
                   FStar_Syntax_Syntax.sigrng = r1;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               let ucons1 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let ucons2 =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r2) in
               let lex_cons_t =
                 let a =
                   let uu___20 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1)) r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu___20 in
                 let hd =
                   let uu___20 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu___20 in
                 let tl =
                   let uu___20 =
                     let uu___21 =
                       let uu___22 =
                         let uu___23 =
                           let uu___24 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2 in
                           FStar_Syntax_Syntax.fvar uu___24
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu___23, [FStar_Syntax_Syntax.U_name ucons2]) in
                       FStar_Syntax_Syntax.Tm_uinst uu___22 in
                     FStar_Syntax_Syntax.mk uu___21 r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu___20 in
                 let res =
                   let uu___20 =
                     let uu___21 =
                       let uu___22 =
                         let uu___23 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r2 in
                         FStar_Syntax_Syntax.fvar uu___23
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       (uu___22,
                         [FStar_Syntax_Syntax.U_max
                            [FStar_Syntax_Syntax.U_name ucons1;
                            FStar_Syntax_Syntax.U_name ucons2]]) in
                     FStar_Syntax_Syntax.Tm_uinst uu___21 in
                   FStar_Syntax_Syntax.mk uu___20 r2 in
                 let uu___20 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd, FStar_Pervasives_Native.None);
                   (tl, FStar_Pervasives_Native.None)] uu___20 in
               let lex_cons_t1 =
                 FStar_Syntax_Subst.close_univ_vars [ucons1; ucons2]
                   lex_cons_t in
               let dc_lexcons =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_cons, [ucons1; ucons2], lex_cons_t1,
                          FStar_Parser_Const.lex_t_lid, Prims.int_zero, []));
                   FStar_Syntax_Syntax.sigrng = r2;
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               let uu___20 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu___20;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu___2 ->
               let err_msg =
                 let uu___3 =
                   let uu___4 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu___4 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu___3 in
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT, err_msg)
                 err_range)
let (tc_type_common :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Syntax_Syntax.typ ->
        FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
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
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1) in
                        FStar_All.pipe_right uu___4
                          (FStar_Syntax_Subst.close_univ_vars uvs1) in
                      (uvs1, uu___3)))
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu___1 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu___ r
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu___ =
          let uu___1 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu___1 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu___ r
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
                 FStar_Common.string_of_list
                   FStar_Syntax_Print.sigelt_to_string ses in
               FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu___2
             else ());
            (let uu___1 =
               FStar_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses quals lids in
             match uu___1 with
             | (sig_bndle, tcs, datas) ->
                 let attrs' =
                   FStar_Syntax_Util.remove_attr
                     FStar_Parser_Const.erasable_attr attrs in
                 let data_ops_ses =
                   let uu___2 =
                     FStar_List.map
                       (FStar_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas in
                   FStar_All.pipe_right uu___2 FStar_List.flatten in
                 ((let uu___3 =
                     (FStar_Options.no_positivity ()) ||
                       (let uu___4 = FStar_TypeChecker_Env.should_verify env in
                        Prims.op_Negation uu___4) in
                   if uu___3
                   then ()
                   else
                     (let env1 =
                        FStar_TypeChecker_Env.push_sigelt env sig_bndle in
                      FStar_List.iter
                        (fun ty ->
                           let b =
                             FStar_TypeChecker_TcInductive.check_positivity
                               ty env1 in
                           if Prims.op_Negation b
                           then
                             let uu___6 =
                               match ty.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   (lid, uu___7, uu___8, uu___9, uu___10,
                                    uu___11)
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
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Inductive type " uu___9 in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu___8) in
                                 FStar_Errors.log_issue r uu___7
                           else ()) tcs;
                      FStar_List.iter
                        (fun d ->
                           let uu___6 =
                             match d.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (data_lid, uu___7, uu___8, ty_lid, uu___9,
                                  uu___10)
                                 -> (data_lid, ty_lid)
                             | uu___7 -> failwith "Impossible" in
                           match uu___6 with
                           | (data_lid, ty_lid) ->
                               let uu___7 =
                                 (FStar_Ident.lid_equals ty_lid
                                    FStar_Parser_Const.exn_lid)
                                   &&
                                   (let uu___8 =
                                      FStar_TypeChecker_TcInductive.check_exn_positivity
                                        data_lid env1 in
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
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu___9) in
                                 FStar_Errors.log_issue
                                   d.FStar_Syntax_Syntax.sigrng uu___8
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu___3 =
                       let lid =
                         let ty = FStar_List.hd tcs in
                         match ty.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid1, uu___4, uu___5, uu___6, uu___7, uu___8)
                             -> lid1
                         | uu___4 -> failwith "Impossible" in
                       FStar_List.existsb
                         (fun s ->
                            let uu___4 =
                              let uu___5 = FStar_Ident.ident_of_lid lid in
                              FStar_Ident.string_of_id uu___5 in
                            s = uu___4)
                         FStar_TypeChecker_TcInductive.early_prims_inductives in
                     let is_noeq =
                       FStar_List.existsb
                         (fun q -> q = FStar_Syntax_Syntax.Noeq) quals in
                     let is_erasable uu___3 =
                       let uu___4 =
                         let uu___5 = FStar_List.hd tcs in
                         uu___5.FStar_Syntax_Syntax.sigattrs in
                       FStar_Syntax_Util.has_attribute uu___4
                         FStar_Parser_Const.erasable_attr in
                     ((((FStar_List.length tcs) = Prims.int_zero) ||
                         ((FStar_Ident.lid_equals
                             env.FStar_TypeChecker_Env.curmodule
                             FStar_Parser_Const.prims_lid)
                            && (skip_prims_type ())))
                        || is_noeq)
                       || (is_erasable ()) in
                   let res =
                     if skip_haseq
                     then (sig_bndle, data_ops_ses)
                     else
                       (let is_unopteq =
                          FStar_List.existsb
                            (fun q -> q = FStar_Syntax_Syntax.Unopteq) quals in
                        let ses1 =
                          if is_unopteq
                          then
                            FStar_TypeChecker_TcInductive.unoptimized_haseq_scheme
                              sig_bndle tcs datas env
                          else
                            FStar_TypeChecker_TcInductive.optimized_haseq_scheme
                              sig_bndle tcs datas env in
                        (sig_bndle, (FStar_List.append ses1 data_ops_ses))) in
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
                        FStar_All.pipe_right uu___3 (fun r -> pop (); r)) ()
               with | uu___2 -> (pop (); FStar_Exn.raise uu___2))
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
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
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                         let has_iface_val =
                           let uu___2 =
                             let uu___3 =
                               let uu___4 =
                                 FStar_Ident.ident_of_lid
                                   (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               FStar_Parser_AST.decl_is_val uu___4 in
                             FStar_Util.for_some uu___3 in
                           FStar_All.pipe_right iface_decls uu___2 in
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
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu___5 uu___6 in
                                (FStar_Errors.Error_MustEraseMissing, uu___4) in
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
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu___6 in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu___5) in
                                 FStar_Errors.log_issue uu___3 uu___4)
                              else ())
                         else ())))
          else ()
      | uu___ -> ()
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
            let uu___2 =
              FStar_Syntax_Embeddings.unembed
                FStar_Syntax_Embeddings.e_vconfig a1 in
            uu___2 true FStar_Syntax_Embeddings.id_norm_cb in
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
      let tc_and_elab_tactic env1 tau =
        let uu___ =
          FStar_TypeChecker_TcTerm.tc_tactic FStar_Syntax_Syntax.t_unit
            FStar_Syntax_Syntax.t_unit env1 tau in
        match uu___ with
        | (tau1, uu___1, g_tau) ->
            (FStar_TypeChecker_Rel.force_trivial_guard env1 g_tau; tau1) in
      let ats1 =
        let uu___ =
          FStar_Syntax_Util.extract_attr'
            FStar_Parser_Const.postprocess_extr_with ats in
        match uu___ with
        | FStar_Pervasives_Native.None -> ats
        | FStar_Pervasives_Native.Some
            (ats2, (tau, FStar_Pervasives_Native.None)::[]) ->
            let tau1 = tc_and_elab_tactic env tau in
            let tau2 = FStar_Syntax_Subst.deep_compress tau1 in
            let uu___1 =
              let uu___2 =
                FStar_Syntax_Syntax.tabbrev
                  FStar_Parser_Const.postprocess_extr_with in
              FStar_Syntax_Util.mk_app uu___2
                [(tau2, FStar_Pervasives_Native.None)] in
            uu___1 :: ats2
        | FStar_Pervasives_Native.Some
            (ats2, (tau, FStar_Pervasives_Native.None)::[]) ->
            ((let uu___2 = FStar_TypeChecker_Env.get_range env in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStar_Ident.string_of_lid
                      FStar_Parser_Const.postprocess_extr_with in
                  FStar_Util.format1 "Ill-formed application of `%s`" uu___5 in
                (FStar_Errors.Warning_UnrecognizedAttribute, uu___4) in
              FStar_Errors.log_issue uu___2 uu___3);
             ats2) in
      let uu___ =
        FStar_Syntax_Util.extract_attr' FStar_Parser_Const.postprocess_with
          ats1 in
      match uu___ with
      | FStar_Pervasives_Native.None -> (ats1, FStar_Pervasives_Native.None)
      | FStar_Pervasives_Native.Some
          (ats2, (tau, FStar_Pervasives_Native.None)::[]) ->
          let uu___1 =
            let uu___2 = tc_and_elab_tactic env tau in
            FStar_Pervasives_Native.Some uu___2 in
          (ats2, uu___1)
      | FStar_Pervasives_Native.Some (ats2, args) ->
          ((let uu___2 = FStar_TypeChecker_Env.get_range env in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Ident.string_of_lid
                    FStar_Parser_Const.postprocess_with in
                FStar_Util.format1 "Ill-formed application of `%s`" uu___5 in
              (FStar_Errors.Warning_UnrecognizedAttribute, uu___4) in
            FStar_Errors.log_issue uu___2 uu___3);
           (ats2, FStar_Pervasives_Native.None))
let (store_sigopts :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun se ->
    let uu___ = se in
    let uu___1 =
      let uu___2 = FStar_Options.get_vconfig () in
      FStar_Pervasives_Native.Some uu___2 in
    {
      FStar_Syntax_Syntax.sigel = (uu___.FStar_Syntax_Syntax.sigel);
      FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
      FStar_Syntax_Syntax.sigquals = (uu___.FStar_Syntax_Syntax.sigquals);
      FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
      FStar_Syntax_Syntax.sigattrs = (uu___.FStar_Syntax_Syntax.sigattrs);
      FStar_Syntax_Syntax.sigopts = uu___1
    }
let (tc_decls_knot :
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.sigelt Prims.list ->
       (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env))
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (tc_decl' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun se ->
      let env = env0 in
      FStar_TypeChecker_Util.check_sigelt_quals env se;
      proc_check_with se.FStar_Syntax_Syntax.sigattrs
        (fun uu___1 ->
           let r = se.FStar_Syntax_Syntax.sigrng in
           let se1 =
             let uu___2 = FStar_Options.record_options () in
             if uu___2 then store_sigopts se else se in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu___2 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail (uu___2, false, uu___3) when
               (let uu___4 = FStar_TypeChecker_Env.should_verify env in
                Prims.op_Negation uu___4) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail (expected_errors, lax, ses) ->
               let env' =
                 if lax
                 then
                   let uu___2 = env in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___2.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___2.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___2.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___2.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___2.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___2.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___2.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___2.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___2.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___2.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___2.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___2.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___2.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___2.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___2.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___2.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___2.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___2.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___2.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___2.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___2.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___2.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___2.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___2.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___2.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___2.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___2.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.type_of_well_typed =
                       (uu___2.FStar_TypeChecker_Env.type_of_well_typed);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___2.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___2.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___2.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___2.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___2.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___2.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___2.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___2.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___2.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___2.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___2.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___2.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___2.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___2.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___2.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___2.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___2.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___2.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (uu___2.FStar_TypeChecker_Env.enable_defer_to_tac);
                     FStar_TypeChecker_Env.unif_allow_ref_guards =
                       (uu___2.FStar_TypeChecker_Env.unif_allow_ref_guards)
                   }
                 else env in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure" in
               ((let uu___3 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       FStar_List.map FStar_Util.string_of_int
                         expected_errors in
                     FStar_All.pipe_left (FStar_String.concat "; ") uu___5 in
                   FStar_Util.print1 ">> Expecting errors: [%s]\n" uu___4
                 else ());
                (let uu___3 =
                   FStar_Errors.catch_errors
                     (fun uu___4 ->
                        FStar_Options.with_saved_options
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 = FStar_ST.op_Bang tc_decls_knot in
                               FStar_Util.must uu___7 in
                             uu___6 env'1 ses)) in
                 match uu___3 with
                 | (errs, uu___4) ->
                     ((let uu___6 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low) in
                       if uu___6
                       then
                         (FStar_Util.print_string ">> Got issues: [\n";
                          FStar_List.iter FStar_Errors.print_issue errs;
                          FStar_Util.print_string ">>]\n")
                       else ());
                      (let uu___6 =
                         FStar_TypeChecker_Env.pop env'1 "expect_failure" in
                       let actual_errors =
                         FStar_List.concatMap
                           (fun i ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs in
                       (match errs with
                        | [] ->
                            (FStar_List.iter FStar_Errors.print_issue errs;
                             FStar_Errors.log_issue
                               se1.FStar_Syntax_Syntax.sigrng
                               (FStar_Errors.Error_DidNotFail,
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
                                   (FStar_List.iter FStar_Errors.print_issue
                                      errs;
                                    (let uu___11 =
                                       let uu___12 =
                                         let uu___13 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             expected_errors in
                                         let uu___14 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             actual_errors in
                                         let uu___15 =
                                           FStar_Util.string_of_int e in
                                         let uu___16 =
                                           FStar_Util.string_of_int n2 in
                                         let uu___17 =
                                           FStar_Util.string_of_int n1 in
                                         FStar_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu___13 uu___14 uu___15 uu___16
                                           uu___17 in
                                       (FStar_Errors.Error_DidNotFail,
                                         uu___12) in
                                     FStar_Errors.log_issue
                                       se1.FStar_Syntax_Syntax.sigrng uu___11)))
                            else ());
                       ([], [], env)))))
           | FStar_Syntax_Syntax.Sig_bundle (ses, lids) when
               FStar_All.pipe_right lids
                 (FStar_Util.for_some
                    (FStar_Ident.lid_equals FStar_Parser_Const.lex_t_lid))
               ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               let se2 =
                 tc_lex_t env1 ses se1.FStar_Syntax_Syntax.sigquals lids in
               ([se2], [], env0)
           | FStar_Syntax_Syntax.Sig_bundle (ses, lids) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               let ses1 =
                 let uu___2 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1) in
                 if uu___2
                 then
                   let ses2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           tc_inductive
                             (let uu___6 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___6.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___6.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___6.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___6.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___6.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___6.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___6.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___6.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___6.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___6.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___6.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___6.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___6.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___6.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___6.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___6.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___6.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___6.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___6.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___6.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___6.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___6.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___6.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___6.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___6.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___6.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.type_of_well_typed =
                                  (uu___6.FStar_TypeChecker_Env.type_of_well_typed);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___6.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___6.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___6.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___6.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___6.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___6.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___6.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___6.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___6.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___6.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___6.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___6.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___6.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___6.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___6.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___6.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___6.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___6.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___6.FStar_TypeChecker_Env.enable_defer_to_tac);
                                FStar_TypeChecker_Env.unif_allow_ref_guards =
                                  (uu___6.FStar_TypeChecker_Env.unif_allow_ref_guards)
                              }) ses se1.FStar_Syntax_Syntax.sigquals
                             se1.FStar_Syntax_Syntax.sigattrs lids in
                         FStar_All.pipe_right uu___5
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu___4
                         (FStar_TypeChecker_Normalize.elim_uvars env1) in
                     FStar_All.pipe_right uu___3
                       FStar_Syntax_Util.ses_of_sigbundle in
                   ((let uu___4 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu___4
                     then
                       let uu___5 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___6 = se1 in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses2, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___6.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___6.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___6.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___6.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___6.FStar_Syntax_Syntax.sigopts)
                            }) in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu___5
                     else ());
                    ses2)
                 else ses in
               let uu___2 =
                 tc_inductive env1 ses1 se1.FStar_Syntax_Syntax.sigquals
                   se1.FStar_Syntax_Syntax.sigattrs lids in
               (match uu___2 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      let uu___3 = sigbndle in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___3.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu___2 =
                       let uu___3 =
                         FStar_All.pipe_right
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu___3
                         FStar_Syntax_Subst.compress in
                     (match uu___2 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown;
                          FStar_Syntax_Syntax.pos = uu___3;
                          FStar_Syntax_Syntax.vars = uu___4;_} -> true
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
                            [(let uu___3 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___3.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___3.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___3.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___3.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___3.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [(let uu___3 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___3.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___3.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___3.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___3.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___3.FStar_Syntax_Syntax.sigopts)
                              })] in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu___3 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env) in
                    if uu___3
                    then
                      let ne2 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___7 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___7.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___7.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___7.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___7.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___7.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___7.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___7.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___7.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___7.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___7.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___7.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___7.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___7.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___7.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___7.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___7.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___7.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___7.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___7.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___7.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___7.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___7.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___7.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___7.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___7.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___7.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.type_of_well_typed =
                                     (uu___7.FStar_TypeChecker_Env.type_of_well_typed);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___7.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___7.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___7.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___7.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___7.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___7.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___7.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___7.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___7.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___7.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___7.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___7.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___7.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___7.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___7.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___7.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___7.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___7.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___7.FStar_TypeChecker_Env.enable_defer_to_tac);
                                   FStar_TypeChecker_Env.unif_allow_ref_guards
                                     =
                                     (uu___7.FStar_TypeChecker_Env.unif_allow_ref_guards)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals
                                se1.FStar_Syntax_Syntax.sigattrs in
                            FStar_All.pipe_right uu___6
                              (fun ne3 ->
                                 let uu___7 = se1 in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne3);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___7.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___7.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___7.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___7.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___7.FStar_Syntax_Syntax.sigopts)
                                 }) in
                          FStar_All.pipe_right uu___5
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_All.pipe_right uu___4
                          FStar_Syntax_Util.eff_decl_of_new_effect in
                      ((let uu___5 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases") in
                        if uu___5
                        then
                          let uu___6 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___7 = se1 in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne2);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___7.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___7.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___7.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___7.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___7.FStar_Syntax_Syntax.sigopts)
                               }) in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu___6
                        else ());
                       ne2)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals
                      se1.FStar_Syntax_Syntax.sigattrs in
                  let se2 =
                    let uu___3 = se1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se2 =
                 let uu___2 = se1 in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___2.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___2.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___2.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___2.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___2.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags)
               ->
               let uu___2 =
                 let uu___3 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___7 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___7.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___7.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___7.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___7.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___7.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___7.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___7.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___7.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___7.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___7.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___7.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___7.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___7.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___7.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___7.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___7.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___7.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___7.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___7.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___7.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___7.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___7.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___7.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___7.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___7.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___7.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.type_of_well_typed =
                                (uu___7.FStar_TypeChecker_Env.type_of_well_typed);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___7.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___7.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___7.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___7.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___7.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___7.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___7.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___7.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___7.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___7.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___7.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___7.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___7.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___7.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___7.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___7.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___7.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___7.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___7.FStar_TypeChecker_Env.enable_defer_to_tac);
                              FStar_TypeChecker_Env.unif_allow_ref_guards =
                                (uu___7.FStar_TypeChecker_Env.unif_allow_ref_guards)
                            }) (lid, uvs, tps, c) r in
                       FStar_All.pipe_right uu___6
                         (fun uu___7 ->
                            match uu___7 with
                            | (lid1, uvs1, tps1, c1) ->
                                let uu___8 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___8.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___8.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___8.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___8.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___8.FStar_Syntax_Syntax.sigopts)
                                }) in
                     FStar_All.pipe_right uu___5
                       (FStar_TypeChecker_Normalize.elim_uvars env) in
                   FStar_All.pipe_right uu___4
                     (fun se2 ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1, uvs1, tps1, c1, uu___5) ->
                            (lid1, uvs1, tps1, c1)
                        | uu___5 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu___2 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu___3 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu___3 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se2 =
                           let uu___4 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___4.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___4.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___4.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___4.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___4.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ (uu___2, uu___3, uu___4)
               when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___5 ->
                       match uu___5 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu___6 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu___2, uu___3) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___4 ->
                       match uu___4 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu___5 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu___3 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStar_Ident.string_of_lid lid in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu___6 in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu___5) in
                   FStar_Errors.raise_error uu___4 r
                 else ());
                (let uu___3 =
                   let uu___4 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu___4
                   then
                     let uu___5 =
                       tc_declare_typ
                         (let uu___6 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___6.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___6.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___6.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___6.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___6.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___6.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___6.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___6.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___6.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___6.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___6.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___6.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___6.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___6.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___6.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___6.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___6.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___6.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___6.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___6.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___6.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___6.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___6.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___6.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___6.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___6.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.type_of_well_typed =
                              (uu___6.FStar_TypeChecker_Env.type_of_well_typed);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___6.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___6.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___6.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___6.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___6.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___6.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___6.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___6.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___6.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___6.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___6.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___6.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___6.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___6.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___6.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___6.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___6.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___6.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___6.FStar_TypeChecker_Env.enable_defer_to_tac);
                            FStar_TypeChecker_Env.unif_allow_ref_guards =
                              (uu___6.FStar_TypeChecker_Env.unif_allow_ref_guards)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu___5 with
                     | (uvs1, t1) ->
                         ((let uu___7 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu___7
                           then
                             let uu___8 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu___9 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu___8 uu___9
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([(let uu___5 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___5.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___5.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___5.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___5.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___5.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
               ((let uu___3 =
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Print.lid_to_string lid in
                     FStar_Util.format1 "Admitting a top-level assumption %s"
                       uu___5 in
                   (FStar_Errors.Warning_WarnOnUse, uu___4) in
                 FStar_Errors.log_issue r uu___3);
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu___3 =
                   let uu___4 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu___4
                   then
                     let uu___5 =
                       tc_assume
                         (let uu___6 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___6.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___6.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___6.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___6.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___6.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___6.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___6.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___6.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___6.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___6.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___6.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___6.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___6.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___6.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___6.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___6.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___6.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___6.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___6.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___6.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___6.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___6.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___6.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___6.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___6.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___6.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.type_of_well_typed =
                              (uu___6.FStar_TypeChecker_Env.type_of_well_typed);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___6.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___6.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___6.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___6.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___6.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___6.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___6.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___6.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___6.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___6.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___6.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___6.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___6.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___6.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___6.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___6.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___6.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___6.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___6.FStar_TypeChecker_Env.enable_defer_to_tac);
                            FStar_TypeChecker_Env.unif_allow_ref_guards =
                              (uu___6.FStar_TypeChecker_Env.unif_allow_ref_guards)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu___5 with
                     | (uvs1, t1) ->
                         ((let uu___7 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu___7
                           then
                             let uu___8 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu___9 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Assume after phase 1: %s and uvs: %s\n"
                               uu___8 uu___9
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu___3 with
                 | (uvs1, t1) ->
                     let uu___4 =
                       tc_assume env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu___4 with
                      | (uvs2, t2) ->
                          ([(let uu___5 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_assume
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___5.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___5.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___5.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___5.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___5.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
               ((let uu___3 = FStar_Options.debug_any () in
                 if uu___3
                 then
                   let uu___4 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu___5 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu___4
                     uu___5
                 else ());
                (let uu___3 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t in
                 match uu___3 with
                 | (t1, uu___4, g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses =
                         env.FStar_TypeChecker_Env.splice env
                           se1.FStar_Syntax_Syntax.sigrng t1 in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses in
                       FStar_List.iter
                         (fun lid ->
                            let uu___7 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids' in
                            match uu___7 with
                            | FStar_Pervasives_Native.None when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_Ident.string_of_lid lid in
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids' in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu___12 in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu___10 uu___11 in
                                  (FStar_Errors.Fatal_SplicedUndef, uu___9) in
                                FStar_Errors.raise_error uu___8 r
                            | uu___8 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses in
                        let env1 =
                          let uu___7 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___7.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___7.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___7.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___7.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___7.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___7.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___7.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___7.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___7.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___7.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___7.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___7.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___7.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___7.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___7.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___7.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___7.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___7.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___7.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___7.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___7.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___7.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___7.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___7.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___7.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___7.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___7.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___7.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.type_of_well_typed =
                              (uu___7.FStar_TypeChecker_Env.type_of_well_typed);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___7.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___7.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___7.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___7.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___7.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___7.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___7.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___7.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___7.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___7.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___7.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___7.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___7.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___7.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___7.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___7.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___7.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___7.FStar_TypeChecker_Env.enable_defer_to_tac);
                            FStar_TypeChecker_Env.unif_allow_ref_guards =
                              (uu___7.FStar_TypeChecker_Env.unif_allow_ref_guards)
                          } in
                        (let uu___8 =
                           FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                         if uu___8
                         then
                           let uu___9 =
                             let uu___10 =
                               FStar_List.map
                                 FStar_Syntax_Print.sigelt_to_string ses in
                             FStar_All.pipe_left (FStar_String.concat "\n")
                               uu___10 in
                           FStar_Util.print1
                             "Splice returned sigelts {\n%s\n}\n" uu___9
                         else ());
                        ([], ses, env1))))))
           | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               let check_quals_eq l qopt val_q =
                 match qopt with
                 | FStar_Pervasives_Native.None ->
                     FStar_Pervasives_Native.Some val_q
                 | FStar_Pervasives_Native.Some q' ->
                     let drop_logic =
                       FStar_List.filter
                         (fun x ->
                            Prims.op_Negation (x = FStar_Syntax_Syntax.Logic)) in
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = drop_logic val_q in
                         let uu___5 = drop_logic q' in (uu___4, uu___5) in
                       match uu___3 with
                       | (val_q1, q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                     if uu___2
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Syntax_Print.lid_to_string l in
                            let uu___7 =
                              FStar_Syntax_Print.quals_to_string val_q in
                            let uu___8 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu___6 uu___7 uu___8 in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu___5) in
                        FStar_Errors.raise_error uu___4 r) in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ in
                   let def_bs =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Subst.compress def in
                       uu___3.FStar_Syntax_Syntax.n in
                     match uu___2 with
                     | FStar_Syntax_Syntax.Tm_abs (binders, uu___3, uu___4)
                         -> binders
                     | uu___3 -> [] in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs, c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu___2;_} ->
                       let has_auto_name bv =
                         let uu___3 =
                           FStar_Ident.string_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.starts_with uu___3
                           FStar_Ident.reserved_prefix in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([], uu___3) -> val_bs1
                         | (uu___3, []) -> val_bs1
                         | ((body_bv, uu___3)::bt, (val_bv, aqual)::vt) ->
                             let uu___4 =
                               let uu___5 =
                                 let uu___6 = has_auto_name body_bv in
                                 let uu___7 = has_auto_name val_bv in
                                 (uu___6, uu___7) in
                               match uu___5 with
                               | (true, uu___6) -> (val_bv, aqual)
                               | (false, true) ->
                                   let uu___6 =
                                     let uu___7 = val_bv in
                                     let uu___8 =
                                       let uu___9 =
                                         let uu___10 =
                                           FStar_Ident.string_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname in
                                         let uu___11 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname in
                                         (uu___10, uu___11) in
                                       FStar_Ident.mk_ident uu___9 in
                                     {
                                       FStar_Syntax_Syntax.ppname = uu___8;
                                       FStar_Syntax_Syntax.index =
                                         (uu___7.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___7.FStar_Syntax_Syntax.sort)
                                     } in
                                   (uu___6, aqual)
                               | (false, false) -> (val_bv, aqual) in
                             let uu___5 = rename_binders bt vt in uu___4 ::
                               uu___5 in
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = rename_binders def_bs val_bs in
                           (uu___5, c) in
                         FStar_Syntax_Syntax.Tm_arrow uu___4 in
                       FStar_Syntax_Syntax.mk uu___3 r1
                   | uu___2 -> typ1 in
                 let uu___2 = lb in
                 let uu___3 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___2.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___2.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu___3;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___2.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___2.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___2.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___2.FStar_Syntax_Syntax.lbpos)
                 } in
               let uu___2 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu___3 ->
                         fun lb ->
                           match uu___3 with
                           | (gen, lbs1, quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu___4 =
                                 let uu___5 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 match uu___5 with
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
                                       | uu___6 ->
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_ascribed
                                                ((lb.FStar_Syntax_Syntax.lbdef),
                                                  ((FStar_Util.Inl
                                                      (lb.FStar_Syntax_Syntax.lbtyp)),
                                                    FStar_Pervasives_Native.None),
                                                  FStar_Pervasives_Native.None))
                                             (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.pos in
                                     (if
                                        (lb.FStar_Syntax_Syntax.lbunivs <> [])
                                          &&
                                          ((FStar_List.length
                                              lb.FStar_Syntax_Syntax.lbunivs)
                                             <> (FStar_List.length uvs))
                                      then
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_IncoherentInlineUniverse,
                                            "Inline universes are incoherent with annotation from val declaration")
                                          r
                                      else ();
                                      (let uu___7 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos)) in
                                       (false, uu___7, quals_opt1))) in
                               (match uu___4 with
                                | (gen1, lb1, quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals)))) in
               (match uu___2 with
                | (should_generalize, lbs', quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu___3 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | FStar_Syntax_Syntax.Irreducible -> true
                                    | FStar_Syntax_Syntax.Visible_default ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                        -> true
                                    | uu___5 -> false)) in
                          if uu___3
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q in
                    let lbs'1 = FStar_List.rev lbs' in
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs in
                      match uu___4 with
                      | FStar_Pervasives_Native.None ->
                          ((se1.FStar_Syntax_Syntax.sigattrs),
                            FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some
                          (ats, (tau, FStar_Pervasives_Native.None)::[]) ->
                          (ats, (FStar_Pervasives_Native.Some tau))
                      | FStar_Pervasives_Native.Some (ats, args) ->
                          (FStar_Errors.log_issue r
                             (FStar_Errors.Warning_UnrecognizedAttribute,
                               "Ill-formed application of `preprocess_with`");
                           ((se1.FStar_Syntax_Syntax.sigattrs),
                             FStar_Pervasives_Native.None)) in
                    (match uu___3 with
                     | (attrs, pre_tau) ->
                         let se2 =
                           let uu___4 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___4.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___4.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___4.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___4.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___4.FStar_Syntax_Syntax.sigopts)
                           } in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef in
                           (let uu___5 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases") in
                            if uu___5
                            then
                              let uu___6 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu___6
                            else ());
                           (let uu___5 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___5.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___5.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___5.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___5.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___5.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___5.FStar_Syntax_Syntax.lbpos)
                            }) in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None -> lbs'1 in
                         let e =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_constant
                                      FStar_Const.Const_unit) r in
                               (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                 uu___6) in
                             FStar_Syntax_Syntax.Tm_let uu___5 in
                           FStar_Syntax_Syntax.mk uu___4 r in
                         let env' =
                           let uu___4 = env1 in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___4.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___4.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___4.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___4.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___4.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___4.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___4.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___4.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___4.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___4.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___4.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___4.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___4.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___4.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___4.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___4.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___4.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___4.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___4.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___4.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___4.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___4.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___4.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___4.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___4.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___4.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.type_of_well_typed =
                               (uu___4.FStar_TypeChecker_Env.type_of_well_typed);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___4.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___4.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___4.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___4.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___4.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___4.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___4.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___4.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___4.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___4.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___4.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___4.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___4.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___4.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___4.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___4.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___4.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___4.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___4.FStar_TypeChecker_Env.enable_defer_to_tac);
                             FStar_TypeChecker_Env.unif_allow_ref_guards =
                               (uu___4.FStar_TypeChecker_Env.unif_allow_ref_guards)
                           } in
                         let e1 =
                           let uu___4 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env') in
                           if uu___4
                           then
                             let drop_lbtyp e_lax =
                               let uu___5 =
                                 let uu___6 =
                                   FStar_Syntax_Subst.compress e_lax in
                                 uu___6.FStar_Syntax_Syntax.n in
                               match uu___5 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false, lb::[]), e2) ->
                                   let lb_unannotated =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Syntax_Subst.compress e in
                                       uu___7.FStar_Syntax_Syntax.n in
                                     match uu___6 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu___7, lb1::[]), uu___8) ->
                                         let uu___9 =
                                           let uu___10 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp in
                                           uu___10.FStar_Syntax_Syntax.n in
                                         (match uu___9 with
                                          | FStar_Syntax_Syntax.Tm_unknown ->
                                              true
                                          | uu___10 -> false)
                                     | uu___7 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!" in
                                   if lb_unannotated
                                   then
                                     let uu___6 = e_lax in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___7 = lb in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___7.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___6.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___6.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu___6 -> e_lax in
                             let uu___5 =
                               FStar_Util.record_time
                                 (fun uu___6 ->
                                    let uu___7 =
                                      FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                        (let uu___8 = env' in
                                         {
                                           FStar_TypeChecker_Env.solver =
                                             (uu___8.FStar_TypeChecker_Env.solver);
                                           FStar_TypeChecker_Env.range =
                                             (uu___8.FStar_TypeChecker_Env.range);
                                           FStar_TypeChecker_Env.curmodule =
                                             (uu___8.FStar_TypeChecker_Env.curmodule);
                                           FStar_TypeChecker_Env.gamma =
                                             (uu___8.FStar_TypeChecker_Env.gamma);
                                           FStar_TypeChecker_Env.gamma_sig =
                                             (uu___8.FStar_TypeChecker_Env.gamma_sig);
                                           FStar_TypeChecker_Env.gamma_cache
                                             =
                                             (uu___8.FStar_TypeChecker_Env.gamma_cache);
                                           FStar_TypeChecker_Env.modules =
                                             (uu___8.FStar_TypeChecker_Env.modules);
                                           FStar_TypeChecker_Env.expected_typ
                                             =
                                             (uu___8.FStar_TypeChecker_Env.expected_typ);
                                           FStar_TypeChecker_Env.sigtab =
                                             (uu___8.FStar_TypeChecker_Env.sigtab);
                                           FStar_TypeChecker_Env.attrtab =
                                             (uu___8.FStar_TypeChecker_Env.attrtab);
                                           FStar_TypeChecker_Env.instantiate_imp
                                             =
                                             (uu___8.FStar_TypeChecker_Env.instantiate_imp);
                                           FStar_TypeChecker_Env.effects =
                                             (uu___8.FStar_TypeChecker_Env.effects);
                                           FStar_TypeChecker_Env.generalize =
                                             (uu___8.FStar_TypeChecker_Env.generalize);
                                           FStar_TypeChecker_Env.letrecs =
                                             (uu___8.FStar_TypeChecker_Env.letrecs);
                                           FStar_TypeChecker_Env.top_level =
                                             (uu___8.FStar_TypeChecker_Env.top_level);
                                           FStar_TypeChecker_Env.check_uvars
                                             =
                                             (uu___8.FStar_TypeChecker_Env.check_uvars);
                                           FStar_TypeChecker_Env.use_eq =
                                             (uu___8.FStar_TypeChecker_Env.use_eq);
                                           FStar_TypeChecker_Env.use_eq_strict
                                             =
                                             (uu___8.FStar_TypeChecker_Env.use_eq_strict);
                                           FStar_TypeChecker_Env.is_iface =
                                             (uu___8.FStar_TypeChecker_Env.is_iface);
                                           FStar_TypeChecker_Env.admit =
                                             (uu___8.FStar_TypeChecker_Env.admit);
                                           FStar_TypeChecker_Env.lax = true;
                                           FStar_TypeChecker_Env.lax_universes
                                             =
                                             (uu___8.FStar_TypeChecker_Env.lax_universes);
                                           FStar_TypeChecker_Env.phase1 =
                                             true;
                                           FStar_TypeChecker_Env.failhard =
                                             (uu___8.FStar_TypeChecker_Env.failhard);
                                           FStar_TypeChecker_Env.nosynth =
                                             (uu___8.FStar_TypeChecker_Env.nosynth);
                                           FStar_TypeChecker_Env.uvar_subtyping
                                             =
                                             (uu___8.FStar_TypeChecker_Env.uvar_subtyping);
                                           FStar_TypeChecker_Env.tc_term =
                                             (uu___8.FStar_TypeChecker_Env.tc_term);
                                           FStar_TypeChecker_Env.type_of =
                                             (uu___8.FStar_TypeChecker_Env.type_of);
                                           FStar_TypeChecker_Env.type_of_well_typed
                                             =
                                             (uu___8.FStar_TypeChecker_Env.type_of_well_typed);
                                           FStar_TypeChecker_Env.universe_of
                                             =
                                             (uu___8.FStar_TypeChecker_Env.universe_of);
                                           FStar_TypeChecker_Env.check_type_of
                                             =
                                             (uu___8.FStar_TypeChecker_Env.check_type_of);
                                           FStar_TypeChecker_Env.use_bv_sorts
                                             =
                                             (uu___8.FStar_TypeChecker_Env.use_bv_sorts);
                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                             =
                                             (uu___8.FStar_TypeChecker_Env.qtbl_name_and_index);
                                           FStar_TypeChecker_Env.normalized_eff_names
                                             =
                                             (uu___8.FStar_TypeChecker_Env.normalized_eff_names);
                                           FStar_TypeChecker_Env.fv_delta_depths
                                             =
                                             (uu___8.FStar_TypeChecker_Env.fv_delta_depths);
                                           FStar_TypeChecker_Env.proof_ns =
                                             (uu___8.FStar_TypeChecker_Env.proof_ns);
                                           FStar_TypeChecker_Env.synth_hook =
                                             (uu___8.FStar_TypeChecker_Env.synth_hook);
                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                             =
                                             (uu___8.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                           FStar_TypeChecker_Env.splice =
                                             (uu___8.FStar_TypeChecker_Env.splice);
                                           FStar_TypeChecker_Env.mpreprocess
                                             =
                                             (uu___8.FStar_TypeChecker_Env.mpreprocess);
                                           FStar_TypeChecker_Env.postprocess
                                             =
                                             (uu___8.FStar_TypeChecker_Env.postprocess);
                                           FStar_TypeChecker_Env.identifier_info
                                             =
                                             (uu___8.FStar_TypeChecker_Env.identifier_info);
                                           FStar_TypeChecker_Env.tc_hooks =
                                             (uu___8.FStar_TypeChecker_Env.tc_hooks);
                                           FStar_TypeChecker_Env.dsenv =
                                             (uu___8.FStar_TypeChecker_Env.dsenv);
                                           FStar_TypeChecker_Env.nbe =
                                             (uu___8.FStar_TypeChecker_Env.nbe);
                                           FStar_TypeChecker_Env.strict_args_tab
                                             =
                                             (uu___8.FStar_TypeChecker_Env.strict_args_tab);
                                           FStar_TypeChecker_Env.erasable_types_tab
                                             =
                                             (uu___8.FStar_TypeChecker_Env.erasable_types_tab);
                                           FStar_TypeChecker_Env.enable_defer_to_tac
                                             =
                                             (uu___8.FStar_TypeChecker_Env.enable_defer_to_tac);
                                           FStar_TypeChecker_Env.unif_allow_ref_guards
                                             =
                                             (uu___8.FStar_TypeChecker_Env.unif_allow_ref_guards)
                                         }) e in
                                    match uu___7 with
                                    | (e2, uu___8, uu___9) -> e2) in
                             match uu___5 with
                             | (e2, ms) ->
                                 ((let uu___7 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime") in
                                   if uu___7
                                   then
                                     let uu___8 = FStar_Util.string_of_int ms in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds, now removing uvars\n"
                                       uu___8
                                   else ());
                                  (let uu___8 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases") in
                                   if uu___8
                                   then
                                     let uu___9 =
                                       FStar_Syntax_Print.term_to_string e2 in
                                     FStar_Util.print1
                                       "Let binding after phase 1, before removing uvars: %s\n"
                                       uu___9
                                   else ());
                                  (let e3 =
                                     let uu___8 =
                                       FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env' e2 in
                                     FStar_All.pipe_right uu___8 drop_lbtyp in
                                   (let uu___9 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other "TwoPhases") in
                                    if uu___9
                                    then
                                      let uu___10 =
                                        FStar_Syntax_Print.term_to_string e3 in
                                      FStar_Util.print1
                                        "Let binding after phase 1, uvars removed: %s\n"
                                        uu___10
                                    else ());
                                   e3))
                           else e in
                         let uu___4 =
                           handle_postprocess_with_attr env1
                             se2.FStar_Syntax_Syntax.sigattrs in
                         (match uu___4 with
                          | (attrs1, post_tau) ->
                              let se3 =
                                let uu___5 = se2 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___5.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___5.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___5.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___5.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___5.FStar_Syntax_Syntax.sigopts)
                                } in
                              let postprocess_lb tau lb =
                                let uu___5 =
                                  FStar_Syntax_Subst.univ_var_opening
                                    lb.FStar_Syntax_Syntax.lbunivs in
                                match uu___5 with
                                | (s, univnames) ->
                                    let lbdef =
                                      FStar_Syntax_Subst.subst s
                                        lb.FStar_Syntax_Syntax.lbdef in
                                    let lbtyp =
                                      FStar_Syntax_Subst.subst s
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    let env2 =
                                      FStar_TypeChecker_Env.push_univ_vars
                                        env1 univnames in
                                    let lbdef1 =
                                      FStar_TypeChecker_Env.postprocess env2
                                        tau lbtyp lbdef in
                                    let lbdef2 =
                                      FStar_Syntax_Subst.close_univ_vars
                                        univnames lbdef1 in
                                    let uu___6 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___6.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___6.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___6.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___6.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef2;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___6.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___6.FStar_Syntax_Syntax.lbpos)
                                    } in
                              let uu___5 =
                                FStar_Util.record_time
                                  (fun uu___6 ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1) in
                              (match uu___5 with
                               | (r1, ms) ->
                                   ((let uu___7 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime") in
                                     if uu___7
                                     then
                                       let uu___8 =
                                         FStar_Util.string_of_int ms in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu___8
                                     else ());
                                    (let uu___7 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1, e2);
                                            FStar_Syntax_Syntax.pos = uu___8;
                                            FStar_Syntax_Syntax.vars = uu___9;_},
                                          uu___10, g) when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu___11 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters) in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu___11) in
                                           let lbs3 =
                                             let uu___11 =
                                               match post_tau with
                                               | FStar_Pervasives_Native.Some
                                                   tau ->
                                                   FStar_List.map
                                                     (postprocess_lb tau)
                                                     (FStar_Pervasives_Native.snd
                                                        lbs2)
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   FStar_Pervasives_Native.snd
                                                     lbs2 in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs2), uu___11) in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu___11,
                                                  FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu___11 -> quals in
                                           ((let uu___11 = se3 in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___11.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___11.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___11.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___11.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu___8 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)" in
                                     match uu___7 with
                                     | (se4, lbs1) ->
                                         (FStar_All.pipe_right
                                            (FStar_Pervasives_Native.snd lbs1)
                                            (FStar_List.iter
                                               (fun lb ->
                                                  let fv =
                                                    FStar_Util.right
                                                      lb.FStar_Syntax_Syntax.lbname in
                                                  FStar_TypeChecker_Env.insert_fv_info
                                                    env1 fv
                                                    lb.FStar_Syntax_Syntax.lbtyp));
                                          (let uu___10 = log env1 in
                                           if uu___10
                                           then
                                             let uu___11 =
                                               let uu___12 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb ->
                                                         let should_log =
                                                           let uu___13 =
                                                             let uu___14 =
                                                               let uu___15 =
                                                                 let uu___16
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname in
                                                                 uu___16.FStar_Syntax_Syntax.fv_name in
                                                               uu___15.FStar_Syntax_Syntax.v in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1 uu___14 in
                                                           match uu___13 with
                                                           | FStar_Pervasives_Native.None
                                                               -> true
                                                           | uu___14 -> false in
                                                         if should_log
                                                         then
                                                           let uu___13 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname in
                                                           let uu___14 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu___13 uu___14
                                                         else "")) in
                                               FStar_All.pipe_right uu___12
                                                 (FStar_String.concat "\n") in
                                             FStar_Util.print1 "%s\n" uu___11
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind (m, n, p, t, uu___2) ->
               let t1 =
                 let uu___3 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___8 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___8.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___8.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___8.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___8.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___8.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___8.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___8.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___8.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___8.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___8.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___8.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___8.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___8.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___8.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___8.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___8.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___8.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___8.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___8.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___8.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___8.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___8.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___8.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___8.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___8.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___8.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.type_of_well_typed =
                                  (uu___8.FStar_TypeChecker_Env.type_of_well_typed);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___8.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___8.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___8.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___8.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___8.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___8.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___8.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___8.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___8.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___8.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___8.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___8.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___8.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___8.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___8.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___8.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___8.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___8.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___8.FStar_TypeChecker_Env.enable_defer_to_tac);
                                FStar_TypeChecker_Env.unif_allow_ref_guards =
                                  (uu___8.FStar_TypeChecker_Env.unif_allow_ref_guards)
                              }) m n p t in
                         FStar_All.pipe_right uu___7
                           (fun uu___8 ->
                              match uu___8 with
                              | (t2, ty) ->
                                  let uu___9 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t2, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___9.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___9.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___9.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___9.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___9.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu___6
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu___5
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu___6, uu___7, uu___8, t2, ty) -> (t2, ty)
                          | uu___6 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                   match uu___4 with
                   | (t2, ty) ->
                       ((let uu___6 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu___6
                         then
                           let uu___7 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___8 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t2, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___8.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___8.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___8.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___8.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___8.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n" uu___7
                         else ());
                        t2)
                 else t in
               let uu___3 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu___3 with
                | (t2, ty) ->
                    let se2 =
                      let uu___4 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___4.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___4.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___4.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___4.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___4.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m, n, t, uu___2) ->
               let t1 =
                 let uu___3 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu___3
                 then
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                             (let uu___8 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___8.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___8.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___8.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___8.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___8.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___8.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___8.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___8.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___8.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___8.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___8.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___8.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___8.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___8.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___8.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___8.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___8.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___8.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___8.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___8.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___8.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___8.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___8.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___8.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___8.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___8.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.type_of_well_typed =
                                  (uu___8.FStar_TypeChecker_Env.type_of_well_typed);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___8.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___8.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___8.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___8.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___8.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___8.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___8.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___8.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___8.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___8.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___8.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___8.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___8.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___8.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___8.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___8.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___8.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___8.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___8.FStar_TypeChecker_Env.enable_defer_to_tac);
                                FStar_TypeChecker_Env.unif_allow_ref_guards =
                                  (uu___8.FStar_TypeChecker_Env.unif_allow_ref_guards)
                              }) m n t in
                         FStar_All.pipe_right uu___7
                           (fun uu___8 ->
                              match uu___8 with
                              | (t2, ty) ->
                                  let uu___9 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                         (m, n, t2, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___9.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___9.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___9.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___9.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___9.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu___6
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu___5
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                              (uu___6, uu___7, t2, ty) -> (t2, ty)
                          | uu___6 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                   match uu___4 with
                   | (t2, ty) ->
                       ((let uu___6 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu___6
                         then
                           let uu___7 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___8 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                       (m, n, t2, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___8.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___8.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___8.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___8.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___8.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic subcomp after phase 1: %s\n" uu___7
                         else ());
                        t2)
                 else t in
               let uu___3 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu___3 with
                | (t2, ty) ->
                    let se2 =
                      let uu___4 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             (m, n, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___4.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___4.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___4.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___4.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___4.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0)))
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
         let uu___2 =
           let uu___3 =
             FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
               (FStar_List.map FStar_Ident.string_of_lid) in
           FStar_All.pipe_right uu___3 (FStar_String.concat ", ") in
         FStar_Util.print1 "Processing %s\n" uu___2
       else ());
      (let uu___2 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu___2
       then
         let uu___3 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu___3
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
           let uu___3 = FStar_Util.string_of_bool from_cache in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu___2 uu___3
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu___4 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu___3) in
             FStar_Errors.raise_error uu___2 se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu___1 ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu___4 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu___3) in
             FStar_Errors.raise_error uu___2 se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ (uu___1, uu___2, uu___3) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4 ->
                     match uu___4 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu___5 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu___1, uu___2) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___3 ->
                     match uu___3 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu___4 -> false))
             -> env
         | uu___1 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = env1 in
                     let uu___5 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___4.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___4.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___4.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___4.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___4.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___4.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___4.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___4.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___4.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___4.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___4.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___4.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___4.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___4.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___4.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___4.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___4.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___4.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___4.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___4.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___4.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___4.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___4.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___4.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___4.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___4.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___4.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___4.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.type_of_well_typed =
                         (uu___4.FStar_TypeChecker_Env.type_of_well_typed);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___4.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___4.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___4.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___4.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___4.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___4.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___5;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___4.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___4.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___4.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___4.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___4.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___4.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___4.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___4.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___4.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___4.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___4.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___4.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___4.FStar_TypeChecker_Env.unif_allow_ref_guards)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___3 = env1 in
                     let uu___4 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___3.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___3.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___3.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___3.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___3.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___3.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___3.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___3.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___3.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___3.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___3.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___3.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___3.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___3.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___3.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___3.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___3.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___3.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___3.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___3.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___3.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___3.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___3.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___3.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___3.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___3.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___3.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___3.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.type_of_well_typed =
                         (uu___3.FStar_TypeChecker_Env.type_of_well_typed);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___3.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___3.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___3.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___3.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___3.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___3.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___4;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___3.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___3.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___3.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___3.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___3.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___3.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___3.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___3.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___3.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___3.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___3.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___3.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___3.FStar_TypeChecker_Env.unif_allow_ref_guards)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = env1 in
                     let uu___5 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___4.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___4.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___4.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___4.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___4.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___4.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___4.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___4.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___4.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___4.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___4.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___4.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___4.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___4.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___4.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___4.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___4.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___4.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___4.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___4.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___4.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___4.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___4.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___4.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___4.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___4.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___4.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___4.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.type_of_well_typed =
                         (uu___4.FStar_TypeChecker_Env.type_of_well_typed);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___4.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___4.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___4.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___4.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___4.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___4.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___5;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___4.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___4.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___4.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___4.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___4.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___4.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___4.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___4.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___4.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___4.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___4.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___4.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___4.FStar_TypeChecker_Env.unif_allow_ref_guards)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu___2) ->
                  if from_cache
                  then env1
                  else
                    (let uu___4 = env1 in
                     let uu___5 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___4.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___4.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___4.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___4.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___4.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___4.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___4.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___4.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___4.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___4.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___4.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___4.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___4.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___4.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___4.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___4.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___4.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___4.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___4.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___4.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___4.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___4.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___4.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___4.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___4.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___4.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___4.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___4.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.type_of_well_typed =
                         (uu___4.FStar_TypeChecker_Env.type_of_well_typed);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___4.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___4.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___4.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___4.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___4.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___4.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu___5;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___4.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___4.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___4.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___4.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___4.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___4.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___4.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___4.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___4.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___4.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___4.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___4.FStar_TypeChecker_Env.enable_defer_to_tac);
                       FStar_TypeChecker_Env.unif_allow_ref_guards =
                         (uu___4.FStar_TypeChecker_Env.unif_allow_ref_guards)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.RestartSolver) ->
                  if from_cache || env1.FStar_TypeChecker_Env.nosynth
                  then env1
                  else
                    ((env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                       ();
                     env1)
              | FStar_Syntax_Syntax.Sig_new_effect ne ->
                  let env2 =
                    FStar_TypeChecker_Env.push_new_effect env1
                      (ne, (se.FStar_Syntax_Syntax.sigquals)) in
                  FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions
                    (FStar_List.fold_left
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
                  (m, n, p, uu___2, ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  (m, n, uu___2, ty) ->
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n ty
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
                  FStar_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n" uu___5
                    uu___6
                else ());
               (let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_Print.sigelt_to_string_short se in
                    FStar_Util.format1
                      "While typechecking the top-level declaration `%s`"
                      uu___6 in
                  FStar_Errors.with_ctx uu___5
                    (fun uu___6 -> tc_decl env1 se) in
                match uu___4 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_All.pipe_right ses'
                        (FStar_List.map
                           (fun se1 ->
                              (let uu___6 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu___6
                               then
                                 let uu___7 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from %s\n" uu___7
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_All.pipe_right ses_elaborated
                        (FStar_List.map
                           (fun se1 ->
                              (let uu___6 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu___6
                               then
                                 let uu___7 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu___7
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    (FStar_TypeChecker_Env.promote_id_info env2
                       (fun t ->
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
                            FStar_TypeChecker_Env.NoFullNorm] env2 t);
                     (let env3 =
                        FStar_All.pipe_right ses'1
                          (FStar_List.fold_left
                             (fun env4 ->
                                fun se1 -> add_sigelt_to_env env4 se1 false)
                             env2) in
                      FStar_Syntax_Unionfind.reset ();
                      (let uu___8 =
                         (FStar_Options.log_types ()) ||
                           (FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu___8
                       then
                         let uu___9 =
                           FStar_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu___11 "\n" in
                                  Prims.op_Hat s uu___10) "" ses'1 in
                         FStar_Util.print1 "Checked: %s\n" uu___9
                       else ());
                      FStar_List.iter
                        (fun se1 ->
                           (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                             env3 se1) ses'1;
                      (((FStar_List.rev_append ses'1 ses1), env3),
                        ses_elaborated1))))) in
      let process_one_decl_timed acc se =
        let uu___ = acc in
        match uu___ with
        | (uu___1, env1) ->
            let r =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_TypeChecker_Env.current_module env1 in
                  FStar_Ident.string_of_lid uu___4 in
                FStar_Pervasives_Native.Some uu___3 in
              FStar_Profiling.profile (fun uu___3 -> process_one_decl acc se)
                uu___2 "FStar.TypeChecker.Tc.process_one_decl" in
            ((let uu___3 = FStar_Options.profile_group_by_decls () in
              if uu___3
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu___4 -> FStar_Ident.string_of_lid hd
                  | uu___4 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se) in
                FStar_Profiling.report_and_clear tag
              else ());
             r) in
      let uu___ =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu___1 ->
             FStar_Util.fold_flatten process_one_decl_timed ([], env) ses) in
      match uu___ with
      | (ses1, env1) -> ((FStar_List.rev_append ses1 []), env1)
let (uu___998 : unit) =
  FStar_ST.op_Colon_Equals tc_decls_knot
    (FStar_Pervasives_Native.Some tc_decls)
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun msg ->
      FStar_Util.atomically
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
        FStar_Util.atomically
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
         FStar_Util.print3 "Now %s %s of %s\n" action label uu___2
       else ());
      (let name =
         let uu___1 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu___1 in
       let env1 =
         let uu___1 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range = (uu___1.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma = (uu___1.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.type_of_well_typed =
             (uu___1.FStar_TypeChecker_Env.type_of_well_typed);
           FStar_TypeChecker_Env.universe_of =
             (uu___1.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv = (uu___1.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
           FStar_TypeChecker_Env.unif_allow_ref_guards =
             (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards)
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
         FStar_Util.format2 "While loading dependency %s%s" uu___3
           (if modul.FStar_Syntax_Syntax.is_interface
            then " (interface)"
            else "") in
       FStar_Errors.with_ctx_if uu___1 uu___2
         (fun uu___3 ->
            let uu___4 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
            match uu___4 with
            | (ses, env3) ->
                ((let uu___5 = modul in
                  {
                    FStar_Syntax_Syntax.name =
                      (uu___5.FStar_Syntax_Syntax.name);
                    FStar_Syntax_Syntax.declarations = ses;
                    FStar_Syntax_Syntax.is_interface =
                      (uu___5.FStar_Syntax_Syntax.is_interface)
                  }), env3)))
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
              let uu___1 = modul in
              {
                FStar_Syntax_Syntax.name = (uu___1.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1.FStar_Syntax_Syntax.is_interface)
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
             FStar_All.pipe_right
               env.FStar_TypeChecker_Env.qtbl_name_and_index
               FStar_Pervasives_Native.fst in
           FStar_All.pipe_right uu___1 FStar_Util.smap_clear);
          (let uu___2 =
             let uu___3 =
               let uu___4 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               Prims.op_Hat "Ending modul " uu___4 in
             pop_context env uu___3 in
           FStar_All.pipe_right uu___2 (fun uu___3 -> ()));
          (m, env)
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
      let env =
        FStar_TypeChecker_Env.set_current_module en
          m.FStar_Syntax_Syntax.name in
      let env1 =
        let uu___ =
          let uu___1 = FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu___1 in
        push_context env uu___ in
      let env2 =
        FStar_List.fold_left
          (fun env3 ->
             fun se ->
               let env4 = add_sigelt_to_env env3 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu___1 =
                         FStar_TypeChecker_Env.lookup_sigelt env4 lid in
                       ()));
               env4) env1 m.FStar_Syntax_Syntax.declarations in
      let uu___ = finish_partial_modul true true env2 m in
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
           FStar_Util.print2 "Checking %s: %s\n"
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
           FStar_Util.print1 "Module before type checking:\n%s\n" uu___3
         else ());
        (let env1 =
           let uu___2 = env in
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu___5 in
             Prims.op_Negation uu___4 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___2.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___2.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___2.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___2.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___2.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___2.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___2.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___2.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___2.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___2.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___2.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___2.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___2.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___2.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___2.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___2.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___2.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___2.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___2.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___2.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu___3;
             FStar_TypeChecker_Env.lax_universes =
               (uu___2.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___2.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___2.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___2.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___2.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___2.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___2.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.type_of_well_typed =
               (uu___2.FStar_TypeChecker_Env.type_of_well_typed);
             FStar_TypeChecker_Env.universe_of =
               (uu___2.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___2.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___2.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___2.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___2.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___2.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___2.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___2.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___2.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___2.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___2.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___2.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___2.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___2.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___2.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe = (uu___2.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___2.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___2.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___2.FStar_TypeChecker_Env.enable_defer_to_tac);
             FStar_TypeChecker_Env.unif_allow_ref_guards =
               (uu___2.FStar_TypeChecker_Env.unif_allow_ref_guards)
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
                 FStar_Util.print1 "Module after type checking:\n%s\n" uu___5
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
                   | FStar_Syntax_Syntax.Sig_let ((b1, lbs), ids) ->
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
                             let uu___7 = lb in
                             let uu___8 =
                               let uu___9 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu___9 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___7.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___7.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___7.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___7.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu___8;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___7.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___7.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___6 = se in
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 = FStar_List.map update lbs in
                             (b1, uu___10) in
                           (uu___9, ids) in
                         FStar_Syntax_Syntax.Sig_let uu___8 in
                       {
                         FStar_Syntax_Syntax.sigel = uu___7;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___6.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___6.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___6.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___6.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___6.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu___6 -> se in
                 let normalized_module =
                   let uu___6 = m1 in
                   let uu___7 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___6.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu___7;
                     FStar_Syntax_Syntax.is_interface =
                       (uu___6.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu___6 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu___6
               else ());
              (m1, env2)))