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
          let uu____44 = FStar_Ident.string_of_lid lid in
          FStar_Util.smap_try_find tbl uu____44 in
        if FStar_Util.is_some n_opt
        then FStar_All.pipe_right n_opt FStar_Util.must
        else Prims.int_zero in
      let uu____48 = FStar_Options.reuse_hint_for () in
      match uu____48 with
      | FStar_Pervasives_Native.Some l ->
          let lid =
            let uu____53 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.lid_add_suffix uu____53 l in
          let uu___15_54 = env in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid in (lid, uu____80) in
              FStar_Pervasives_Native.Some uu____75 in
            (tbl, uu____68) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___15_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___15_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___15_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___15_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___15_54.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___15_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___15_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___15_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___15_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___15_54.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___15_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___15_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___15_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___15_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___15_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___15_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___15_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___15_54.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___15_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___15_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___15_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___15_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___15_54.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___15_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___15_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___15_54.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___15_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___15_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___15_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___15_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___15_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___15_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___15_54.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___15_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___15_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___15_54.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___15_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___15_54.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___15_54.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___15_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___15_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___15_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___15_54.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___15_54.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___15_54.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___15_54.FStar_TypeChecker_Env.enable_defer_to_tac)
          }
      | FStar_Pervasives_Native.None ->
          let lids = FStar_Syntax_Util.lids_of_sigelt se in
          let lid =
            match lids with
            | [] ->
                let uu____97 = FStar_TypeChecker_Env.current_module env in
                let uu____98 =
                  let uu____99 = FStar_Ident.next_id () in
                  FStar_All.pipe_right uu____99 FStar_Util.string_of_int in
                FStar_Ident.lid_add_suffix uu____97 uu____98
            | l::uu____101 -> l in
          let uu___24_104 = env in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid in (lid, uu____130) in
              FStar_Pervasives_Native.Some uu____125 in
            (tbl, uu____118) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___24_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___24_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___24_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___24_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___24_104.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___24_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___24_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___24_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___24_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___24_104.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___24_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___24_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___24_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___24_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___24_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___24_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___24_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___24_104.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___24_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___24_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___24_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___24_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___24_104.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___24_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___24_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___24_104.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___24_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___24_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___24_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___24_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___24_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___24_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___24_104.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___24_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___24_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___24_104.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___24_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___24_104.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___24_104.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___24_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___24_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___24_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___24_104.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___24_104.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___24_104.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___24_104.FStar_TypeChecker_Env.enable_defer_to_tac)
          }
let (log : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    (FStar_Options.log_types ()) &&
      (let uu____149 =
         let uu____150 = FStar_TypeChecker_Env.current_module env in
         FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____150 in
       Prims.op_Negation uu____149)
let tc_lex_t :
  'uuuuuu161 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'uuuuuu161 Prims.list ->
          FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt
  =
  fun env ->
    fun ses ->
      fun quals ->
        fun lids ->
          let err_range =
            let uu____196 = FStar_List.hd ses in
            uu____196.FStar_Syntax_Syntax.sigrng in
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
           | uu____201 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_InvalidRedefinitionOfLexT,
                   "Invalid (partial) redefinition of lex_t") err_range);
          (match ses with
           | {
               FStar_Syntax_Syntax.sigel =
                 FStar_Syntax_Syntax.Sig_inductive_typ
                 (lex_t, uu____205, [], t, uu____207, uu____208);
               FStar_Syntax_Syntax.sigrng = r;
               FStar_Syntax_Syntax.sigquals = [];
               FStar_Syntax_Syntax.sigmeta = uu____210;
               FStar_Syntax_Syntax.sigattrs = uu____211;
               FStar_Syntax_Syntax.sigopts = uu____212;_}::{
                                                             FStar_Syntax_Syntax.sigel
                                                               =
                                                               FStar_Syntax_Syntax.Sig_datacon
                                                               (lex_top,
                                                                uu____214,
                                                                _t_top,
                                                                _lex_t_top,
                                                                uu____251,
                                                                uu____217);
                                                             FStar_Syntax_Syntax.sigrng
                                                               = r1;
                                                             FStar_Syntax_Syntax.sigquals
                                                               = [];
                                                             FStar_Syntax_Syntax.sigmeta
                                                               = uu____219;
                                                             FStar_Syntax_Syntax.sigattrs
                                                               = uu____220;
                                                             FStar_Syntax_Syntax.sigopts
                                                               = uu____221;_}::
               {
                 FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                   (lex_cons, uu____223, _t_cons, _lex_t_cons, uu____260,
                    uu____226);
                 FStar_Syntax_Syntax.sigrng = r2;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta = uu____228;
                 FStar_Syntax_Syntax.sigattrs = uu____229;
                 FStar_Syntax_Syntax.sigopts = uu____230;_}::[]
               when
               ((uu____251 = Prims.int_zero) && (uu____260 = Prims.int_zero))
                 &&
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
               let utop =
                 FStar_Syntax_Syntax.new_univ_name
                   (FStar_Pervasives_Native.Some r1) in
               let lex_top_t =
                 let uu____287 =
                   let uu____288 =
                     let uu____295 =
                       let uu____298 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.lex_t_lid r1 in
                       FStar_Syntax_Syntax.fvar uu____298
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None in
                     (uu____295, [FStar_Syntax_Syntax.U_name utop]) in
                   FStar_Syntax_Syntax.Tm_uinst uu____288 in
                 FStar_Syntax_Syntax.mk uu____287 r1 in
               let lex_top_t1 =
                 FStar_Syntax_Subst.close_univ_vars [utop] lex_top_t in
               let dc_lextop =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (lex_top, [utop], lex_top_t1,
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
                   let uu____311 =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_type
                          (FStar_Syntax_Syntax.U_name ucons1)) r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____311 in
                 let hd =
                   let uu____313 = FStar_Syntax_Syntax.bv_to_name a in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____313 in
                 let tl =
                   let uu____315 =
                     let uu____316 =
                       let uu____317 =
                         let uu____324 =
                           let uu____327 =
                             FStar_Ident.set_lid_range
                               FStar_Parser_Const.lex_t_lid r2 in
                           FStar_Syntax_Syntax.fvar uu____327
                             FStar_Syntax_Syntax.delta_constant
                             FStar_Pervasives_Native.None in
                         (uu____324, [FStar_Syntax_Syntax.U_name ucons2]) in
                       FStar_Syntax_Syntax.Tm_uinst uu____317 in
                     FStar_Syntax_Syntax.mk uu____316 r2 in
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some r2) uu____315 in
                 let res =
                   let uu____333 =
                     let uu____334 =
                       let uu____341 =
                         let uu____344 =
                           FStar_Ident.set_lid_range
                             FStar_Parser_Const.lex_t_lid r2 in
                         FStar_Syntax_Syntax.fvar uu____344
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       (uu____341,
                         [FStar_Syntax_Syntax.U_max
                            [FStar_Syntax_Syntax.U_name ucons1;
                            FStar_Syntax_Syntax.U_name ucons2]]) in
                     FStar_Syntax_Syntax.Tm_uinst uu____334 in
                   FStar_Syntax_Syntax.mk uu____333 r2 in
                 let uu____347 = FStar_Syntax_Syntax.mk_Total res in
                 FStar_Syntax_Util.arrow
                   [(a,
                      (FStar_Pervasives_Native.Some
                         FStar_Syntax_Syntax.imp_tag));
                   (hd, FStar_Pervasives_Native.None);
                   (tl, FStar_Pervasives_Native.None)] uu____347 in
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
               let uu____384 = FStar_TypeChecker_Env.get_range env in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_bundle
                      ([tc; dc_lextop; dc_lexcons], lids));
                 FStar_Syntax_Syntax.sigrng = uu____384;
                 FStar_Syntax_Syntax.sigquals = [];
                 FStar_Syntax_Syntax.sigmeta =
                   FStar_Syntax_Syntax.default_sigmeta;
                 FStar_Syntax_Syntax.sigattrs = [];
                 FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
               }
           | uu____389 ->
               let err_msg =
                 let uu____393 =
                   let uu____394 =
                     FStar_Syntax_Syntax.mk_sigelt
                       (FStar_Syntax_Syntax.Sig_bundle (ses, lids)) in
                   FStar_Syntax_Print.sigelt_to_string uu____394 in
                 FStar_Util.format1 "Invalid (re)definition of lex_t: %s\n"
                   uu____393 in
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
    fun uu____416 ->
      fun expected_typ ->
        fun r ->
          match uu____416 with
          | (uvs, t) ->
              let uu____429 = FStar_Syntax_Subst.open_univ_vars uvs t in
              (match uu____429 with
               | (uvs1, t1) ->
                   let env1 = FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                   let t2 =
                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t1
                       expected_typ in
                   if uvs1 = []
                   then
                     let uu____440 =
                       FStar_TypeChecker_Util.generalize_universes env1 t2 in
                     (match uu____440 with
                      | (uvs2, t3) ->
                          (FStar_TypeChecker_Util.check_uvars r t3;
                           (uvs2, t3)))
                   else
                     (let uu____457 =
                        let uu____460 =
                          FStar_All.pipe_right t2
                            (FStar_TypeChecker_Normalize.remove_uvar_solutions
                               env1) in
                        FStar_All.pipe_right uu____460
                          (FStar_Syntax_Subst.close_univ_vars uvs1) in
                      (uvs1, uu____457)))
let (tc_declare_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____482 =
          let uu____483 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____483 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____482 r
let (tc_assume :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.tscheme ->
      FStar_Range.range -> FStar_Syntax_Syntax.tscheme)
  =
  fun env ->
    fun ts ->
      fun r ->
        let uu____507 =
          let uu____508 = FStar_Syntax_Util.type_u () in
          FStar_All.pipe_right uu____508 FStar_Pervasives_Native.fst in
        tc_type_common env ts uu____507 r
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
            (let uu____565 =
               FStar_TypeChecker_Env.debug env FStar_Options.Low in
             if uu____565
             then
               let uu____566 =
                 FStar_Common.string_of_list
                   FStar_Syntax_Print.sigelt_to_string ses in
               FStar_Util.print1 ">>>>>>>>>>>>>>tc_inductive %s\n" uu____566
             else ());
            (let uu____568 =
               FStar_TypeChecker_TcInductive.check_inductive_well_typedness
                 env ses quals lids in
             match uu____568 with
             | (sig_bndle, tcs, datas) ->
                 let attrs' =
                   FStar_Syntax_Util.remove_attr
                     FStar_Parser_Const.erasable_attr attrs in
                 let data_ops_ses =
                   let uu____602 =
                     FStar_List.map
                       (FStar_TypeChecker_TcInductive.mk_data_operations
                          quals attrs' env tcs) datas in
                   FStar_All.pipe_right uu____602 FStar_List.flatten in
                 ((let uu____616 =
                     (FStar_Options.no_positivity ()) ||
                       (let uu____618 =
                          FStar_TypeChecker_Env.should_verify env in
                        Prims.op_Negation uu____618) in
                   if uu____616
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
                             let uu____630 =
                               match ty.FStar_Syntax_Syntax.sigel with
                               | FStar_Syntax_Syntax.Sig_inductive_typ
                                   (lid, uu____640, uu____641, uu____642,
                                    uu____643, uu____644)
                                   -> (lid, (ty.FStar_Syntax_Syntax.sigrng))
                               | uu____653 -> failwith "Impossible!" in
                             match uu____630 with
                             | (lid, r) ->
                                 let uu____660 =
                                   let uu____665 =
                                     let uu____666 =
                                       let uu____667 =
                                         FStar_Ident.string_of_lid lid in
                                       Prims.op_Hat uu____667
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Inductive type " uu____666 in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____665) in
                                 FStar_Errors.log_issue r uu____660
                           else ()) tcs;
                      FStar_List.iter
                        (fun d ->
                           let uu____676 =
                             match d.FStar_Syntax_Syntax.sigel with
                             | FStar_Syntax_Syntax.Sig_datacon
                                 (data_lid, uu____686, uu____687, ty_lid,
                                  uu____689, uu____690)
                                 -> (data_lid, ty_lid)
                             | uu____695 -> failwith "Impossible" in
                           match uu____676 with
                           | (data_lid, ty_lid) ->
                               let uu____702 =
                                 (FStar_Ident.lid_equals ty_lid
                                    FStar_Parser_Const.exn_lid)
                                   &&
                                   (let uu____704 =
                                      FStar_TypeChecker_TcInductive.check_exn_positivity
                                        data_lid env1 in
                                    Prims.op_Negation uu____704) in
                               if uu____702
                               then
                                 let uu____705 =
                                   let uu____710 =
                                     let uu____711 =
                                       let uu____712 =
                                         FStar_Ident.string_of_lid data_lid in
                                       Prims.op_Hat uu____712
                                         " does not satisfy the positivity condition" in
                                     Prims.op_Hat "Exception " uu____711 in
                                   (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                     uu____710) in
                                 FStar_Errors.log_issue
                                   d.FStar_Syntax_Syntax.sigrng uu____705
                               else ()) datas));
                  (let skip_haseq =
                     let skip_prims_type uu____720 =
                       let lid =
                         let ty = FStar_List.hd tcs in
                         match ty.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid, uu____724, uu____725, uu____726,
                              uu____727, uu____728)
                             -> lid
                         | uu____737 -> failwith "Impossible" in
                       FStar_List.existsb
                         (fun s ->
                            let uu____741 =
                              let uu____742 = FStar_Ident.ident_of_lid lid in
                              FStar_Ident.string_of_id uu____742 in
                            s = uu____741)
                         FStar_TypeChecker_TcInductive.early_prims_inductives in
                     let is_noeq =
                       FStar_List.existsb
                         (fun q -> q = FStar_Syntax_Syntax.Noeq) quals in
                     let is_erasable uu____751 =
                       let uu____752 =
                         let uu____755 = FStar_List.hd tcs in
                         uu____755.FStar_Syntax_Syntax.sigattrs in
                       FStar_Syntax_Util.has_attribute uu____752
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
            let pop uu____836 =
              let uu____837 = FStar_TypeChecker_Env.pop env1 "tc_inductive" in
              () in
            try
              (fun uu___203_846 ->
                 match () with
                 | () ->
                     let uu____853 = tc_inductive' env1 ses quals attrs lids in
                     FStar_All.pipe_right uu____853 (fun r -> pop (); r)) ()
            with | uu___202_884 -> (pop (); FStar_Exn.raise uu___202_884)
let (check_must_erase_attribute :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
          let uu____914 =
            let uu____915 = FStar_Options.ide () in
            Prims.op_Negation uu____915 in
          if uu____914
          then
            let uu____916 =
              let uu____921 = FStar_TypeChecker_Env.dsenv env in
              let uu____922 = FStar_TypeChecker_Env.current_module env in
              FStar_Syntax_DsEnv.iface_decls uu____921 uu____922 in
            (match uu____916 with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some iface_decls ->
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.iter
                      (fun lb ->
                         let lbname =
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                         let has_iface_val =
                           let uu____944 =
                             let uu____951 =
                               let uu____956 =
                                 FStar_Ident.ident_of_lid
                                   (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               FStar_Parser_AST.decl_is_val uu____956 in
                             FStar_Util.for_some uu____951 in
                           FStar_All.pipe_right iface_decls uu____944 in
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
                              let uu____961 =
                                FStar_Syntax_Syntax.range_of_fv lbname in
                              let uu____962 =
                                let uu____967 =
                                  let uu____968 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  let uu____969 =
                                    FStar_Syntax_Print.fv_to_string lbname in
                                  FStar_Util.format2
                                    "Values of type `%s` will be erased during extraction, but its interface hides this fact. Add the `must_erase_for_extraction` attribute to the `val %s` declaration for this symbol in the interface"
                                    uu____968 uu____969 in
                                (FStar_Errors.Error_MustEraseMissing,
                                  uu____967) in
                              FStar_Errors.log_issue uu____961 uu____962
                            else
                              if has_attr && (Prims.op_Negation must_erase)
                              then
                                (let uu____971 =
                                   FStar_Syntax_Syntax.range_of_fv lbname in
                                 let uu____972 =
                                   let uu____977 =
                                     let uu____978 =
                                       FStar_Syntax_Print.fv_to_string lbname in
                                     FStar_Util.format1
                                       "Values of type `%s` cannot be erased during extraction, but the `must_erase_for_extraction` attribute claims that it can. Please remove the attribute."
                                       uu____978 in
                                   (FStar_Errors.Error_MustEraseMissing,
                                     uu____977) in
                                 FStar_Errors.log_issue uu____971 uu____972)
                              else ())
                         else ())))
          else ()
      | uu____982 -> ()
let (unembed_optionstate_knot :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (unembed_optionstate :
  FStar_Syntax_Syntax.term ->
    FStar_Options.optionstate FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____1010 =
      let uu____1017 =
        let uu____1020 = FStar_ST.op_Bang unembed_optionstate_knot in
        FStar_Util.must uu____1020 in
      FStar_Syntax_Embeddings.unembed uu____1017 t in
    uu____1010 true FStar_Syntax_Embeddings.id_norm_cb
let proc_check_with :
  'a . FStar_Syntax_Syntax.attribute Prims.list -> (unit -> 'a) -> 'a =
  fun attrs ->
    fun kont ->
      let uu____1067 =
        FStar_Syntax_Util.get_attribute FStar_Parser_Const.check_with_lid
          attrs in
      match uu____1067 with
      | FStar_Pervasives_Native.None -> kont ()
      | FStar_Pervasives_Native.Some ((a1, FStar_Pervasives_Native.None)::[])
          ->
          FStar_Options.with_saved_options
            (fun uu____1095 ->
               (let uu____1097 =
                  let uu____1098 = unembed_optionstate a1 in
                  FStar_All.pipe_right uu____1098 FStar_Util.must in
                FStar_Options.set uu____1097);
               kont ())
      | uu____1103 -> failwith "huh?"
let (tc_decls_knot :
  (FStar_TypeChecker_Env.env ->
     FStar_Syntax_Syntax.sigelt Prims.list ->
       (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
         Prims.list * FStar_TypeChecker_Env.env))
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
        (fun uu____1212 ->
           let r = se.FStar_Syntax_Syntax.sigrng in
           let se1 =
             let uu____1215 = FStar_Options.record_options () in
             if uu____1215
             then
               let uu___250_1216 = se in
               let uu____1217 =
                 let uu____1220 = FStar_Options.peek () in
                 FStar_Pervasives_Native.Some uu____1220 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (uu___250_1216.FStar_Syntax_Syntax.sigel);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___250_1216.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___250_1216.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___250_1216.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___250_1216.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts = uu____1217
               }
             else se in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____1232 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____1259 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail (uu____1284, false, uu____1285)
               when
               (let uu____1296 = FStar_TypeChecker_Env.should_verify env in
                Prims.op_Negation uu____1296) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail (expected_errors, lax, ses) ->
               let env' =
                 if lax
                 then
                   let uu___268_1313 = env in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___268_1313.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___268_1313.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___268_1313.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___268_1313.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___268_1313.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___268_1313.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___268_1313.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___268_1313.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___268_1313.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___268_1313.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___268_1313.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___268_1313.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___268_1313.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___268_1313.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___268_1313.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___268_1313.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___268_1313.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___268_1313.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___268_1313.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___268_1313.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___268_1313.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___268_1313.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___268_1313.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___268_1313.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___268_1313.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___268_1313.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___268_1313.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___268_1313.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___268_1313.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___268_1313.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___268_1313.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___268_1313.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___268_1313.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___268_1313.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___268_1313.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___268_1313.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___268_1313.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___268_1313.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___268_1313.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___268_1313.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___268_1313.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___268_1313.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___268_1313.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___268_1313.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___268_1313.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (uu___268_1313.FStar_TypeChecker_Env.enable_defer_to_tac)
                   }
                 else env in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure" in
               ((let uu____1317 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low in
                 if uu____1317
                 then
                   let uu____1318 =
                     let uu____1319 =
                       FStar_List.map FStar_Util.string_of_int
                         expected_errors in
                     FStar_All.pipe_left (FStar_String.concat "; ")
                       uu____1319 in
                   FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____1318
                 else ());
                (let uu____1325 =
                   FStar_Errors.catch_errors
                     (fun uu____1355 ->
                        FStar_Options.with_saved_options
                          (fun uu____1368 ->
                             let uu____1369 =
                               let uu____1390 =
                                 FStar_ST.op_Bang tc_decls_knot in
                               FStar_Util.must uu____1390 in
                             uu____1369 env'1 ses)) in
                 match uu____1325 with
                 | (errs, uu____1486) ->
                     ((let uu____1516 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low) in
                       if uu____1516
                       then
                         (FStar_Util.print_string ">> Got issues: [\n";
                          FStar_List.iter FStar_Errors.print_issue errs;
                          FStar_Util.print_string ">>]\n")
                       else ());
                      (let uu____1520 =
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
                        | uu____1528 ->
                            if expected_errors <> []
                            then
                              let uu____1533 =
                                FStar_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors in
                              (match uu____1533 with
                               | FStar_Pervasives_Native.None -> ()
                               | FStar_Pervasives_Native.Some (e, n1, n2) ->
                                   (FStar_List.iter FStar_Errors.print_issue
                                      errs;
                                    (let uu____1558 =
                                       let uu____1563 =
                                         let uu____1564 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             expected_errors in
                                         let uu____1565 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             actual_errors in
                                         let uu____1566 =
                                           FStar_Util.string_of_int e in
                                         let uu____1567 =
                                           FStar_Util.string_of_int n2 in
                                         let uu____1568 =
                                           FStar_Util.string_of_int n1 in
                                         FStar_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu____1564 uu____1565 uu____1566
                                           uu____1567 uu____1568 in
                                       (FStar_Errors.Error_DidNotFail,
                                         uu____1563) in
                                     FStar_Errors.log_issue
                                       se1.FStar_Syntax_Syntax.sigrng
                                       uu____1558)))
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
                 let uu____1606 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1) in
                 if uu____1606
                 then
                   let ses1 =
                     let uu____1612 =
                       let uu____1613 =
                         let uu____1614 =
                           tc_inductive
                             (let uu___310_1623 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___310_1623.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___310_1623.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___310_1623.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___310_1623.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___310_1623.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___310_1623.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___310_1623.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___310_1623.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___310_1623.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___310_1623.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___310_1623.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___310_1623.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___310_1623.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___310_1623.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___310_1623.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___310_1623.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___310_1623.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___310_1623.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___310_1623.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___310_1623.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___310_1623.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___310_1623.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___310_1623.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___310_1623.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___310_1623.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___310_1623.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___310_1623.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___310_1623.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___310_1623.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___310_1623.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___310_1623.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___310_1623.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___310_1623.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___310_1623.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___310_1623.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___310_1623.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___310_1623.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___310_1623.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___310_1623.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___310_1623.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___310_1623.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___310_1623.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___310_1623.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___310_1623.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___310_1623.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) ses se1.FStar_Syntax_Syntax.sigquals
                             se1.FStar_Syntax_Syntax.sigattrs lids in
                         FStar_All.pipe_right uu____1614
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____1613
                         (FStar_TypeChecker_Normalize.elim_uvars env1) in
                     FStar_All.pipe_right uu____1612
                       FStar_Syntax_Util.ses_of_sigbundle in
                   ((let uu____1635 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____1635
                     then
                       let uu____1636 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___314_1639 = se1 in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___314_1639.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___314_1639.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___314_1639.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___314_1639.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___314_1639.FStar_Syntax_Syntax.sigopts)
                            }) in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____1636
                     else ());
                    ses1)
                 else ses in
               let uu____1646 =
                 tc_inductive env1 ses1 se1.FStar_Syntax_Syntax.sigquals
                   se1.FStar_Syntax_Syntax.sigattrs lids in
               (match uu____1646 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      let uu___321_1670 = sigbndle in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___321_1670.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___321_1670.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___321_1670.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___321_1670.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___321_1670.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu____1684 =
                       let uu____1687 =
                         FStar_All.pipe_right
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____1687
                         FStar_Syntax_Subst.compress in
                     (match uu____1684 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown;
                          FStar_Syntax_Syntax.pos = uu____1698;
                          FStar_Syntax_Syntax.vars = uu____1699;_} -> true
                      | uu____1702 -> false)
                 | uu____1705 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____1717 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu____1717 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___346_1756 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___346_1756.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___346_1756.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___346_1756.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___346_1756.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___346_1756.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [(let uu___349_1758 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___349_1758.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___349_1758.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___349_1758.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___349_1758.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___349_1758.FStar_Syntax_Syntax.sigopts)
                              })] in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____1765 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env) in
                    if uu____1765
                    then
                      let ne1 =
                        let uu____1767 =
                          let uu____1768 =
                            let uu____1769 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___353_1772 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___353_1772.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___353_1772.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___353_1772.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___353_1772.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___353_1772.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___353_1772.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___353_1772.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___353_1772.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___353_1772.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___353_1772.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___353_1772.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___353_1772.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___353_1772.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___353_1772.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___353_1772.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___353_1772.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___353_1772.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___353_1772.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___353_1772.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___353_1772.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___353_1772.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___353_1772.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___353_1772.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___353_1772.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___353_1772.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___353_1772.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___353_1772.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___353_1772.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___353_1772.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___353_1772.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___353_1772.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___353_1772.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___353_1772.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___353_1772.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___353_1772.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___353_1772.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___353_1772.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___353_1772.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___353_1772.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___353_1772.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___353_1772.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___353_1772.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___353_1772.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___353_1772.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___353_1772.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals
                                se1.FStar_Syntax_Syntax.sigattrs in
                            FStar_All.pipe_right uu____1769
                              (fun ne1 ->
                                 let uu___356_1776 = se1 in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___356_1776.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___356_1776.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___356_1776.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___356_1776.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___356_1776.FStar_Syntax_Syntax.sigopts)
                                 }) in
                          FStar_All.pipe_right uu____1768
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_All.pipe_right uu____1767
                          FStar_Syntax_Util.eff_decl_of_new_effect in
                      ((let uu____1778 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases") in
                        if uu____1778
                        then
                          let uu____1779 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___360_1782 = se1 in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___360_1782.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___360_1782.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___360_1782.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___360_1782.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___360_1782.FStar_Syntax_Syntax.sigopts)
                               }) in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____1779
                        else ());
                       ne1)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals
                      se1.FStar_Syntax_Syntax.sigattrs in
                  let se2 =
                    let uu___365_1787 = se1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___365_1787.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___365_1787.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___365_1787.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___365_1787.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___365_1787.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se2 =
                 let uu___371_1795 = se1 in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___371_1795.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___371_1795.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___371_1795.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___371_1795.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___371_1795.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags)
               ->
               let uu____1809 =
                 let uu____1818 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____1818
                 then
                   let uu____1827 =
                     let uu____1828 =
                       let uu____1829 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___382_1840 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___382_1840.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___382_1840.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___382_1840.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___382_1840.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___382_1840.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___382_1840.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___382_1840.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___382_1840.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___382_1840.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___382_1840.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___382_1840.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___382_1840.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___382_1840.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___382_1840.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___382_1840.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___382_1840.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___382_1840.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___382_1840.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___382_1840.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___382_1840.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___382_1840.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___382_1840.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___382_1840.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___382_1840.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___382_1840.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___382_1840.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___382_1840.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___382_1840.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___382_1840.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___382_1840.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___382_1840.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___382_1840.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___382_1840.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___382_1840.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___382_1840.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___382_1840.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___382_1840.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___382_1840.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___382_1840.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___382_1840.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___382_1840.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___382_1840.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___382_1840.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___382_1840.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___382_1840.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) (lid, uvs, tps, c) r in
                       FStar_All.pipe_right uu____1829
                         (fun uu____1855 ->
                            match uu____1855 with
                            | (lid1, uvs1, tps1, c1) ->
                                let uu___389_1868 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___389_1868.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___389_1868.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___389_1868.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___389_1868.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___389_1868.FStar_Syntax_Syntax.sigopts)
                                }) in
                     FStar_All.pipe_right uu____1828
                       (FStar_TypeChecker_Normalize.elim_uvars env) in
                   FStar_All.pipe_right uu____1827
                     (fun se2 ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1, uvs1, tps1, c1, uu____1898) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____1903 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu____1809 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu____1927 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu____1927 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se2 =
                           let uu___410_1951 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___410_1951.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___410_1951.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___410_1951.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___410_1951.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___410_1951.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____1958, uu____1959, uu____1960) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1964 ->
                       match uu___0_1964 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1965 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____1970, uu____1971) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1979 ->
                       match uu___0_1979 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1980 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu____1990 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu____1990
                 then
                   let uu____1991 =
                     let uu____1996 =
                       let uu____1997 = FStar_Ident.string_of_lid lid in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____1997 in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____1996) in
                   FStar_Errors.raise_error uu____1991 r
                 else ());
                (let uu____1999 =
                   let uu____2008 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2008
                   then
                     let uu____2017 =
                       tc_declare_typ
                         (let uu___434_2020 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___434_2020.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___434_2020.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___434_2020.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___434_2020.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___434_2020.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___434_2020.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___434_2020.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___434_2020.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___434_2020.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___434_2020.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___434_2020.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___434_2020.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___434_2020.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___434_2020.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___434_2020.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___434_2020.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___434_2020.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___434_2020.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___434_2020.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___434_2020.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___434_2020.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___434_2020.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___434_2020.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___434_2020.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___434_2020.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___434_2020.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___434_2020.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___434_2020.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___434_2020.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___434_2020.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___434_2020.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___434_2020.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___434_2020.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___434_2020.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___434_2020.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___434_2020.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___434_2020.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___434_2020.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___434_2020.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___434_2020.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___434_2020.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___434_2020.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___434_2020.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___434_2020.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___434_2020.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2017 with
                     | (uvs1, t1) ->
                         ((let uu____2044 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2044
                           then
                             let uu____2045 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2046 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2045 uu____2046
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____1999 with
                 | (uvs1, t1) ->
                     let uu____2077 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2077 with
                      | (uvs2, t2) ->
                          ([(let uu___447_2107 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___447_2107.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___447_2107.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___447_2107.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___447_2107.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___447_2107.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
               ((let uu____2112 =
                   let uu____2117 =
                     let uu____2118 = FStar_Syntax_Print.lid_to_string lid in
                     FStar_Util.format1 "Admitting a top-level assumption %s"
                       uu____2118 in
                   (FStar_Errors.Warning_WarnOnUse, uu____2117) in
                 FStar_Errors.log_issue r uu____2112);
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____2120 =
                   let uu____2129 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2129
                   then
                     let uu____2138 =
                       tc_assume
                         (let uu___457_2141 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___457_2141.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___457_2141.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___457_2141.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___457_2141.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___457_2141.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___457_2141.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___457_2141.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___457_2141.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___457_2141.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___457_2141.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___457_2141.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___457_2141.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___457_2141.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___457_2141.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___457_2141.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___457_2141.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___457_2141.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___457_2141.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___457_2141.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___457_2141.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___457_2141.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___457_2141.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___457_2141.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___457_2141.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___457_2141.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___457_2141.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___457_2141.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___457_2141.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___457_2141.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___457_2141.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___457_2141.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___457_2141.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___457_2141.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___457_2141.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___457_2141.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___457_2141.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___457_2141.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___457_2141.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___457_2141.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___457_2141.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___457_2141.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___457_2141.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___457_2141.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___457_2141.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___457_2141.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2138 with
                     | (uvs1, t1) ->
                         ((let uu____2165 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2165
                           then
                             let uu____2166 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2167 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Assume after phase 1: %s and uvs: %s\n"
                               uu____2166 uu____2167
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2120 with
                 | (uvs1, t1) ->
                     let uu____2198 =
                       tc_assume env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2198 with
                      | (uvs2, t2) ->
                          ([(let uu___470_2228 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_assume
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___470_2228.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___470_2228.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___470_2228.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___470_2228.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___470_2228.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
               ((let uu____2236 = FStar_Options.debug_any () in
                 if uu____2236
                 then
                   let uu____2237 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu____2238 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2237
                     uu____2238
                 else ());
                (let uu____2240 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t in
                 match uu____2240 with
                 | (t1, uu____2258, g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses =
                         env.FStar_TypeChecker_Env.splice env
                           se1.FStar_Syntax_Syntax.sigrng t1 in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses in
                       FStar_List.iter
                         (fun lid ->
                            let uu____2272 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids' in
                            match uu____2272 with
                            | FStar_Pervasives_Native.None when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2275 =
                                  let uu____2280 =
                                    let uu____2281 =
                                      FStar_Ident.string_of_lid lid in
                                    let uu____2282 =
                                      let uu____2283 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids' in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2283 in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2281 uu____2282 in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2280) in
                                FStar_Errors.raise_error uu____2275 r
                            | uu____2288 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses in
                        let env1 =
                          let uu___490_2293 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___490_2293.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___490_2293.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___490_2293.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___490_2293.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___490_2293.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___490_2293.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___490_2293.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___490_2293.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___490_2293.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___490_2293.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___490_2293.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___490_2293.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___490_2293.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___490_2293.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___490_2293.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___490_2293.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___490_2293.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___490_2293.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___490_2293.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___490_2293.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___490_2293.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___490_2293.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___490_2293.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___490_2293.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___490_2293.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___490_2293.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___490_2293.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___490_2293.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___490_2293.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___490_2293.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___490_2293.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___490_2293.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___490_2293.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___490_2293.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___490_2293.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___490_2293.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___490_2293.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___490_2293.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___490_2293.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___490_2293.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___490_2293.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___490_2293.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___490_2293.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___490_2293.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___490_2293.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___490_2293.FStar_TypeChecker_Env.enable_defer_to_tac)
                          } in
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
                     let uu____2361 =
                       let uu____2362 =
                         let uu____2371 = drop_logic val_q in
                         let uu____2374 = drop_logic q' in
                         (uu____2371, uu____2374) in
                       match uu____2362 with
                       | (val_q1, q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                     if uu____2361
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2398 =
                          let uu____2403 =
                            let uu____2404 =
                              FStar_Syntax_Print.lid_to_string l in
                            let uu____2405 =
                              FStar_Syntax_Print.quals_to_string val_q in
                            let uu____2406 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2404 uu____2405 uu____2406 in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2403) in
                        FStar_Errors.raise_error uu____2398 r) in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ in
                   let def_bs =
                     let uu____2440 =
                       let uu____2441 = FStar_Syntax_Subst.compress def in
                       uu____2441.FStar_Syntax_Syntax.n in
                     match uu____2440 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders, uu____2453, uu____2454) -> binders
                     | uu____2479 -> [] in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs, c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2491;_} ->
                       let has_auto_name bv =
                         let uu____2520 =
                           FStar_Ident.string_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.starts_with uu____2520
                           FStar_Ident.reserved_prefix in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([], uu____2596) -> val_bs1
                         | (uu____2627, []) -> val_bs1
                         | ((body_bv, uu____2659)::bt, (val_bv, aqual)::vt)
                             ->
                             let uu____2716 =
                               let uu____2723 =
                                 let uu____2728 = has_auto_name body_bv in
                                 let uu____2729 = has_auto_name val_bv in
                                 (uu____2728, uu____2729) in
                               match uu____2723 with
                               | (true, uu____2736) -> (val_bv, aqual)
                               | (false, true) ->
                                   let uu____2739 =
                                     let uu___559_2740 = val_bv in
                                     let uu____2741 =
                                       let uu____2742 =
                                         let uu____2747 =
                                           FStar_Ident.string_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname in
                                         let uu____2748 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname in
                                         (uu____2747, uu____2748) in
                                       FStar_Ident.mk_ident uu____2742 in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____2741;
                                       FStar_Syntax_Syntax.index =
                                         (uu___559_2740.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___559_2740.FStar_Syntax_Syntax.sort)
                                     } in
                                   (uu____2739, aqual)
                               | (false, false) -> (val_bv, aqual) in
                             let uu____2753 = rename_binders bt vt in
                             uu____2716 :: uu____2753 in
                       let uu____2768 =
                         let uu____2769 =
                           let uu____2784 = rename_binders def_bs val_bs in
                           (uu____2784, c) in
                         FStar_Syntax_Syntax.Tm_arrow uu____2769 in
                       FStar_Syntax_Syntax.mk uu____2768 r1
                   | uu____2803 -> typ1 in
                 let uu___565_2804 = lb in
                 let uu____2805 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___565_2804.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___565_2804.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____2805;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___565_2804.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___565_2804.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___565_2804.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___565_2804.FStar_Syntax_Syntax.lbpos)
                 } in
               let uu____2808 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____2859 ->
                         fun lb ->
                           match uu____2859 with
                           | (gen, lbs1, quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu____2901 =
                                 let uu____2912 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 match uu____2912 with
                                 | FStar_Pervasives_Native.None ->
                                     if lb.FStar_Syntax_Syntax.lbunivs <> []
                                     then (false, lb, quals_opt)
                                     else (gen, lb, quals_opt)
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
                                       | uu____2985 ->
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
                                      (let uu____3028 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos)) in
                                       (false, uu____3028, quals_opt1))) in
                               (match uu____2901 with
                                | (gen1, lb1, quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals)))) in
               (match uu____2808 with
                | (should_generalize, lbs', quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3120 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3124 ->
                                    match uu___1_3124 with
                                    | FStar_Syntax_Syntax.Irreducible -> true
                                    | FStar_Syntax_Syntax.Visible_default ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                        -> true
                                    | uu____3125 -> false)) in
                          if uu____3120
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q in
                    let lbs'1 = FStar_List.rev lbs' in
                    let uu____3132 =
                      let uu____3141 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs in
                      match uu____3141 with
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
                    (match uu____3132 with
                     | (attrs, pre_tau) ->
                         let se2 =
                           let uu___623_3244 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___623_3244.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___623_3244.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___623_3244.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___623_3244.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___623_3244.FStar_Syntax_Syntax.sigopts)
                           } in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef in
                           (let uu____3258 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases") in
                            if uu____3258
                            then
                              let uu____3259 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3259
                            else ());
                           (let uu___632_3261 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___632_3261.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___632_3261.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___632_3261.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___632_3261.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___632_3261.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___632_3261.FStar_Syntax_Syntax.lbpos)
                            }) in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None -> lbs'1 in
                         let e =
                           let uu____3271 =
                             let uu____3272 =
                               let uu____3285 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_constant
                                      FStar_Const.Const_unit) r in
                               (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                 uu____3285) in
                             FStar_Syntax_Syntax.Tm_let uu____3272 in
                           FStar_Syntax_Syntax.mk uu____3271 r in
                         let env' =
                           let uu___639_3301 = env1 in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___639_3301.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___639_3301.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___639_3301.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___639_3301.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___639_3301.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___639_3301.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___639_3301.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___639_3301.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___639_3301.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___639_3301.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___639_3301.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___639_3301.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___639_3301.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___639_3301.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___639_3301.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___639_3301.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___639_3301.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___639_3301.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___639_3301.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___639_3301.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___639_3301.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___639_3301.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___639_3301.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___639_3301.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___639_3301.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___639_3301.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___639_3301.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___639_3301.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___639_3301.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___639_3301.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___639_3301.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___639_3301.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___639_3301.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___639_3301.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___639_3301.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___639_3301.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___639_3301.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___639_3301.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___639_3301.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___639_3301.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___639_3301.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___639_3301.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___639_3301.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___639_3301.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___639_3301.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let e1 =
                           let uu____3303 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env') in
                           if uu____3303
                           then
                             let drop_lbtyp e_lax =
                               let uu____3310 =
                                 let uu____3311 =
                                   FStar_Syntax_Subst.compress e_lax in
                                 uu____3311.FStar_Syntax_Syntax.n in
                               match uu____3310 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false, lb::[]), e2) ->
                                   let lb_unannotated =
                                     let uu____3329 =
                                       let uu____3330 =
                                         FStar_Syntax_Subst.compress e in
                                       uu____3330.FStar_Syntax_Syntax.n in
                                     match uu____3329 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3333, lb1::[]), uu____3335)
                                         ->
                                         let uu____3348 =
                                           let uu____3349 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp in
                                           uu____3349.FStar_Syntax_Syntax.n in
                                         (match uu____3348 with
                                          | FStar_Syntax_Syntax.Tm_unknown ->
                                              true
                                          | uu____3352 -> false)
                                     | uu____3353 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!" in
                                   if lb_unannotated
                                   then
                                     let uu___664_3354 = e_lax in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___666_3366 = lb in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___666_3366.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___664_3354.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___664_3354.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3368 -> e_lax in
                             let uu____3369 =
                               FStar_Util.record_time
                                 (fun uu____3376 ->
                                    let uu____3377 =
                                      let uu____3378 =
                                        let uu____3379 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___670_3388 = env' in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___670_3388.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___670_3388.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___670_3388.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___670_3388.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___670_3388.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___670_3388.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___670_3388.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___670_3388.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___670_3388.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___670_3388.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) e in
                                        FStar_All.pipe_right uu____3379
                                          (fun uu____3399 ->
                                             match uu____3399 with
                                             | (e1, uu____3407, uu____3408)
                                                 -> e1) in
                                      FStar_All.pipe_right uu____3378
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env') in
                                    FStar_All.pipe_right uu____3377
                                      drop_lbtyp) in
                             match uu____3369 with
                             | (e1, ms) ->
                                 ((let uu____3412 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases") in
                                   if uu____3412
                                   then
                                     let uu____3413 =
                                       FStar_Syntax_Print.term_to_string e1 in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3413
                                   else ());
                                  (let uu____3416 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime") in
                                   if uu____3416
                                   then
                                     let uu____3417 =
                                       FStar_Util.string_of_int ms in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____3417
                                   else ());
                                  e1)
                           else e in
                         let uu____3420 =
                           let uu____3429 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs in
                           match uu____3429 with
                           | FStar_Pervasives_Native.None ->
                               ((se2.FStar_Syntax_Syntax.sigattrs),
                                 FStar_Pervasives_Native.None)
                           | FStar_Pervasives_Native.Some
                               (ats, (tau, FStar_Pervasives_Native.None)::[])
                               -> (ats, (FStar_Pervasives_Native.Some tau))
                           | FStar_Pervasives_Native.Some (ats, args) ->
                               (FStar_Errors.log_issue r
                                  (FStar_Errors.Warning_UnrecognizedAttribute,
                                    "Ill-formed application of `postprocess_with`");
                                ((se2.FStar_Syntax_Syntax.sigattrs),
                                  FStar_Pervasives_Native.None)) in
                         (match uu____3420 with
                          | (attrs1, post_tau) ->
                              let se3 =
                                let uu___700_3532 = se2 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___700_3532.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___700_3532.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___700_3532.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___700_3532.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___700_3532.FStar_Syntax_Syntax.sigopts)
                                } in
                              let postprocess_lb tau lb =
                                let uu____3544 =
                                  FStar_Syntax_Subst.univ_var_opening
                                    lb.FStar_Syntax_Syntax.lbunivs in
                                match uu____3544 with
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
                                    let uu___714_3568 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef2;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___714_3568.FStar_Syntax_Syntax.lbpos)
                                    } in
                              let uu____3569 =
                                FStar_Util.record_time
                                  (fun uu____3587 ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1) in
                              (match uu____3569 with
                               | (r1, ms) ->
                                   ((let uu____3613 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime") in
                                     if uu____3613
                                     then
                                       let uu____3614 =
                                         FStar_Util.string_of_int ms in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____3614
                                     else ());
                                    (let uu____3616 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1, e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____3639;
                                            FStar_Syntax_Syntax.vars =
                                              uu____3640;_},
                                          uu____3641, g) when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____3668 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters) in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____3668) in
                                           let lbs3 =
                                             let uu____3688 =
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
                                                 lbs2), uu____3688) in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____3707,
                                                  FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____3712 -> quals in
                                           ((let uu___744_3720 = se3 in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___744_3720.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___744_3720.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___744_3720.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___744_3720.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____3723 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)" in
                                     match uu____3616 with
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
                                          (let uu____3774 = log env1 in
                                           if uu____3774
                                           then
                                             let uu____3775 =
                                               let uu____3776 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb ->
                                                         let should_log =
                                                           let uu____3791 =
                                                             let uu____3800 =
                                                               let uu____3801
                                                                 =
                                                                 let uu____3804
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname in
                                                                 uu____3804.FStar_Syntax_Syntax.fv_name in
                                                               uu____3801.FStar_Syntax_Syntax.v in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____3800 in
                                                           match uu____3791
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                               -> true
                                                           | uu____3811 ->
                                                               false in
                                                         if should_log
                                                         then
                                                           let uu____3820 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname in
                                                           let uu____3821 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____3820
                                                             uu____3821
                                                         else "")) in
                                               FStar_All.pipe_right
                                                 uu____3776
                                                 (FStar_String.concat "\n") in
                                             FStar_Util.print1 "%s\n"
                                               uu____3775
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind
               (m, n, p, t, uu____3835) ->
               let t1 =
                 let uu____3837 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3837
                 then
                   let uu____3838 =
                     let uu____3843 =
                       let uu____3844 =
                         let uu____3845 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___769_3852 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___769_3852.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___769_3852.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___769_3852.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___769_3852.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___769_3852.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___769_3852.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___769_3852.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___769_3852.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___769_3852.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___769_3852.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___769_3852.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___769_3852.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___769_3852.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___769_3852.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___769_3852.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___769_3852.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___769_3852.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___769_3852.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___769_3852.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___769_3852.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___769_3852.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___769_3852.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___769_3852.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___769_3852.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___769_3852.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___769_3852.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___769_3852.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___769_3852.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___769_3852.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___769_3852.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___769_3852.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___769_3852.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___769_3852.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___769_3852.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___769_3852.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___769_3852.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___769_3852.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___769_3852.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___769_3852.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___769_3852.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___769_3852.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___769_3852.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___769_3852.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___769_3852.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___769_3852.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n p t in
                         FStar_All.pipe_right uu____3845
                           (fun uu____3861 ->
                              match uu____3861 with
                              | (t1, ty) ->
                                  let uu___774_3868 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___774_3868.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___774_3868.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___774_3868.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___774_3868.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___774_3868.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3844
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3843
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____3884, uu____3885, uu____3886, t1, ty) ->
                              (t1, ty)
                          | uu____3889 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                   match uu____3838 with
                   | (t1, ty) ->
                       ((let uu____3897 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3897
                         then
                           let uu____3898 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___789_3901 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___789_3901.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___789_3901.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___789_3901.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___789_3901.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___789_3901.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____3898
                         else ());
                        t1)
                 else t in
               let uu____3904 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu____3904 with
                | (t2, ty) ->
                    let se2 =
                      let uu___796_3922 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___796_3922.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___796_3922.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___796_3922.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___796_3922.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___796_3922.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
               (m, n, t, uu____3930) ->
               let t1 =
                 let uu____3932 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3932
                 then
                   let uu____3933 =
                     let uu____3938 =
                       let uu____3939 =
                         let uu____3940 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                             (let uu___806_3947 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___806_3947.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___806_3947.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___806_3947.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___806_3947.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___806_3947.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___806_3947.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___806_3947.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___806_3947.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___806_3947.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___806_3947.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___806_3947.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___806_3947.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___806_3947.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___806_3947.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___806_3947.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___806_3947.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___806_3947.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___806_3947.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___806_3947.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___806_3947.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___806_3947.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___806_3947.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___806_3947.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___806_3947.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___806_3947.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___806_3947.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___806_3947.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___806_3947.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___806_3947.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___806_3947.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___806_3947.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___806_3947.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___806_3947.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___806_3947.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___806_3947.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___806_3947.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___806_3947.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___806_3947.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___806_3947.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___806_3947.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___806_3947.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___806_3947.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___806_3947.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___806_3947.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___806_3947.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n t in
                         FStar_All.pipe_right uu____3940
                           (fun uu____3956 ->
                              match uu____3956 with
                              | (t1, ty) ->
                                  let uu___811_3963 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                         (m, n, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___811_3963.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___811_3963.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___811_3963.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___811_3963.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___811_3963.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3939
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3938
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                              (uu____3978, uu____3979, t1, ty) -> (t1, ty)
                          | uu____3982 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                   match uu____3933 with
                   | (t1, ty) ->
                       ((let uu____3990 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3990
                         then
                           let uu____3991 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___825_3994 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                       (m, n, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___825_3994.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___825_3994.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___825_3994.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___825_3994.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___825_3994.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic subcomp after phase 1: %s\n"
                             uu____3991
                         else ());
                        t1)
                 else t in
               let uu____3997 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu____3997 with
                | (t2, ty) ->
                    let se2 =
                      let uu___832_4015 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             (m, n, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___832_4015.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___832_4015.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___832_4015.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___832_4015.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___832_4015.FStar_Syntax_Syntax.sigopts)
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
      (let uu____4052 =
         let uu____4053 =
           FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule in
         FStar_Options.debug_module uu____4053 in
       if uu____4052
       then
         let uu____4054 =
           let uu____4055 =
             FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
               (FStar_List.map FStar_Ident.string_of_lid) in
           FStar_All.pipe_right uu____4055 (FStar_String.concat ", ") in
         FStar_Util.print1 "Processing %s\n" uu____4054
       else ());
      (let uu____4066 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____4066
       then
         let uu____4067 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4067
       else ());
      if (se.FStar_Syntax_Syntax.sigmeta).FStar_Syntax_Syntax.sigmeta_admit
      then
        (let old = FStar_Options.admit_smt_queries () in
         FStar_Options.set_admit_smt_queries true;
         (let result = tc_decl' env1 se in
          FStar_Options.set_admit_smt_queries old; result))
      else tc_decl' env1 se
let for_export :
  'uuuuuu4102 .
    'uuuuuu4102 ->
      FStar_Ident.lident Prims.list ->
        FStar_Syntax_Syntax.sigelt ->
          (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Ident.lident
            Prims.list)
  =
  fun env ->
    fun hidden ->
      fun se ->
        let is_abstract quals =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___2_4143 ->
                  match uu___2_4143 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | uu____4144 -> false)) in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l, uu____4152) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4158 -> false in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4167 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_fail uu____4172 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_splice uu____4191 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4206 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4231 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____4255) ->
            let uu____4264 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4264
            then
              let for_export_bundle se1 uu____4299 =
                match uu____4299 with
                | (out, hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, us, bs, t, uu____4338, uu____4339) ->
                         let dec =
                           let uu___891_4349 = se1 in
                           let uu____4350 =
                             let uu____4351 =
                               let uu____4358 =
                                 let uu____4359 =
                                   FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow bs uu____4359 in
                               (l, us, uu____4358) in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____4351 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____4350;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___891_4349.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___891_4349.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___891_4349.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___891_4349.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l, us, t, uu____4369, uu____4370, uu____4371) ->
                         let dec =
                           let uu___902_4377 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___902_4377.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___902_4377.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___902_4377.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___902_4377.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), (l :: hidden1))
                     | uu____4382 -> (out, hidden1)) in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____4404, uu____4405, uu____4406)
            ->
            let uu____4407 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4407 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
            let uu____4428 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc) in
            if uu____4428
            then
              ([(let uu___918_4444 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___918_4444.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___918_4444.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___918_4444.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___918_4444.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____4446 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___3_4450 ->
                         match uu___3_4450 with
                         | FStar_Syntax_Syntax.Assumption -> true
                         | FStar_Syntax_Syntax.Projector uu____4451 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____4456 ->
                             true
                         | uu____4457 -> false)) in
               if uu____4446 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_new_effect uu____4475 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____4480 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4485 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4502 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____4517 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____4531) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____4542 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
            if uu____4542
            then ([], hidden)
            else
              (let dec =
                 let uu____4559 = FStar_Ident.range_of_lid lid in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____4559;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
            let uu____4570 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4570
            then
              let uu____4579 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb ->
                        let uu___955_4592 = se in
                        let uu____4593 =
                          let uu____4594 =
                            let uu____4601 =
                              let uu____4602 =
                                let uu____4605 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname in
                                uu____4605.FStar_Syntax_Syntax.fv_name in
                              uu____4602.FStar_Syntax_Syntax.v in
                            (uu____4601, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp)) in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____4594 in
                        {
                          FStar_Syntax_Syntax.sigel = uu____4593;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___955_4592.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___955_4592.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___955_4592.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___955_4592.FStar_Syntax_Syntax.sigopts)
                        })) in
              (uu____4579, hidden)
            else ([se], hidden)
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      fun from_cache ->
        (let uu____4631 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____4631
         then
           let uu____4632 = FStar_Syntax_Print.sigelt_to_string se in
           let uu____4633 = FStar_Util.string_of_bool from_cache in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____4632 uu____4633
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____4635 ->
             let uu____4652 =
               let uu____4657 =
                 let uu____4658 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4658 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4657) in
             FStar_Errors.raise_error uu____4652
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____4659 ->
             let uu____4674 =
               let uu____4679 =
                 let uu____4680 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4680 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4679) in
             FStar_Errors.raise_error uu____4674
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____4681, uu____4682, uu____4683) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_4687 ->
                     match uu___4_4687 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4688 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____4689, uu____4690) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_4698 ->
                     match uu___4_4698 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4699 -> false))
             -> env
         | uu____4700 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____4702) ->
                  if from_cache
                  then env1
                  else
                    (let uu___992_4706 = env1 in
                     let uu____4707 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___992_4706.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___992_4706.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___992_4706.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___992_4706.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___992_4706.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___992_4706.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___992_4706.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___992_4706.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___992_4706.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___992_4706.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___992_4706.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___992_4706.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___992_4706.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___992_4706.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___992_4706.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___992_4706.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___992_4706.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___992_4706.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___992_4706.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___992_4706.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___992_4706.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___992_4706.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___992_4706.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___992_4706.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___992_4706.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___992_4706.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___992_4706.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___992_4706.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___992_4706.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___992_4706.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___992_4706.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___992_4706.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___992_4706.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___992_4706.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4707;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___992_4706.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___992_4706.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___992_4706.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___992_4706.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___992_4706.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___992_4706.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___992_4706.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___992_4706.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___992_4706.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___992_4706.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___992_4706.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___992_4706.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___992_4709 = env1 in
                     let uu____4710 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___992_4709.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___992_4709.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___992_4709.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___992_4709.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___992_4709.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___992_4709.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___992_4709.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___992_4709.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___992_4709.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___992_4709.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___992_4709.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___992_4709.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___992_4709.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___992_4709.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___992_4709.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___992_4709.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___992_4709.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___992_4709.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___992_4709.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___992_4709.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___992_4709.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___992_4709.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___992_4709.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___992_4709.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___992_4709.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___992_4709.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___992_4709.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___992_4709.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___992_4709.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___992_4709.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___992_4709.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___992_4709.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___992_4709.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___992_4709.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4710;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___992_4709.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___992_4709.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___992_4709.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___992_4709.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___992_4709.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___992_4709.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___992_4709.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___992_4709.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___992_4709.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___992_4709.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___992_4709.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___992_4709.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____4711) ->
                  if from_cache
                  then env1
                  else
                    (let uu___992_4713 = env1 in
                     let uu____4714 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___992_4713.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___992_4713.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___992_4713.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___992_4713.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___992_4713.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___992_4713.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___992_4713.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___992_4713.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___992_4713.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___992_4713.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___992_4713.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___992_4713.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___992_4713.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___992_4713.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___992_4713.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___992_4713.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___992_4713.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___992_4713.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___992_4713.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___992_4713.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___992_4713.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___992_4713.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___992_4713.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___992_4713.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___992_4713.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___992_4713.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___992_4713.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___992_4713.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___992_4713.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___992_4713.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___992_4713.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___992_4713.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___992_4713.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___992_4713.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4714;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___992_4713.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___992_4713.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___992_4713.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___992_4713.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___992_4713.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___992_4713.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___992_4713.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___992_4713.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___992_4713.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___992_4713.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___992_4713.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___992_4713.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____4715) ->
                  if from_cache
                  then env1
                  else
                    (let uu___992_4719 = env1 in
                     let uu____4720 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___992_4719.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___992_4719.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___992_4719.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___992_4719.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___992_4719.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___992_4719.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___992_4719.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___992_4719.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___992_4719.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___992_4719.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___992_4719.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___992_4719.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___992_4719.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___992_4719.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___992_4719.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___992_4719.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___992_4719.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___992_4719.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___992_4719.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___992_4719.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___992_4719.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___992_4719.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___992_4719.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___992_4719.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___992_4719.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___992_4719.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___992_4719.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___992_4719.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___992_4719.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___992_4719.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___992_4719.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___992_4719.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___992_4719.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___992_4719.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4720;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___992_4719.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___992_4719.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___992_4719.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___992_4719.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___992_4719.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___992_4719.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___992_4719.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___992_4719.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___992_4719.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___992_4719.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___992_4719.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___992_4719.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                            let uu____4734 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____4734)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
                    se.FStar_Syntax_Syntax.sigrng
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m, n, p, uu____4739, ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  (m, n, uu____4743, ty) ->
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n ty
              | uu____4745 -> env1))
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____4813 se =
        match uu____4813 with
        | (ses1, exports, env1, hidden) ->
            let uu____4865 =
              env1.FStar_TypeChecker_Env.nosynth &&
                (FStar_Options.debug_any ()) in
            if uu____4865
            then ((ses1, exports, env1, hidden), [])
            else
              ((let uu____4910 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                if uu____4910
                then
                  let uu____4911 = FStar_Syntax_Print.tag_of_sigelt se in
                  let uu____4912 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                    uu____4911 uu____4912
                else ());
               (let uu____4914 = tc_decl env1 se in
                match uu____4914 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_All.pipe_right ses'
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4967 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4967
                               then
                                 let uu____4968 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from %s\n" uu____4968
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_All.pipe_right ses_elaborated
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4981 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4981
                               then
                                 let uu____4982 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu____4982
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
                             (fun env3 ->
                                fun se1 -> add_sigelt_to_env env3 se1 false)
                             env2) in
                      FStar_Syntax_Unionfind.reset ();
                      (let uu____4996 =
                         (FStar_Options.log_types ()) ||
                           (FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu____4996
                       then
                         let uu____4997 =
                           FStar_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu____5003 =
                                    let uu____5004 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu____5004 "\n" in
                                  Prims.op_Hat s uu____5003) "" ses'1 in
                         FStar_Util.print1 "Checked: %s\n" uu____4997
                       else ());
                      FStar_List.iter
                        (fun se1 ->
                           (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                             env3 se1) ses'1;
                      (let uu____5009 =
                         let uu____5018 =
                           FStar_Options.use_extracted_interfaces () in
                         if uu____5018
                         then ((FStar_List.rev_append ses'1 exports), [])
                         else
                           (let accum_exports_hidden uu____5057 se1 =
                              match uu____5057 with
                              | (exports1, hidden1) ->
                                  let uu____5085 =
                                    for_export env3 hidden1 se1 in
                                  (match uu____5085 with
                                   | (se_exported, hidden2) ->
                                       ((FStar_List.rev_append se_exported
                                           exports1), hidden2)) in
                            FStar_List.fold_left accum_exports_hidden
                              (exports, hidden) ses'1) in
                       match uu____5009 with
                       | (exports1, hidden1) ->
                           (((FStar_List.rev_append ses'1 ses1), exports1,
                              env3, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____5239 = acc in
        match uu____5239 with
        | (uu____5274, uu____5275, env1, uu____5277) ->
            let r =
              let uu____5311 =
                let uu____5314 =
                  let uu____5315 = FStar_TypeChecker_Env.current_module env1 in
                  FStar_Ident.string_of_lid uu____5315 in
                FStar_Pervasives_Native.Some uu____5314 in
              FStar_Profiling.profile
                (fun uu____5337 -> process_one_decl acc se) uu____5311
                "FStar.TypeChecker.Tc.process_one_decl" in
            ((let uu____5339 = FStar_Options.profile_group_by_decls () in
              if uu____5339
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____5342 -> FStar_Ident.string_of_lid hd
                  | uu____5345 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se) in
                FStar_Profiling.report_and_clear tag
              else ());
             r) in
      let uu____5349 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____5379 ->
             FStar_Util.fold_flatten process_one_decl_timed ([], [], env, [])
               ses) in
      match uu____5349 with
      | (ses1, exports, env1, uu____5413) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let (uu___1090 : unit) =
  FStar_ST.op_Colon_Equals tc_decls_knot
    (FStar_Pervasives_Native.Some tc_decls)
let (check_exports :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      FStar_Syntax_Syntax.sigelt Prims.list -> unit)
  =
  fun env ->
    fun modul ->
      fun exports ->
        let env1 =
          let uu___1094_5514 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1094_5514.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1094_5514.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1094_5514.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1094_5514.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1094_5514.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1094_5514.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1094_5514.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1094_5514.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1094_5514.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1094_5514.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1094_5514.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1094_5514.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1094_5514.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1094_5514.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1094_5514.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1094_5514.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1094_5514.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1094_5514.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1094_5514.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1094_5514.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1094_5514.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1094_5514.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1094_5514.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1094_5514.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1094_5514.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1094_5514.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1094_5514.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1094_5514.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1094_5514.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1094_5514.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1094_5514.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1094_5514.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1094_5514.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1094_5514.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1094_5514.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1094_5514.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1094_5514.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1094_5514.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1094_5514.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1094_5514.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1094_5514.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1094_5514.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1094_5514.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1094_5514.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let check_term lid univs t =
          let uu____5531 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____5531 with
          | (univs1, t1) ->
              ((let uu____5539 =
                  let uu____5540 =
                    let uu____5545 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5545 in
                  FStar_All.pipe_left uu____5540
                    (FStar_Options.Other "Exports") in
                if uu____5539
                then
                  let uu____5546 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5547 =
                    let uu____5548 =
                      FStar_All.pipe_right univs1
                        (FStar_List.map
                           (fun x ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5548
                      (FStar_String.concat ", ") in
                  let uu____5559 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5546 uu____5547 uu____5559
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs1 in
                let uu____5562 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5562 (fun uu____5571 -> ()))) in
        let check_term1 lid univs t =
          (let uu____5589 =
             let uu____5590 =
               FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
             let uu____5591 = FStar_Ident.string_of_lid lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5590 uu____5591 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5589);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____5600) ->
              let uu____5609 =
                let uu____5610 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5610 in
              if uu____5609
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l, univs, binders, typ, uu____5620, uu____5621) ->
              let t =
                let uu____5633 =
                  let uu____5634 =
                    let uu____5649 = FStar_Syntax_Syntax.mk_Total typ in
                    (binders, uu____5649) in
                  FStar_Syntax_Syntax.Tm_arrow uu____5634 in
                FStar_Syntax_Syntax.mk uu____5633
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l, univs, t, uu____5665, uu____5666, uu____5667) ->
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t) ->
              let uu____5675 =
                let uu____5676 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5676 in
              if uu____5675 then check_term1 l univs t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____5680, lbs), uu____5682) ->
              let uu____5691 =
                let uu____5692 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5692 in
              if uu____5691
              then
                FStar_All.pipe_right lbs
                  (FStar_List.iter
                     (fun lb ->
                        let fv =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        check_term1
                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                          lb.FStar_Syntax_Syntax.lbunivs
                          lb.FStar_Syntax_Syntax.lbtyp))
              else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev
              (l, univs, binders, comp, flags) ->
              let uu____5711 =
                let uu____5712 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5712 in
              if uu____5711
              then
                let arrow =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_assume uu____5729 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5736 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5737 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5738 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5739 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5750 -> ()
          | FStar_Syntax_Syntax.Sig_fail uu____5759 ->
              failwith "Impossible (Already handled)"
          | FStar_Syntax_Syntax.Sig_splice uu____5770 ->
              failwith "Impossible (Already handled)" in
        let uu____5777 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____5777 then () else FStar_List.iter check_sigelt exports
let (extract_interface :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul -> FStar_Syntax_Syntax.modul)
  =
  fun en ->
    fun m ->
      let is_abstract = FStar_List.contains FStar_Syntax_Syntax.Abstract in
      let is_irreducible =
        FStar_List.contains FStar_Syntax_Syntax.Irreducible in
      let is_assume = FStar_List.contains FStar_Syntax_Syntax.Assumption in
      let filter_out_abstract =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((q = FStar_Syntax_Syntax.Abstract) ||
                   (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_noeq =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Noeq))
                    || (q = FStar_Syntax_Syntax.Unopteq))
                   || (q = FStar_Syntax_Syntax.Irreducible))
                  || (q = FStar_Syntax_Syntax.Visible_default))) in
      let filter_out_abstract_and_inline =
        FStar_List.filter
          (fun q ->
             Prims.op_Negation
               (((((q = FStar_Syntax_Syntax.Abstract) ||
                     (q = FStar_Syntax_Syntax.Irreducible))
                    || (q = FStar_Syntax_Syntax.Visible_default))
                   || (q = FStar_Syntax_Syntax.Inline_for_extraction))
                  ||
                  (q = FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))) in
      let abstract_inductive_tycons = FStar_Util.mk_ref [] in
      let abstract_inductive_datacons = FStar_Util.mk_ref [] in
      let is_projector_or_discriminator_of_an_abstract_inductive quals =
        FStar_List.existsML
          (fun q ->
             match q with
             | FStar_Syntax_Syntax.Discriminator l -> true
             | FStar_Syntax_Syntax.Projector (l, uu____5872) -> true
             | uu____5873 -> false) quals in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____5902 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs', c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c)) r
               | uu____5941 ->
                   let uu____5942 =
                     let uu____5943 =
                       let uu____5958 = FStar_Syntax_Syntax.mk_Total t in
                       (bs, uu____5958) in
                     FStar_Syntax_Syntax.Tm_arrow uu____5943 in
                   FStar_Syntax_Syntax.mk uu____5942 r) in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, uvs, bs, t, uu____5975, uu____5976) ->
            let s1 =
              let uu___1222_5986 = s in
              let uu____5987 =
                let uu____5988 =
                  let uu____5995 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng in
                  (lid, uvs, uu____5995) in
                FStar_Syntax_Syntax.Sig_declare_typ uu____5988 in
              let uu____5996 =
                let uu____5999 =
                  let uu____6002 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals in
                  FStar_Syntax_Syntax.New :: uu____6002 in
                FStar_Syntax_Syntax.Assumption :: uu____5999 in
              {
                FStar_Syntax_Syntax.sigel = uu____5987;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1222_5986.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____5996;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1222_5986.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1222_5986.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1222_5986.FStar_Syntax_Syntax.sigopts)
              } in
            [s1]
        | uu____6005 -> failwith "Impossible!" in
      let val_of_lb s lid uu____6029 lbdef =
        match uu____6029 with
        | (uvs, t) ->
            let attrs =
              let uu____6040 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef in
              if uu____6040
              then
                let uu____6043 =
                  let uu____6044 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_right uu____6044
                    FStar_Syntax_Syntax.fv_to_tm in
                uu____6043 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs in
            let uu___1235_6046 = s in
            let uu____6047 =
              let uu____6050 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals in
              FStar_Syntax_Syntax.Assumption :: uu____6050 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1235_6046.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6047;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1235_6046.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1235_6046.FStar_Syntax_Syntax.sigopts)
            } in
      let should_keep_lbdef t =
        let comp_effect_name c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6066 -> failwith "Impossible!" in
        let c_opt =
          let uu____6072 = FStar_Syntax_Util.is_unit t in
          if uu____6072
          then
            let uu____6077 = FStar_Syntax_Syntax.mk_Total t in
            FStar_Pervasives_Native.Some uu____6077
          else
            (let uu____6083 =
               let uu____6084 = FStar_Syntax_Subst.compress t in
               uu____6084.FStar_Syntax_Syntax.n in
             match uu____6083 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6091, c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6115 -> FStar_Pervasives_Native.None) in
        match c_opt with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6125 = FStar_Syntax_Util.is_lemma_comp c in
            if uu____6125
            then false
            else
              (let uu____6127 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
               if uu____6127
               then true
               else
                 (let uu____6129 = comp_effect_name c in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6129)) in
      let extract_sigelt s =
        (let uu____6141 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme in
         if uu____6141
         then
           let uu____6142 = FStar_Syntax_Print.sigelt_to_string s in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6142
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6146 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6165 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6182 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu____6191 ->
             failwith
               "Impossible! extract_interface: trying to extract Sig_fail"
         | FStar_Syntax_Syntax.Sig_bundle (sigelts, lidents) ->
             if is_abstract s.FStar_Syntax_Syntax.sigquals
             then
               FStar_All.pipe_right sigelts
                 (FStar_List.fold_left
                    (fun sigelts1 ->
                       fun s1 ->
                         match s1.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (lid, uu____6239, uu____6240, uu____6241,
                              uu____6242, uu____6243)
                             ->
                             ((let uu____6253 =
                                 let uu____6256 =
                                   FStar_ST.op_Bang abstract_inductive_tycons in
                                 lid :: uu____6256 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____6253);
                              (let uu____6279 = vals_of_abstract_inductive s1 in
                               FStar_List.append uu____6279 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid, uu____6283, uu____6284, uu____6285,
                              uu____6286, uu____6287)
                             ->
                             ((let uu____6293 =
                                 let uu____6296 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons in
                                 lid :: uu____6296 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____6293);
                              sigelts1)
                         | uu____6319 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
             let uu____6326 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____6326
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____6332 =
                    let uu___1301_6333 = s in
                    let uu____6334 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1301_6333.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1301_6333.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____6334;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1301_6333.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1301_6333.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1301_6333.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____6332])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let uu____6344 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____6344
             then []
             else
               (let uu____6348 = lbs in
                match uu____6348 with
                | (flbs, slbs) ->
                    let typs_and_defs =
                      FStar_All.pipe_right slbs
                        (FStar_List.map
                           (fun lb ->
                              ((lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp),
                                (lb.FStar_Syntax_Syntax.lbdef)))) in
                    let is_lemma =
                      FStar_List.existsML
                        (fun uu____6407 ->
                           match uu____6407 with
                           | (uu____6414, t, uu____6416) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs in
                    let vals =
                      FStar_List.map2
                        (fun lid ->
                           fun uu____6432 ->
                             match uu____6432 with
                             | (u, t, d) -> val_of_lb s lid (u, t) d) lids
                        typs_and_defs in
                    if
                      ((is_abstract s.FStar_Syntax_Syntax.sigquals) ||
                         (is_irreducible s.FStar_Syntax_Syntax.sigquals))
                        || is_lemma
                    then vals
                    else
                      (let should_keep_defs =
                         FStar_List.existsML
                           (fun uu____6456 ->
                              match uu____6456 with
                              | (uu____6463, t, uu____6465) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_assume (lid, uu____6470, uu____6471) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____6476 = FStar_ST.op_Bang abstract_inductive_tycons in
                 FStar_List.existsML
                   (fun l ->
                      let uu____6492 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l in
                      FStar_Ident.lid_equals lid uu____6492) uu____6476 in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____6495 =
                    let uu___1341_6496 = s in
                    let uu____6497 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1341_6496.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1341_6496.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____6497;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1341_6496.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1341_6496.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1341_6496.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____6495]
                else [])
             else
               (let uu____6502 =
                  let uu___1343_6503 = s in
                  let uu____6504 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1343_6503.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1343_6503.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____6504;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1343_6503.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1343_6503.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1343_6503.FStar_Syntax_Syntax.sigopts)
                  } in
                [uu____6502])
         | FStar_Syntax_Syntax.Sig_new_effect uu____6507 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____6508 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6509 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____6522 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6523 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____6534 -> [s]) in
      let uu___1357_6543 = m in
      let uu____6544 =
        let uu____6545 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt) in
        FStar_All.pipe_right uu____6545 FStar_List.flatten in
      {
        FStar_Syntax_Syntax.name = (uu___1357_6543.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____6544;
        FStar_Syntax_Syntax.exports =
          (uu___1357_6543.FStar_Syntax_Syntax.exports);
        FStar_Syntax_Syntax.is_interface = true
      }
let (snapshot_context :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun msg ->
      FStar_Util.atomically
        (fun uu____6589 -> FStar_TypeChecker_Env.snapshot env msg)
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
          (fun uu____6627 ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu____6639 = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu____6639
let (pop_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      rollback_context env.FStar_TypeChecker_Env.solver msg
        FStar_Pervasives_Native.None
let (tc_partial_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_Syntax_Syntax.sigelt Prims.list *
        FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun modul ->
      let verify =
        let uu____6697 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
        FStar_Options.should_verify uu____6697 in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____6703 = FStar_Options.debug_any () in
       if uu____6703
       then
         let uu____6704 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.print3 "%s %s of %s\n" action label uu____6704
       else ());
      (let name =
         let uu____6707 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____6707 in
       let env1 =
         let uu___1382_6710 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1382_6710.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1382_6710.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1382_6710.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1382_6710.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1382_6710.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1382_6710.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1382_6710.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1382_6710.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1382_6710.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1382_6710.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1382_6710.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1382_6710.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1382_6710.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1382_6710.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1382_6710.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1382_6710.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1382_6710.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1382_6710.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1382_6710.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1382_6710.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1382_6710.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1382_6710.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1382_6710.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1382_6710.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1382_6710.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1382_6710.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1382_6710.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1382_6710.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1382_6710.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1382_6710.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1382_6710.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1382_6710.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1382_6710.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1382_6710.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1382_6710.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1382_6710.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1382_6710.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1382_6710.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1382_6710.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1382_6710.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1382_6710.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1382_6710.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1382_6710.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1382_6710.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1382_6710.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____6712 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____6712 with
       | (ses, exports, env3) ->
           ((let uu___1390_6745 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1390_6745.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1390_6745.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1390_6745.FStar_Syntax_Syntax.is_interface)
             }), exports, env3))
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
        let uu____6773 = tc_decls env decls in
        match uu____6773 with
        | (ses, exports, env1) ->
            let modul1 =
              let uu___1399_6804 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1399_6804.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1399_6804.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1399_6804.FStar_Syntax_Syntax.is_interface)
              } in
            (modul1, exports, env1)
let rec (tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env0 ->
    fun m ->
      fun iface_exists ->
        let msg =
          let uu____6857 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____6857 in
        let env01 = push_context env0 msg in
        let uu____6859 = tc_partial_modul env01 m in
        match uu____6859 with
        | (modul, non_private_decls, env) ->
            finish_partial_modul false iface_exists env modul
              non_private_decls
and (finish_partial_modul :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.modul ->
          FStar_Syntax_Syntax.sigelt Prims.list ->
            (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun loading_from_cache ->
    fun iface_exists ->
      fun en ->
        fun m ->
          fun exports ->
            let should_extract_interface =
              ((((Prims.op_Negation loading_from_cache) &&
                   (Prims.op_Negation iface_exists))
                  && (FStar_Options.use_extracted_interfaces ()))
                 && (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
                &&
                (let uu____6892 = FStar_Errors.get_err_count () in
                 uu____6892 = Prims.int_zero) in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m in
              ((let uu____6899 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low in
                if uu____6899
                then
                  let uu____6900 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  let uu____6901 =
                    let uu____6902 =
                      let uu____6903 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.should_verify uu____6903 in
                    if uu____6902 then "" else " (in lax mode) " in
                  let uu____6905 =
                    let uu____6906 =
                      let uu____6907 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____6907 in
                    if uu____6906
                    then
                      let uu____6908 =
                        let uu____6909 = FStar_Syntax_Print.modul_to_string m in
                        Prims.op_Hat uu____6909 "\n" in
                      Prims.op_Hat "\nfrom: " uu____6908
                    else "" in
                  let uu____6911 =
                    let uu____6912 =
                      let uu____6913 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____6913 in
                    if uu____6912
                    then
                      let uu____6914 =
                        let uu____6915 =
                          FStar_Syntax_Print.modul_to_string modul_iface in
                        Prims.op_Hat uu____6915 "\n" in
                      Prims.op_Hat "\nto: " uu____6914
                    else "" in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    uu____6900 uu____6901 uu____6905 uu____6911
                else ());
               (let en0 =
                  let en0 =
                    let uu____6920 =
                      let uu____6921 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      Prims.op_Hat "Ending modul " uu____6921 in
                    pop_context en uu____6920 in
                  let en01 =
                    let uu___1425_6923 = en0 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1425_6923.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1425_6923.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1425_6923.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1425_6923.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1425_6923.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1425_6923.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1425_6923.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1425_6923.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1425_6923.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1425_6923.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1425_6923.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1425_6923.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1425_6923.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1425_6923.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1425_6923.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1425_6923.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1425_6923.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1425_6923.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1425_6923.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1425_6923.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1425_6923.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1425_6923.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1425_6923.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1425_6923.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1425_6923.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1425_6923.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1425_6923.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1425_6923.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1425_6923.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1425_6923.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1425_6923.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1425_6923.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1425_6923.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1425_6923.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1425_6923.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1425_6923.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1425_6923.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1425_6923.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1425_6923.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1425_6923.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1425_6923.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1425_6923.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1425_6923.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1425_6923.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1425_6923.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1425_6923.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let en02 =
                    let uu___1428_6925 = en01 in
                    let uu____6926 =
                      let uu____6939 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst in
                      (uu____6939, FStar_Pervasives_Native.None) in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1428_6925.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1428_6925.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1428_6925.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1428_6925.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1428_6925.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1428_6925.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1428_6925.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1428_6925.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1428_6925.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1428_6925.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1428_6925.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1428_6925.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1428_6925.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1428_6925.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1428_6925.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1428_6925.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1428_6925.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1428_6925.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1428_6925.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1428_6925.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1428_6925.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1428_6925.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1428_6925.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1428_6925.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1428_6925.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1428_6925.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1428_6925.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1428_6925.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1428_6925.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1428_6925.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1428_6925.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____6926;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1428_6925.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1428_6925.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1428_6925.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1428_6925.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1428_6925.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1428_6925.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1428_6925.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1428_6925.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1428_6925.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1428_6925.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1428_6925.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1428_6925.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1428_6925.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1428_6925.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1428_6925.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let uu____6976 =
                    let uu____6977 = FStar_Options.interactive () in
                    Prims.op_Negation uu____6977 in
                  if uu____6976
                  then
                    ((let uu____6979 =
                        FStar_Options.restore_cmd_line_options true in
                      FStar_All.pipe_right uu____6979 (fun uu____6980 -> ()));
                     en02)
                  else en02 in
                let uu____6982 = tc_modul en0 modul_iface true in
                match uu____6982 with
                | (modul_iface1, env) ->
                    ((let uu___1437_6994 = m in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1437_6994.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1437_6994.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1437_6994.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1439_6997 = m in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1439_6997.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1439_6997.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1439_6997.FStar_Syntax_Syntax.is_interface)
                 } in
               let env = FStar_TypeChecker_Env.finish_module en modul in
               (let uu____7000 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____7000 FStar_Util.smap_clear);
               (let uu____7028 =
                  ((let uu____7031 = FStar_Options.lax () in
                    Prims.op_Negation uu____7031) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____7033 =
                       FStar_Options.use_extracted_interfaces () in
                     Prims.op_Negation uu____7033) in
                if uu____7028
                then
                  FStar_Syntax_Unionfind.with_uf_enabled
                    (fun uu____7035 -> check_exports env modul exports)
                else ());
               (let uu____7038 =
                  let uu____7039 =
                    let uu____7040 =
                      FStar_Ident.string_of_lid
                        modul.FStar_Syntax_Syntax.name in
                    Prims.op_Hat "Ending modul " uu____7040 in
                  pop_context env uu____7039 in
                FStar_All.pipe_right uu____7038 (fun uu____7041 -> ()));
               (modul, env))
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
        let uu____7054 =
          let uu____7055 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____7055 in
        push_context env uu____7054 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = add_sigelt_to_env env2 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____7074 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____7077 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports in
      match uu____7077 with | (uu____7082, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu____7104 = FStar_Options.debug_any () in
         if uu____7104
         then
           let uu____7105 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____7105
         else ());
        (let uu____7109 =
           let uu____7110 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.dump_module uu____7110 in
         if uu____7109
         then
           let uu____7111 = FStar_Syntax_Print.modul_to_string m in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____7111
         else ());
        (let env1 =
           let uu___1470_7114 = env in
           let uu____7115 =
             let uu____7116 =
               let uu____7117 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu____7117 in
             Prims.op_Negation uu____7116 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1470_7114.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1470_7114.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1470_7114.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1470_7114.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1470_7114.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1470_7114.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1470_7114.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1470_7114.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1470_7114.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1470_7114.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1470_7114.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1470_7114.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1470_7114.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1470_7114.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1470_7114.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1470_7114.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1470_7114.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1470_7114.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1470_7114.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1470_7114.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____7115;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1470_7114.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1470_7114.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1470_7114.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1470_7114.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1470_7114.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1470_7114.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1470_7114.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1470_7114.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1470_7114.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1470_7114.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1470_7114.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1470_7114.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1470_7114.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1470_7114.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1470_7114.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1470_7114.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1470_7114.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1470_7114.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1470_7114.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1470_7114.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1470_7114.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1470_7114.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1470_7114.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1470_7114.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1470_7114.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___1470_7114.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         let uu____7118 = tc_modul env1 m b in
         match uu____7118 with
         | (m1, env2) ->
             ((let uu____7130 =
                 let uu____7131 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                 FStar_Options.dump_module uu____7131 in
               if uu____7130
               then
                 let uu____7132 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____7132
               else ());
              (let uu____7135 =
                 (let uu____7138 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                  FStar_Options.dump_module uu____7138) &&
                   (let uu____7140 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                    FStar_Options.debug_at_level uu____7140
                      (FStar_Options.Other "Normalize")) in
               if uu____7135
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
                         let uu____7173 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____7173 with
                         | (univnames, e) ->
                             let uu___1492_7180 = lb in
                             let uu____7181 =
                               let uu____7184 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu____7184 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____7181;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1492_7180.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___1494_7185 = se in
                       let uu____7186 =
                         let uu____7187 =
                           let uu____7194 =
                             let uu____7195 = FStar_List.map update lbs in
                             (b1, uu____7195) in
                           (uu____7194, ids) in
                         FStar_Syntax_Syntax.Sig_let uu____7187 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____7186;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1494_7185.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1494_7185.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1494_7185.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1494_7185.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1494_7185.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____7202 -> se in
                 let normalized_module =
                   let uu___1498_7204 = m1 in
                   let uu____7205 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1498_7204.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____7205;
                     FStar_Syntax_Syntax.exports =
                       (uu___1498_7204.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1498_7204.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____7206 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____7206
               else ());
              (m1, env2)))