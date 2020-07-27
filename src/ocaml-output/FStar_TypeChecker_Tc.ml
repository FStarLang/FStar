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
                          FStar_Syntax_Syntax.pos = uu____1702;
                          FStar_Syntax_Syntax.vars = uu____1703;_} -> true
                      | uu____1706 -> false)
                 | uu____1709 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____1721 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu____1721 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___346_1760 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___346_1760.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___346_1760.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___346_1760.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___346_1760.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___346_1760.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [(let uu___349_1762 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___349_1762.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___349_1762.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___349_1762.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___349_1762.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___349_1762.FStar_Syntax_Syntax.sigopts)
                              })] in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____1769 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env) in
                    if uu____1769
                    then
                      let ne1 =
                        let uu____1771 =
                          let uu____1772 =
                            let uu____1773 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___353_1776 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___353_1776.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___353_1776.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___353_1776.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___353_1776.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___353_1776.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___353_1776.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___353_1776.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___353_1776.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___353_1776.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___353_1776.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___353_1776.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___353_1776.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___353_1776.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___353_1776.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___353_1776.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___353_1776.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___353_1776.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___353_1776.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___353_1776.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___353_1776.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___353_1776.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___353_1776.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___353_1776.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___353_1776.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___353_1776.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___353_1776.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___353_1776.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___353_1776.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___353_1776.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___353_1776.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___353_1776.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___353_1776.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___353_1776.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___353_1776.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___353_1776.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___353_1776.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___353_1776.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___353_1776.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___353_1776.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___353_1776.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___353_1776.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___353_1776.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___353_1776.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___353_1776.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___353_1776.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals in
                            FStar_All.pipe_right uu____1773
                              (fun ne1 ->
                                 let uu___356_1780 = se1 in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___356_1780.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___356_1780.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___356_1780.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___356_1780.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___356_1780.FStar_Syntax_Syntax.sigopts)
                                 }) in
                          FStar_All.pipe_right uu____1772
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_All.pipe_right uu____1771
                          FStar_Syntax_Util.eff_decl_of_new_effect in
                      ((let uu____1782 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases") in
                        if uu____1782
                        then
                          let uu____1783 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___360_1786 = se1 in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___360_1786.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___360_1786.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___360_1786.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___360_1786.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___360_1786.FStar_Syntax_Syntax.sigopts)
                               }) in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____1783
                        else ());
                       ne1)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals in
                  let se2 =
                    let uu___365_1791 = se1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___365_1791.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___365_1791.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___365_1791.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___365_1791.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___365_1791.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se2 =
                 let uu___371_1799 = se1 in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___371_1799.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___371_1799.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___371_1799.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___371_1799.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___371_1799.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags)
               ->
               let uu____1813 =
                 let uu____1822 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____1822
                 then
                   let uu____1831 =
                     let uu____1832 =
                       let uu____1833 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___382_1844 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___382_1844.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___382_1844.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___382_1844.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___382_1844.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___382_1844.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___382_1844.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___382_1844.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___382_1844.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___382_1844.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___382_1844.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___382_1844.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___382_1844.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___382_1844.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___382_1844.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___382_1844.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___382_1844.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___382_1844.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___382_1844.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___382_1844.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___382_1844.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___382_1844.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___382_1844.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___382_1844.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___382_1844.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___382_1844.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___382_1844.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___382_1844.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___382_1844.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___382_1844.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___382_1844.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___382_1844.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___382_1844.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___382_1844.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___382_1844.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___382_1844.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___382_1844.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___382_1844.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___382_1844.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___382_1844.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___382_1844.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___382_1844.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___382_1844.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___382_1844.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___382_1844.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___382_1844.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) (lid, uvs, tps, c) r in
                       FStar_All.pipe_right uu____1833
                         (fun uu____1859 ->
                            match uu____1859 with
                            | (lid1, uvs1, tps1, c1) ->
                                let uu___389_1872 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___389_1872.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___389_1872.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___389_1872.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___389_1872.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___389_1872.FStar_Syntax_Syntax.sigopts)
                                }) in
                     FStar_All.pipe_right uu____1832
                       (FStar_TypeChecker_Normalize.elim_uvars env) in
                   FStar_All.pipe_right uu____1831
                     (fun se2 ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1, uvs1, tps1, c1, uu____1902) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____1907 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu____1813 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu____1931 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu____1931 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se2 =
                           let uu___410_1955 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___410_1955.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___410_1955.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___410_1955.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___410_1955.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___410_1955.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____1962, uu____1963, uu____1964) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1968 ->
                       match uu___0_1968 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1969 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____1974, uu____1975) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1983 ->
                       match uu___0_1983 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1984 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu____1994 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu____1994
                 then
                   let uu____1995 =
                     let uu____2000 =
                       let uu____2001 = FStar_Ident.string_of_lid lid in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____2001 in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____2000) in
                   FStar_Errors.raise_error uu____1995 r
                 else ());
                (let uu____2003 =
                   let uu____2012 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2012
                   then
                     let uu____2021 =
                       tc_declare_typ
                         (let uu___434_2024 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___434_2024.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___434_2024.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___434_2024.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___434_2024.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___434_2024.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___434_2024.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___434_2024.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___434_2024.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___434_2024.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___434_2024.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___434_2024.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___434_2024.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___434_2024.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___434_2024.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___434_2024.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___434_2024.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___434_2024.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___434_2024.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___434_2024.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___434_2024.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___434_2024.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___434_2024.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___434_2024.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___434_2024.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___434_2024.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___434_2024.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___434_2024.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___434_2024.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___434_2024.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___434_2024.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___434_2024.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___434_2024.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___434_2024.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___434_2024.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___434_2024.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___434_2024.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___434_2024.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___434_2024.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___434_2024.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___434_2024.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___434_2024.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___434_2024.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___434_2024.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___434_2024.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___434_2024.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2021 with
                     | (uvs1, t1) ->
                         ((let uu____2048 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2048
                           then
                             let uu____2049 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2050 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____2049 uu____2050
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2003 with
                 | (uvs1, t1) ->
                     let uu____2081 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2081 with
                      | (uvs2, t2) ->
                          ([(let uu___447_2111 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___447_2111.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___447_2111.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___447_2111.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___447_2111.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___447_2111.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
               ((let uu____2116 =
                   let uu____2121 =
                     let uu____2122 = FStar_Syntax_Print.lid_to_string lid in
                     FStar_Util.format1 "Admitting a top-level assumption %s"
                       uu____2122 in
                   (FStar_Errors.Warning_WarnOnUse, uu____2121) in
                 FStar_Errors.log_issue r uu____2116);
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____2124 =
                   let uu____2133 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2133
                   then
                     let uu____2142 =
                       tc_assume
                         (let uu___457_2145 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___457_2145.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___457_2145.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___457_2145.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___457_2145.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___457_2145.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___457_2145.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___457_2145.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___457_2145.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___457_2145.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___457_2145.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___457_2145.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___457_2145.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___457_2145.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___457_2145.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___457_2145.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___457_2145.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___457_2145.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___457_2145.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___457_2145.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___457_2145.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___457_2145.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___457_2145.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___457_2145.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___457_2145.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___457_2145.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___457_2145.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___457_2145.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___457_2145.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___457_2145.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___457_2145.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___457_2145.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___457_2145.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___457_2145.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___457_2145.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___457_2145.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___457_2145.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___457_2145.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___457_2145.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___457_2145.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___457_2145.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___457_2145.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___457_2145.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___457_2145.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___457_2145.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___457_2145.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2142 with
                     | (uvs1, t1) ->
                         ((let uu____2169 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2169
                           then
                             let uu____2170 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2171 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Assume after phase 1: %s and uvs: %s\n"
                               uu____2170 uu____2171
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2124 with
                 | (uvs1, t1) ->
                     let uu____2202 =
                       tc_assume env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2202 with
                      | (uvs2, t2) ->
                          ([(let uu___470_2232 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_assume
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___470_2232.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___470_2232.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___470_2232.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___470_2232.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___470_2232.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
               ((let uu____2240 = FStar_Options.debug_any () in
                 if uu____2240
                 then
                   let uu____2241 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu____2242 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2241
                     uu____2242
                 else ());
                (let uu____2244 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t in
                 match uu____2244 with
                 | (t1, uu____2262, g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses =
                         env.FStar_TypeChecker_Env.splice env
                           se1.FStar_Syntax_Syntax.sigrng t1 in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses in
                       FStar_List.iter
                         (fun lid ->
                            let uu____2276 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids' in
                            match uu____2276 with
                            | FStar_Pervasives_Native.None when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2279 =
                                  let uu____2284 =
                                    let uu____2285 =
                                      FStar_Ident.string_of_lid lid in
                                    let uu____2286 =
                                      let uu____2287 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids' in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2287 in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2285 uu____2286 in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2284) in
                                FStar_Errors.raise_error uu____2279 r
                            | uu____2292 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses in
                        let env1 =
                          let uu___490_2297 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___490_2297.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___490_2297.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___490_2297.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___490_2297.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___490_2297.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___490_2297.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___490_2297.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___490_2297.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___490_2297.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___490_2297.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___490_2297.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___490_2297.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___490_2297.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___490_2297.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___490_2297.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___490_2297.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___490_2297.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___490_2297.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___490_2297.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___490_2297.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___490_2297.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___490_2297.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___490_2297.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___490_2297.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___490_2297.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___490_2297.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___490_2297.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___490_2297.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___490_2297.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___490_2297.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___490_2297.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___490_2297.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___490_2297.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___490_2297.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___490_2297.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___490_2297.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___490_2297.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___490_2297.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___490_2297.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___490_2297.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___490_2297.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___490_2297.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___490_2297.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___490_2297.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___490_2297.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___490_2297.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                     let uu____2365 =
                       let uu____2366 =
                         let uu____2375 = drop_logic val_q in
                         let uu____2378 = drop_logic q' in
                         (uu____2375, uu____2378) in
                       match uu____2366 with
                       | (val_q1, q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                     if uu____2365
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2402 =
                          let uu____2407 =
                            let uu____2408 =
                              FStar_Syntax_Print.lid_to_string l in
                            let uu____2409 =
                              FStar_Syntax_Print.quals_to_string val_q in
                            let uu____2410 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2408 uu____2409 uu____2410 in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2407) in
                        FStar_Errors.raise_error uu____2402 r) in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ in
                   let def_bs =
                     let uu____2444 =
                       let uu____2445 = FStar_Syntax_Subst.compress def in
                       uu____2445.FStar_Syntax_Syntax.n in
                     match uu____2444 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders, uu____2457, uu____2458) -> binders
                     | uu____2483 -> [] in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs, c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2495;_} ->
                       let has_auto_name bv =
                         let uu____2524 =
                           FStar_Ident.string_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.starts_with uu____2524
                           FStar_Ident.reserved_prefix in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([], uu____2600) -> val_bs1
                         | (uu____2631, []) -> val_bs1
                         | ((body_bv, uu____2663)::bt, (val_bv, aqual)::vt)
                             ->
                             let uu____2720 =
                               let uu____2727 =
                                 let uu____2732 = has_auto_name body_bv in
                                 let uu____2733 = has_auto_name val_bv in
                                 (uu____2732, uu____2733) in
                               match uu____2727 with
                               | (true, uu____2740) -> (val_bv, aqual)
                               | (false, true) ->
                                   let uu____2743 =
                                     let uu___559_2744 = val_bv in
                                     let uu____2745 =
                                       let uu____2746 =
                                         let uu____2751 =
                                           FStar_Ident.string_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname in
                                         let uu____2752 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname in
                                         (uu____2751, uu____2752) in
                                       FStar_Ident.mk_ident uu____2746 in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____2745;
                                       FStar_Syntax_Syntax.index =
                                         (uu___559_2744.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___559_2744.FStar_Syntax_Syntax.sort)
                                     } in
                                   (uu____2743, aqual)
                               | (false, false) -> (val_bv, aqual) in
                             let uu____2757 = rename_binders bt vt in
                             uu____2720 :: uu____2757 in
                       let uu____2772 =
                         let uu____2773 =
                           let uu____2788 = rename_binders def_bs val_bs in
                           (uu____2788, c) in
                         FStar_Syntax_Syntax.Tm_arrow uu____2773 in
                       FStar_Syntax_Syntax.mk uu____2772 r1
                   | uu____2807 -> typ1 in
                 let uu___565_2808 = lb in
                 let uu____2809 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___565_2808.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___565_2808.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____2809;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___565_2808.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___565_2808.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___565_2808.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___565_2808.FStar_Syntax_Syntax.lbpos)
                 } in
               let uu____2812 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____2863 ->
                         fun lb ->
                           match uu____2863 with
                           | (gen, lbs1, quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu____2905 =
                                 let uu____2916 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 match uu____2916 with
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
                                       | uu____2989 ->
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
                                      (let uu____3032 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos)) in
                                       (false, uu____3032, quals_opt1))) in
                               (match uu____2905 with
                                | (gen1, lb1, quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals)))) in
               (match uu____2812 with
                | (should_generalize, lbs', quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3124 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3128 ->
                                    match uu___1_3128 with
                                    | FStar_Syntax_Syntax.Irreducible -> true
                                    | FStar_Syntax_Syntax.Visible_default ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                        -> true
                                    | uu____3129 -> false)) in
                          if uu____3124
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q in
                    let lbs'1 = FStar_List.rev lbs' in
                    let uu____3136 =
                      let uu____3145 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs in
                      match uu____3145 with
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
                    (match uu____3136 with
                     | (attrs, pre_tau) ->
                         let se2 =
                           let uu___623_3248 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___623_3248.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___623_3248.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___623_3248.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___623_3248.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___623_3248.FStar_Syntax_Syntax.sigopts)
                           } in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef in
                           (let uu____3262 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases") in
                            if uu____3262
                            then
                              let uu____3263 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3263
                            else ());
                           (let uu___632_3265 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___632_3265.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___632_3265.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___632_3265.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___632_3265.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___632_3265.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___632_3265.FStar_Syntax_Syntax.lbpos)
                            }) in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None -> lbs'1 in
                         let e =
                           let uu____3275 =
                             let uu____3276 =
                               let uu____3289 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_constant
                                      FStar_Const.Const_unit) r in
                               (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                 uu____3289) in
                             FStar_Syntax_Syntax.Tm_let uu____3276 in
                           FStar_Syntax_Syntax.mk uu____3275 r in
                         let env' =
                           let uu___639_3305 = env1 in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___639_3305.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___639_3305.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___639_3305.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___639_3305.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___639_3305.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___639_3305.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___639_3305.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___639_3305.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___639_3305.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___639_3305.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___639_3305.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___639_3305.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___639_3305.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___639_3305.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___639_3305.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___639_3305.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___639_3305.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___639_3305.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___639_3305.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___639_3305.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___639_3305.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___639_3305.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___639_3305.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___639_3305.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___639_3305.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___639_3305.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___639_3305.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___639_3305.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___639_3305.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___639_3305.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___639_3305.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___639_3305.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___639_3305.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___639_3305.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___639_3305.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___639_3305.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___639_3305.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___639_3305.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___639_3305.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___639_3305.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___639_3305.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___639_3305.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___639_3305.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___639_3305.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___639_3305.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let e1 =
                           let uu____3307 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env') in
                           if uu____3307
                           then
                             let drop_lbtyp e_lax =
                               let uu____3314 =
                                 let uu____3315 =
                                   FStar_Syntax_Subst.compress e_lax in
                                 uu____3315.FStar_Syntax_Syntax.n in
                               match uu____3314 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false, lb::[]), e2) ->
                                   let lb_unannotated =
                                     let uu____3333 =
                                       let uu____3334 =
                                         FStar_Syntax_Subst.compress e in
                                       uu____3334.FStar_Syntax_Syntax.n in
                                     match uu____3333 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3337, lb1::[]), uu____3339)
                                         ->
                                         let uu____3352 =
                                           let uu____3353 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp in
                                           uu____3353.FStar_Syntax_Syntax.n in
                                         (match uu____3352 with
                                          | FStar_Syntax_Syntax.Tm_unknown ->
                                              true
                                          | uu____3356 -> false)
                                     | uu____3357 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!" in
                                   if lb_unannotated
                                   then
                                     let uu___664_3358 = e_lax in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___666_3370 = lb in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___666_3370.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___664_3358.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___664_3358.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3372 -> e_lax in
                             let uu____3373 =
                               FStar_Util.record_time
                                 (fun uu____3380 ->
                                    let uu____3381 =
                                      let uu____3382 =
                                        let uu____3383 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___670_3392 = env' in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___670_3392.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___670_3392.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___670_3392.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___670_3392.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___670_3392.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___670_3392.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___670_3392.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___670_3392.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___670_3392.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___670_3392.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) e in
                                        FStar_All.pipe_right uu____3383
                                          (fun uu____3403 ->
                                             match uu____3403 with
                                             | (e1, uu____3411, uu____3412)
                                                 -> e1) in
                                      FStar_All.pipe_right uu____3382
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env') in
                                    FStar_All.pipe_right uu____3381
                                      drop_lbtyp) in
                             match uu____3373 with
                             | (e1, ms) ->
                                 ((let uu____3416 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases") in
                                   if uu____3416
                                   then
                                     let uu____3417 =
                                       FStar_Syntax_Print.term_to_string e1 in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3417
                                   else ());
                                  (let uu____3420 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime") in
                                   if uu____3420
                                   then
                                     let uu____3421 =
                                       FStar_Util.string_of_int ms in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____3421
                                   else ());
                                  e1)
                           else e in
                         let uu____3424 =
                           let uu____3433 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs in
                           match uu____3433 with
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
                         (match uu____3424 with
                          | (attrs1, post_tau) ->
                              let se3 =
                                let uu___700_3536 = se2 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___700_3536.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___700_3536.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___700_3536.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___700_3536.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___700_3536.FStar_Syntax_Syntax.sigopts)
                                } in
                              let postprocess_lb tau lb =
                                let lbdef =
                                  FStar_TypeChecker_Env.postprocess env1 tau
                                    lb.FStar_Syntax_Syntax.lbtyp
                                    lb.FStar_Syntax_Syntax.lbdef in
                                let uu___707_3549 = lb in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbtyp);
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___707_3549.FStar_Syntax_Syntax.lbpos)
                                } in
                              let uu____3550 =
                                FStar_Util.record_time
                                  (fun uu____3568 ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1) in
                              (match uu____3550 with
                               | (r1, ms) ->
                                   ((let uu____3594 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime") in
                                     if uu____3594
                                     then
                                       let uu____3595 =
                                         FStar_Util.string_of_int ms in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____3595
                                     else ());
                                    (let uu____3597 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1, e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____3620;
                                            FStar_Syntax_Syntax.vars =
                                              uu____3621;_},
                                          uu____3622, g) when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____3649 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters) in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____3649) in
                                           let lbs3 =
                                             let uu____3669 =
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
                                                 lbs2), uu____3669) in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____3688,
                                                  FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____3693 -> quals in
                                           ((let uu___737_3701 = se3 in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___737_3701.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___737_3701.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___737_3701.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___737_3701.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____3704 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)" in
                                     match uu____3597 with
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
                                          (let uu____3755 = log env1 in
                                           if uu____3755
                                           then
                                             let uu____3756 =
                                               let uu____3757 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb ->
                                                         let should_log =
                                                           let uu____3772 =
                                                             let uu____3781 =
                                                               let uu____3782
                                                                 =
                                                                 let uu____3785
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname in
                                                                 uu____3785.FStar_Syntax_Syntax.fv_name in
                                                               uu____3782.FStar_Syntax_Syntax.v in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____3781 in
                                                           match uu____3772
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                               -> true
                                                           | uu____3792 ->
                                                               false in
                                                         if should_log
                                                         then
                                                           let uu____3801 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname in
                                                           let uu____3802 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____3801
                                                             uu____3802
                                                         else "")) in
                                               FStar_All.pipe_right
                                                 uu____3757
                                                 (FStar_String.concat "\n") in
                                             FStar_Util.print1 "%s\n"
                                               uu____3756
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind
               (m, n, p, t, uu____3816) ->
               let t1 =
                 let uu____3818 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3818
                 then
                   let uu____3819 =
                     let uu____3824 =
                       let uu____3825 =
                         let uu____3826 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___762_3833 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___762_3833.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___762_3833.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___762_3833.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___762_3833.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___762_3833.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___762_3833.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___762_3833.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___762_3833.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___762_3833.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___762_3833.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___762_3833.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___762_3833.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___762_3833.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___762_3833.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___762_3833.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___762_3833.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___762_3833.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___762_3833.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___762_3833.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___762_3833.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___762_3833.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___762_3833.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___762_3833.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___762_3833.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___762_3833.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___762_3833.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___762_3833.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___762_3833.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___762_3833.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___762_3833.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___762_3833.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___762_3833.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___762_3833.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___762_3833.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___762_3833.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___762_3833.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___762_3833.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___762_3833.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___762_3833.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___762_3833.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___762_3833.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___762_3833.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___762_3833.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___762_3833.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___762_3833.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n p t in
                         FStar_All.pipe_right uu____3826
                           (fun uu____3842 ->
                              match uu____3842 with
                              | (t1, ty) ->
                                  let uu___767_3849 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___767_3849.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___767_3849.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___767_3849.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___767_3849.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___767_3849.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3825
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3824
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____3865, uu____3866, uu____3867, t1, ty) ->
                              (t1, ty)
                          | uu____3870 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                   match uu____3819 with
                   | (t1, ty) ->
                       ((let uu____3878 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3878
                         then
                           let uu____3879 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___782_3882 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___782_3882.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___782_3882.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___782_3882.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___782_3882.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___782_3882.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____3879
                         else ());
                        t1)
                 else t in
               let uu____3885 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu____3885 with
                | (t2, ty) ->
                    let se2 =
                      let uu___789_3903 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___789_3903.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___789_3903.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___789_3903.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___789_3903.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___789_3903.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
               (m, n, t, uu____3911) ->
               let t1 =
                 let uu____3913 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3913
                 then
                   let uu____3914 =
                     let uu____3919 =
                       let uu____3920 =
                         let uu____3921 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                             (let uu___799_3928 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___799_3928.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___799_3928.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___799_3928.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___799_3928.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___799_3928.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___799_3928.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___799_3928.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___799_3928.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___799_3928.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___799_3928.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___799_3928.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___799_3928.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___799_3928.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___799_3928.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___799_3928.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___799_3928.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___799_3928.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___799_3928.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___799_3928.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___799_3928.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___799_3928.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___799_3928.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___799_3928.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___799_3928.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___799_3928.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___799_3928.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___799_3928.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___799_3928.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___799_3928.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___799_3928.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___799_3928.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___799_3928.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___799_3928.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___799_3928.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___799_3928.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___799_3928.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___799_3928.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___799_3928.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___799_3928.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___799_3928.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___799_3928.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___799_3928.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___799_3928.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___799_3928.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___799_3928.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n t in
                         FStar_All.pipe_right uu____3921
                           (fun uu____3937 ->
                              match uu____3937 with
                              | (t1, ty) ->
                                  let uu___804_3944 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                         (m, n, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___804_3944.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___804_3944.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___804_3944.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___804_3944.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___804_3944.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3920
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3919
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                              (uu____3959, uu____3960, t1, ty) -> (t1, ty)
                          | uu____3963 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                   match uu____3914 with
                   | (t1, ty) ->
                       ((let uu____3971 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3971
                         then
                           let uu____3972 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___818_3975 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                       (m, n, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___818_3975.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___818_3975.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___818_3975.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___818_3975.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___818_3975.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic subcomp after phase 1: %s\n"
                             uu____3972
                         else ());
                        t1)
                 else t in
               let uu____3978 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu____3978 with
                | (t2, ty) ->
                    let se2 =
                      let uu___825_3996 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             (m, n, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___825_3996.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___825_3996.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___825_3996.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___825_3996.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___825_3996.FStar_Syntax_Syntax.sigopts)
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
      (let uu____4033 =
         let uu____4034 =
           FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule in
         FStar_Options.debug_module uu____4034 in
       if uu____4033
       then
         let uu____4035 =
           let uu____4036 =
             FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
               (FStar_List.map FStar_Ident.string_of_lid) in
           FStar_All.pipe_right uu____4036 (FStar_String.concat ", ") in
         FStar_Util.print1 "Processing %s\n" uu____4035
       else ());
      (let uu____4047 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____4047
       then
         let uu____4048 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4048
       else ());
      if (se.FStar_Syntax_Syntax.sigmeta).FStar_Syntax_Syntax.sigmeta_admit
      then
        (let old = FStar_Options.admit_smt_queries () in
         FStar_Options.set_admit_smt_queries true;
         (let result = tc_decl' env1 se in
          FStar_Options.set_admit_smt_queries old; result))
      else tc_decl' env1 se
let for_export :
  'uuuuuu4083 .
    'uuuuuu4083 ->
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
               (fun uu___2_4124 ->
                  match uu___2_4124 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | uu____4125 -> false)) in
        let is_hidden_proj_or_disc q =
          match q with
          | FStar_Syntax_Syntax.Projector (l, uu____4133) ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | FStar_Syntax_Syntax.Discriminator l ->
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Ident.lid_equals l))
          | uu____4139 -> false in
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_pragma uu____4148 -> ([], hidden)
        | FStar_Syntax_Syntax.Sig_fail uu____4153 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_splice uu____4172 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_inductive_typ uu____4187 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_datacon uu____4212 ->
            failwith "Impossible (Already handled)"
        | FStar_Syntax_Syntax.Sig_bundle (ses, uu____4236) ->
            let uu____4245 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4245
            then
              let for_export_bundle se1 uu____4280 =
                match uu____4280 with
                | (out, hidden1) ->
                    (match se1.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, us, bs, t, uu____4319, uu____4320) ->
                         let dec =
                           let uu___884_4330 = se1 in
                           let uu____4331 =
                             let uu____4332 =
                               let uu____4339 =
                                 let uu____4340 =
                                   FStar_Syntax_Syntax.mk_Total t in
                                 FStar_Syntax_Util.arrow bs uu____4340 in
                               (l, us, uu____4339) in
                             FStar_Syntax_Syntax.Sig_declare_typ uu____4332 in
                           {
                             FStar_Syntax_Syntax.sigel = uu____4331;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___884_4330.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (FStar_Syntax_Syntax.Assumption ::
                               FStar_Syntax_Syntax.New ::
                               (se1.FStar_Syntax_Syntax.sigquals));
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___884_4330.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___884_4330.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___884_4330.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), hidden1)
                     | FStar_Syntax_Syntax.Sig_datacon
                         (l, us, t, uu____4350, uu____4351, uu____4352) ->
                         let dec =
                           let uu___895_4358 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_declare_typ
                                  (l, us, t));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___895_4358.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               [FStar_Syntax_Syntax.Assumption];
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___895_4358.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___895_4358.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___895_4358.FStar_Syntax_Syntax.sigopts)
                           } in
                         ((dec :: out), (l :: hidden1))
                     | uu____4363 -> (out, hidden1)) in
              FStar_List.fold_right for_export_bundle ses ([], hidden)
            else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_assume (uu____4385, uu____4386, uu____4387)
            ->
            let uu____4388 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4388 then ([], hidden) else ([se], hidden)
        | FStar_Syntax_Syntax.Sig_declare_typ (l, us, t) ->
            let uu____4409 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_Util.for_some is_hidden_proj_or_disc) in
            if uu____4409
            then
              ([(let uu___911_4425 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ (l, us, t));
                   FStar_Syntax_Syntax.sigrng =
                     (uu___911_4425.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___911_4425.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___911_4425.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___911_4425.FStar_Syntax_Syntax.sigopts)
                 })], (l :: hidden))
            else
              (let uu____4427 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                   (FStar_Util.for_some
                      (fun uu___3_4431 ->
                         match uu___3_4431 with
                         | FStar_Syntax_Syntax.Assumption -> true
                         | FStar_Syntax_Syntax.Projector uu____4432 -> true
                         | FStar_Syntax_Syntax.Discriminator uu____4437 ->
                             true
                         | uu____4438 -> false)) in
               if uu____4427 then ([se], hidden) else ([], hidden))
        | FStar_Syntax_Syntax.Sig_new_effect uu____4456 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_sub_effect uu____4461 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4466 -> ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4483 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____4498 ->
            ([se], hidden)
        | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____4512) when
            FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
              (FStar_Util.for_some is_hidden_proj_or_disc)
            ->
            let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____4523 =
              FStar_All.pipe_right hidden
                (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)) in
            if uu____4523
            then ([], hidden)
            else
              (let dec =
                 let uu____4540 = FStar_Ident.range_of_lid lid in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                          (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = uu____4540;
                   FStar_Syntax_Syntax.sigquals =
                     [FStar_Syntax_Syntax.Assumption];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = [];
                   FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                 } in
               ([dec], (lid :: hidden)))
        | FStar_Syntax_Syntax.Sig_let (lbs, l) ->
            let uu____4551 = is_abstract se.FStar_Syntax_Syntax.sigquals in
            if uu____4551
            then
              let uu____4560 =
                FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                  (FStar_List.map
                     (fun lb ->
                        let uu___948_4573 = se in
                        let uu____4574 =
                          let uu____4575 =
                            let uu____4582 =
                              let uu____4583 =
                                let uu____4586 =
                                  FStar_Util.right
                                    lb.FStar_Syntax_Syntax.lbname in
                                uu____4586.FStar_Syntax_Syntax.fv_name in
                              uu____4583.FStar_Syntax_Syntax.v in
                            (uu____4582, (lb.FStar_Syntax_Syntax.lbunivs),
                              (lb.FStar_Syntax_Syntax.lbtyp)) in
                          FStar_Syntax_Syntax.Sig_declare_typ uu____4575 in
                        {
                          FStar_Syntax_Syntax.sigel = uu____4574;
                          FStar_Syntax_Syntax.sigrng =
                            (uu___948_4573.FStar_Syntax_Syntax.sigrng);
                          FStar_Syntax_Syntax.sigquals =
                            (FStar_Syntax_Syntax.Assumption ::
                            (se.FStar_Syntax_Syntax.sigquals));
                          FStar_Syntax_Syntax.sigmeta =
                            (uu___948_4573.FStar_Syntax_Syntax.sigmeta);
                          FStar_Syntax_Syntax.sigattrs =
                            (uu___948_4573.FStar_Syntax_Syntax.sigattrs);
                          FStar_Syntax_Syntax.sigopts =
                            (uu___948_4573.FStar_Syntax_Syntax.sigopts)
                        })) in
              (uu____4560, hidden)
            else ([se], hidden)
let (add_sigelt_to_env :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> Prims.bool -> FStar_TypeChecker_Env.env)
  =
  fun env ->
    fun se ->
      fun from_cache ->
        (let uu____4612 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____4612
         then
           let uu____4613 = FStar_Syntax_Print.sigelt_to_string se in
           let uu____4614 = FStar_Util.string_of_bool from_cache in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____4613 uu____4614
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____4616 ->
             let uu____4633 =
               let uu____4638 =
                 let uu____4639 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4639 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4638) in
             FStar_Errors.raise_error uu____4633
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____4640 ->
             let uu____4655 =
               let uu____4660 =
                 let uu____4661 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4661 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4660) in
             FStar_Errors.raise_error uu____4655
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____4662, uu____4663, uu____4664) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_4668 ->
                     match uu___4_4668 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4669 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____4670, uu____4671) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___4_4679 ->
                     match uu___4_4679 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4680 -> false))
             -> env
         | uu____4681 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____4683) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_4687 = env1 in
                     let uu____4688 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_4687.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_4687.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_4687.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_4687.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_4687.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_4687.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_4687.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_4687.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_4687.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_4687.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_4687.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_4687.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_4687.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_4687.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_4687.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_4687.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_4687.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_4687.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_4687.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_4687.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_4687.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_4687.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_4687.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_4687.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_4687.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_4687.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_4687.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_4687.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_4687.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_4687.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_4687.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_4687.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_4687.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_4687.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4688;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_4687.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_4687.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_4687.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_4687.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_4687.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_4687.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_4687.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_4687.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_4687.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_4687.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_4687.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_4687.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_4690 = env1 in
                     let uu____4691 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_4690.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_4690.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_4690.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_4690.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_4690.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_4690.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_4690.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_4690.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_4690.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_4690.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_4690.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_4690.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_4690.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_4690.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_4690.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_4690.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_4690.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_4690.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_4690.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_4690.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_4690.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_4690.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_4690.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_4690.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_4690.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_4690.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_4690.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_4690.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_4690.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_4690.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_4690.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_4690.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_4690.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_4690.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4691;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_4690.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_4690.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_4690.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_4690.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_4690.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_4690.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_4690.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_4690.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_4690.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_4690.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_4690.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_4690.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____4692) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_4694 = env1 in
                     let uu____4695 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_4694.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_4694.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_4694.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_4694.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_4694.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_4694.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_4694.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_4694.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_4694.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_4694.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_4694.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_4694.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_4694.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_4694.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_4694.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_4694.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_4694.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_4694.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_4694.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_4694.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_4694.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_4694.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_4694.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_4694.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_4694.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_4694.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_4694.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_4694.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_4694.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_4694.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_4694.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_4694.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_4694.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_4694.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4695;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_4694.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_4694.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_4694.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_4694.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_4694.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_4694.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_4694.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_4694.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_4694.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_4694.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_4694.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_4694.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____4696) ->
                  if from_cache
                  then env1
                  else
                    (let uu___985_4700 = env1 in
                     let uu____4701 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___985_4700.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___985_4700.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___985_4700.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___985_4700.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___985_4700.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___985_4700.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___985_4700.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___985_4700.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___985_4700.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___985_4700.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___985_4700.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___985_4700.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___985_4700.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___985_4700.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___985_4700.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___985_4700.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___985_4700.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___985_4700.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___985_4700.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___985_4700.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___985_4700.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___985_4700.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___985_4700.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___985_4700.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___985_4700.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___985_4700.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___985_4700.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___985_4700.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___985_4700.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___985_4700.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___985_4700.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___985_4700.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___985_4700.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___985_4700.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4701;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___985_4700.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___985_4700.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___985_4700.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___985_4700.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___985_4700.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___985_4700.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___985_4700.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___985_4700.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___985_4700.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___985_4700.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___985_4700.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___985_4700.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                            let uu____4715 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____4715)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m, n, p, uu____4720, ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  (m, n, uu____4724, ty) ->
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n ty
              | uu____4726 -> env1))
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____4794 se =
        match uu____4794 with
        | (ses1, exports, env1, hidden) ->
            let uu____4846 =
              env1.FStar_TypeChecker_Env.nosynth &&
                (FStar_Options.debug_any ()) in
            if uu____4846
            then ((ses1, exports, env1, hidden), [])
            else
              ((let uu____4891 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                if uu____4891
                then
                  let uu____4892 = FStar_Syntax_Print.tag_of_sigelt se in
                  let uu____4893 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                    uu____4892 uu____4893
                else ());
               (let uu____4895 = tc_decl env1 se in
                match uu____4895 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_All.pipe_right ses'
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4948 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4948
                               then
                                 let uu____4949 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from %s\n" uu____4949
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_All.pipe_right ses_elaborated
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4962 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4962
                               then
                                 let uu____4963 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu____4963
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
                      (let uu____4977 =
                         (FStar_Options.log_types ()) ||
                           (FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu____4977
                       then
                         let uu____4978 =
                           FStar_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu____4984 =
                                    let uu____4985 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu____4985 "\n" in
                                  Prims.op_Hat s uu____4984) "" ses'1 in
                         FStar_Util.print1 "Checked: %s\n" uu____4978
                       else ());
                      FStar_List.iter
                        (fun se1 ->
                           (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                             env3 se1) ses'1;
                      (let uu____4990 =
                         let uu____4999 =
                           FStar_Options.use_extracted_interfaces () in
                         if uu____4999
                         then ((FStar_List.rev_append ses'1 exports), [])
                         else
                           (let accum_exports_hidden uu____5038 se1 =
                              match uu____5038 with
                              | (exports1, hidden1) ->
                                  let uu____5066 =
                                    for_export env3 hidden1 se1 in
                                  (match uu____5066 with
                                   | (se_exported, hidden2) ->
                                       ((FStar_List.rev_append se_exported
                                           exports1), hidden2)) in
                            FStar_List.fold_left accum_exports_hidden
                              (exports, hidden) ses'1) in
                       match uu____4990 with
                       | (exports1, hidden1) ->
                           (((FStar_List.rev_append ses'1 ses1), exports1,
                              env3, hidden1), ses_elaborated1)))))) in
      let process_one_decl_timed acc se =
        let uu____5220 = acc in
        match uu____5220 with
        | (uu____5255, uu____5256, env1, uu____5258) ->
            let r =
              let uu____5292 =
                let uu____5295 =
                  let uu____5296 = FStar_TypeChecker_Env.current_module env1 in
                  FStar_Ident.string_of_lid uu____5296 in
                FStar_Pervasives_Native.Some uu____5295 in
              FStar_Profiling.profile
                (fun uu____5318 -> process_one_decl acc se) uu____5292
                "FStar.TypeChecker.Tc.process_one_decl" in
            ((let uu____5320 = FStar_Options.profile_group_by_decls () in
              if uu____5320
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____5323 -> FStar_Ident.string_of_lid hd
                  | uu____5326 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se) in
                FStar_Profiling.report_and_clear tag
              else ());
             r) in
      let uu____5330 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____5360 ->
             FStar_Util.fold_flatten process_one_decl_timed ([], [], env, [])
               ses) in
      match uu____5330 with
      | (ses1, exports, env1, uu____5394) ->
          ((FStar_List.rev_append ses1 []),
            (FStar_List.rev_append exports []), env1)
let (uu___1083 : unit) =
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
          let uu___1087_5495 = env in
          {
            FStar_TypeChecker_Env.solver =
              (uu___1087_5495.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___1087_5495.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___1087_5495.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___1087_5495.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___1087_5495.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___1087_5495.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___1087_5495.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___1087_5495.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___1087_5495.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___1087_5495.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___1087_5495.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___1087_5495.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___1087_5495.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___1087_5495.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___1087_5495.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___1087_5495.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___1087_5495.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___1087_5495.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___1087_5495.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.phase1 =
              (uu___1087_5495.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___1087_5495.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___1087_5495.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___1087_5495.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___1087_5495.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___1087_5495.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___1087_5495.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___1087_5495.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___1087_5495.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (uu___1087_5495.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___1087_5495.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___1087_5495.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___1087_5495.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___1087_5495.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1087_5495.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___1087_5495.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___1087_5495.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___1087_5495.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___1087_5495.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___1087_5495.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___1087_5495.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___1087_5495.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___1087_5495.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___1087_5495.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___1087_5495.FStar_TypeChecker_Env.enable_defer_to_tac)
          } in
        let check_term lid univs t =
          let uu____5512 = FStar_Syntax_Subst.open_univ_vars univs t in
          match uu____5512 with
          | (univs1, t1) ->
              ((let uu____5520 =
                  let uu____5521 =
                    let uu____5526 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name in
                    FStar_TypeChecker_Env.debug uu____5526 in
                  FStar_All.pipe_left uu____5521
                    (FStar_Options.Other "Exports") in
                if uu____5520
                then
                  let uu____5527 = FStar_Syntax_Print.lid_to_string lid in
                  let uu____5528 =
                    let uu____5529 =
                      FStar_All.pipe_right univs1
                        (FStar_List.map
                           (fun x ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x))) in
                    FStar_All.pipe_right uu____5529
                      (FStar_String.concat ", ") in
                  let uu____5540 = FStar_Syntax_Print.term_to_string t1 in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____5527 uu____5528 uu____5540
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs1 in
                let uu____5543 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1 in
                FStar_All.pipe_right uu____5543 (fun uu____5552 -> ()))) in
        let check_term1 lid univs t =
          (let uu____5570 =
             let uu____5571 =
               FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
             let uu____5572 = FStar_Ident.string_of_lid lid in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____5571 uu____5572 in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____5570);
          check_term lid univs t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix () in
        let rec check_sigelt se =
          match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_bundle (ses, uu____5581) ->
              let uu____5590 =
                let uu____5591 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5591 in
              if uu____5590
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l, univs, binders, typ, uu____5601, uu____5602) ->
              let t =
                let uu____5614 =
                  let uu____5615 =
                    let uu____5630 = FStar_Syntax_Syntax.mk_Total typ in
                    (binders, uu____5630) in
                  FStar_Syntax_Syntax.Tm_arrow uu____5615 in
                FStar_Syntax_Syntax.mk uu____5614
                  se.FStar_Syntax_Syntax.sigrng in
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_datacon
              (l, univs, t, uu____5646, uu____5647, uu____5648) ->
              check_term1 l univs t
          | FStar_Syntax_Syntax.Sig_declare_typ (l, univs, t) ->
              let uu____5656 =
                let uu____5657 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5657 in
              if uu____5656 then check_term1 l univs t else ()
          | FStar_Syntax_Syntax.Sig_let ((uu____5661, lbs), uu____5663) ->
              let uu____5672 =
                let uu____5673 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5673 in
              if uu____5672
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
              let uu____5692 =
                let uu____5693 =
                  FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                    (FStar_List.contains FStar_Syntax_Syntax.Private) in
                Prims.op_Negation uu____5693 in
              if uu____5692
              then
                let arrow =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (binders, comp))
                    se.FStar_Syntax_Syntax.sigrng in
                check_term1 l univs arrow
              else ()
          | FStar_Syntax_Syntax.Sig_assume uu____5710 -> ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____5717 -> ()
          | FStar_Syntax_Syntax.Sig_sub_effect uu____5718 -> ()
          | FStar_Syntax_Syntax.Sig_pragma uu____5719 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5720 -> ()
          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5731 -> ()
          | FStar_Syntax_Syntax.Sig_fail uu____5740 ->
              failwith "Impossible (Already handled)"
          | FStar_Syntax_Syntax.Sig_splice uu____5751 ->
              failwith "Impossible (Already handled)" in
        let uu____5758 =
          FStar_Ident.lid_equals modul.FStar_Syntax_Syntax.name
            FStar_Parser_Const.prims_lid in
        if uu____5758 then () else FStar_List.iter check_sigelt exports
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
             | FStar_Syntax_Syntax.Projector (l, uu____5853) -> true
             | uu____5854 -> false) quals in
      let vals_of_abstract_inductive s =
        let mk_typ_for_abstract_inductive bs t r =
          match bs with
          | [] -> t
          | uu____5883 ->
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow (bs', c) ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow
                        ((FStar_List.append bs bs'), c)) r
               | uu____5922 ->
                   let uu____5923 =
                     let uu____5924 =
                       let uu____5939 = FStar_Syntax_Syntax.mk_Total t in
                       (bs, uu____5939) in
                     FStar_Syntax_Syntax.Tm_arrow uu____5924 in
                   FStar_Syntax_Syntax.mk uu____5923 r) in
        match s.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_inductive_typ
            (lid, uvs, bs, t, uu____5956, uu____5957) ->
            let s1 =
              let uu___1215_5967 = s in
              let uu____5968 =
                let uu____5969 =
                  let uu____5976 =
                    mk_typ_for_abstract_inductive bs t
                      s.FStar_Syntax_Syntax.sigrng in
                  (lid, uvs, uu____5976) in
                FStar_Syntax_Syntax.Sig_declare_typ uu____5969 in
              let uu____5977 =
                let uu____5980 =
                  let uu____5983 =
                    filter_out_abstract_and_noeq
                      s.FStar_Syntax_Syntax.sigquals in
                  FStar_Syntax_Syntax.New :: uu____5983 in
                FStar_Syntax_Syntax.Assumption :: uu____5980 in
              {
                FStar_Syntax_Syntax.sigel = uu____5968;
                FStar_Syntax_Syntax.sigrng =
                  (uu___1215_5967.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals = uu____5977;
                FStar_Syntax_Syntax.sigmeta =
                  (uu___1215_5967.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs =
                  (uu___1215_5967.FStar_Syntax_Syntax.sigattrs);
                FStar_Syntax_Syntax.sigopts =
                  (uu___1215_5967.FStar_Syntax_Syntax.sigopts)
              } in
            [s1]
        | uu____5986 -> failwith "Impossible!" in
      let val_of_lb s lid uu____6010 lbdef =
        match uu____6010 with
        | (uvs, t) ->
            let attrs =
              let uu____6021 =
                FStar_TypeChecker_Util.must_erase_for_extraction en lbdef in
              if uu____6021
              then
                let uu____6024 =
                  let uu____6025 =
                    FStar_Syntax_Syntax.lid_as_fv
                      FStar_Parser_Const.must_erase_for_extraction_attr
                      FStar_Syntax_Syntax.delta_constant
                      FStar_Pervasives_Native.None in
                  FStar_All.pipe_right uu____6025
                    FStar_Syntax_Syntax.fv_to_tm in
                uu____6024 :: (s.FStar_Syntax_Syntax.sigattrs)
              else s.FStar_Syntax_Syntax.sigattrs in
            let uu___1228_6027 = s in
            let uu____6028 =
              let uu____6031 =
                filter_out_abstract_and_inline s.FStar_Syntax_Syntax.sigquals in
              FStar_Syntax_Syntax.Assumption :: uu____6031 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t));
              FStar_Syntax_Syntax.sigrng =
                (uu___1228_6027.FStar_Syntax_Syntax.sigrng);
              FStar_Syntax_Syntax.sigquals = uu____6028;
              FStar_Syntax_Syntax.sigmeta =
                (uu___1228_6027.FStar_Syntax_Syntax.sigmeta);
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts =
                (uu___1228_6027.FStar_Syntax_Syntax.sigopts)
            } in
      let should_keep_lbdef t =
        let comp_effect_name c =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
          | uu____6047 -> failwith "Impossible!" in
        let c_opt =
          let uu____6053 = FStar_Syntax_Util.is_unit t in
          if uu____6053
          then
            let uu____6058 = FStar_Syntax_Syntax.mk_Total t in
            FStar_Pervasives_Native.Some uu____6058
          else
            (let uu____6064 =
               let uu____6065 = FStar_Syntax_Subst.compress t in
               uu____6065.FStar_Syntax_Syntax.n in
             match uu____6064 with
             | FStar_Syntax_Syntax.Tm_arrow (uu____6072, c) ->
                 FStar_Pervasives_Native.Some c
             | uu____6096 -> FStar_Pervasives_Native.None) in
        match c_opt with
        | FStar_Pervasives_Native.None -> true
        | FStar_Pervasives_Native.Some c ->
            let uu____6106 = FStar_Syntax_Util.is_lemma_comp c in
            if uu____6106
            then false
            else
              (let uu____6108 = FStar_Syntax_Util.is_pure_or_ghost_comp c in
               if uu____6108
               then true
               else
                 (let uu____6110 = comp_effect_name c in
                  FStar_TypeChecker_Env.is_reifiable_effect en uu____6110)) in
      let extract_sigelt s =
        (let uu____6122 =
           FStar_TypeChecker_Env.debug en FStar_Options.Extreme in
         if uu____6122
         then
           let uu____6123 = FStar_Syntax_Print.sigelt_to_string s in
           FStar_Util.print1 "Extracting interface for %s\n" uu____6123
         else ());
        (match s.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____6127 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_datacon uu____6146 ->
             failwith "Impossible! extract_interface: bare data constructor"
         | FStar_Syntax_Syntax.Sig_splice uu____6163 ->
             failwith
               "Impossible! extract_interface: trying to extract splice"
         | FStar_Syntax_Syntax.Sig_fail uu____6172 ->
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
                             (lid, uu____6220, uu____6221, uu____6222,
                              uu____6223, uu____6224)
                             ->
                             ((let uu____6234 =
                                 let uu____6237 =
                                   FStar_ST.op_Bang abstract_inductive_tycons in
                                 lid :: uu____6237 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_tycons uu____6234);
                              (let uu____6260 = vals_of_abstract_inductive s1 in
                               FStar_List.append uu____6260 sigelts1))
                         | FStar_Syntax_Syntax.Sig_datacon
                             (lid, uu____6264, uu____6265, uu____6266,
                              uu____6267, uu____6268)
                             ->
                             ((let uu____6274 =
                                 let uu____6277 =
                                   FStar_ST.op_Bang
                                     abstract_inductive_datacons in
                                 lid :: uu____6277 in
                               FStar_ST.op_Colon_Equals
                                 abstract_inductive_datacons uu____6274);
                              sigelts1)
                         | uu____6300 ->
                             failwith
                               "Impossible! extract_interface: Sig_bundle can't have anything other than Sig_inductive_typ and Sig_datacon")
                    [])
             else [s]
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
             let uu____6307 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____6307
             then []
             else
               if is_assume s.FStar_Syntax_Syntax.sigquals
               then
                 (let uu____6313 =
                    let uu___1294_6314 = s in
                    let uu____6315 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1294_6314.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1294_6314.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____6315;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1294_6314.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1294_6314.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1294_6314.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____6313])
               else []
         | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
             let uu____6325 =
               is_projector_or_discriminator_of_an_abstract_inductive
                 s.FStar_Syntax_Syntax.sigquals in
             if uu____6325
             then []
             else
               (let uu____6329 = lbs in
                match uu____6329 with
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
                        (fun uu____6388 ->
                           match uu____6388 with
                           | (uu____6395, t, uu____6397) ->
                               FStar_All.pipe_right t
                                 FStar_Syntax_Util.is_lemma) typs_and_defs in
                    let vals =
                      FStar_List.map2
                        (fun lid ->
                           fun uu____6413 ->
                             match uu____6413 with
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
                           (fun uu____6437 ->
                              match uu____6437 with
                              | (uu____6444, t, uu____6446) ->
                                  FStar_All.pipe_right t should_keep_lbdef)
                           typs_and_defs in
                       if should_keep_defs then [s] else vals))
         | FStar_Syntax_Syntax.Sig_assume (lid, uu____6451, uu____6452) ->
             let is_haseq = FStar_TypeChecker_TcInductive.is_haseq_lid lid in
             if is_haseq
             then
               let is_haseq_of_abstract_inductive =
                 let uu____6457 = FStar_ST.op_Bang abstract_inductive_tycons in
                 FStar_List.existsML
                   (fun l ->
                      let uu____6473 =
                        FStar_TypeChecker_TcInductive.get_haseq_axiom_lid l in
                      FStar_Ident.lid_equals lid uu____6473) uu____6457 in
               (if is_haseq_of_abstract_inductive
                then
                  let uu____6476 =
                    let uu___1334_6477 = s in
                    let uu____6478 =
                      filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (uu___1334_6477.FStar_Syntax_Syntax.sigel);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___1334_6477.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals = uu____6478;
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___1334_6477.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___1334_6477.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___1334_6477.FStar_Syntax_Syntax.sigopts)
                    } in
                  [uu____6476]
                else [])
             else
               (let uu____6483 =
                  let uu___1336_6484 = s in
                  let uu____6485 =
                    filter_out_abstract s.FStar_Syntax_Syntax.sigquals in
                  {
                    FStar_Syntax_Syntax.sigel =
                      (uu___1336_6484.FStar_Syntax_Syntax.sigel);
                    FStar_Syntax_Syntax.sigrng =
                      (uu___1336_6484.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals = uu____6485;
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___1336_6484.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___1336_6484.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___1336_6484.FStar_Syntax_Syntax.sigopts)
                  } in
                [uu____6483])
         | FStar_Syntax_Syntax.Sig_new_effect uu____6488 -> [s]
         | FStar_Syntax_Syntax.Sig_sub_effect uu____6489 -> [s]
         | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6490 -> [s]
         | FStar_Syntax_Syntax.Sig_pragma uu____6503 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6504 -> [s]
         | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____6515 -> [s]) in
      let uu___1350_6524 = m in
      let uu____6525 =
        let uu____6526 =
          FStar_All.pipe_right m.FStar_Syntax_Syntax.declarations
            (FStar_List.map extract_sigelt) in
        FStar_All.pipe_right uu____6526 FStar_List.flatten in
      {
        FStar_Syntax_Syntax.name = (uu___1350_6524.FStar_Syntax_Syntax.name);
        FStar_Syntax_Syntax.declarations = uu____6525;
        FStar_Syntax_Syntax.exports =
          (uu___1350_6524.FStar_Syntax_Syntax.exports);
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
        (fun uu____6570 -> FStar_TypeChecker_Env.snapshot env msg)
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
          (fun uu____6608 ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu____6620 = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu____6620
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
        let uu____6678 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
        FStar_Options.should_verify uu____6678 in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____6684 = FStar_Options.debug_any () in
       if uu____6684
       then
         let uu____6685 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.print3 "%s %s of %s\n" action label uu____6685
       else ());
      (let name =
         let uu____6688 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____6688 in
       let env1 =
         let uu___1375_6691 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___1375_6691.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___1375_6691.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___1375_6691.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___1375_6691.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___1375_6691.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___1375_6691.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___1375_6691.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___1375_6691.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___1375_6691.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___1375_6691.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___1375_6691.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___1375_6691.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___1375_6691.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___1375_6691.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___1375_6691.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___1375_6691.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___1375_6691.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___1375_6691.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___1375_6691.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___1375_6691.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___1375_6691.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___1375_6691.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___1375_6691.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___1375_6691.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___1375_6691.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___1375_6691.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___1375_6691.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___1375_6691.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___1375_6691.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___1375_6691.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___1375_6691.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___1375_6691.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___1375_6691.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___1375_6691.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___1375_6691.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___1375_6691.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___1375_6691.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___1375_6691.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___1375_6691.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___1375_6691.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___1375_6691.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___1375_6691.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___1375_6691.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___1375_6691.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___1375_6691.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____6693 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____6693 with
       | (ses, exports, env3) ->
           ((let uu___1383_6726 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___1383_6726.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.exports =
                 (uu___1383_6726.FStar_Syntax_Syntax.exports);
               FStar_Syntax_Syntax.is_interface =
                 (uu___1383_6726.FStar_Syntax_Syntax.is_interface)
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
        let uu____6754 = tc_decls env decls in
        match uu____6754 with
        | (ses, exports, env1) ->
            let modul1 =
              let uu___1392_6785 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1392_6785.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___1392_6785.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1392_6785.FStar_Syntax_Syntax.is_interface)
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
          let uu____6838 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____6838 in
        let env01 = push_context env0 msg in
        let uu____6840 = tc_partial_modul env01 m in
        match uu____6840 with
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
                (let uu____6873 = FStar_Errors.get_err_count () in
                 uu____6873 = Prims.int_zero) in
            if should_extract_interface
            then
              let modul_iface = extract_interface en m in
              ((let uu____6880 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug en)
                    FStar_Options.Low in
                if uu____6880
                then
                  let uu____6881 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  let uu____6882 =
                    let uu____6883 =
                      let uu____6884 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.should_verify uu____6884 in
                    if uu____6883 then "" else " (in lax mode) " in
                  let uu____6886 =
                    let uu____6887 =
                      let uu____6888 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____6888 in
                    if uu____6887
                    then
                      let uu____6889 =
                        let uu____6890 = FStar_Syntax_Print.modul_to_string m in
                        Prims.op_Hat uu____6890 "\n" in
                      Prims.op_Hat "\nfrom: " uu____6889
                    else "" in
                  let uu____6892 =
                    let uu____6893 =
                      let uu____6894 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      FStar_Options.dump_module uu____6894 in
                    if uu____6893
                    then
                      let uu____6895 =
                        let uu____6896 =
                          FStar_Syntax_Print.modul_to_string modul_iface in
                        Prims.op_Hat uu____6896 "\n" in
                      Prims.op_Hat "\nto: " uu____6895
                    else "" in
                  FStar_Util.print4
                    "Extracting and type checking module %s interface%s%s%s\n"
                    uu____6881 uu____6882 uu____6886 uu____6892
                else ());
               (let en0 =
                  let en0 =
                    let uu____6901 =
                      let uu____6902 =
                        FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                      Prims.op_Hat "Ending modul " uu____6902 in
                    pop_context en uu____6901 in
                  let en01 =
                    let uu___1418_6904 = en0 in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1418_6904.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1418_6904.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1418_6904.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1418_6904.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1418_6904.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1418_6904.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1418_6904.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1418_6904.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1418_6904.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1418_6904.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1418_6904.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1418_6904.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1418_6904.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1418_6904.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1418_6904.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1418_6904.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1418_6904.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1418_6904.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1418_6904.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1418_6904.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1418_6904.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1418_6904.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1418_6904.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1418_6904.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1418_6904.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1418_6904.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1418_6904.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1418_6904.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1418_6904.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1418_6904.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1418_6904.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___1418_6904.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1418_6904.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1418_6904.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1418_6904.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1418_6904.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1418_6904.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1418_6904.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1418_6904.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1418_6904.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1418_6904.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1418_6904.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (en.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1418_6904.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1418_6904.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1418_6904.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1418_6904.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let en02 =
                    let uu___1421_6906 = en01 in
                    let uu____6907 =
                      let uu____6920 =
                        FStar_All.pipe_right
                          en.FStar_TypeChecker_Env.qtbl_name_and_index
                          FStar_Pervasives_Native.fst in
                      (uu____6920, FStar_Pervasives_Native.None) in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___1421_6906.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___1421_6906.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___1421_6906.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___1421_6906.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___1421_6906.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___1421_6906.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___1421_6906.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___1421_6906.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___1421_6906.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___1421_6906.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___1421_6906.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___1421_6906.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___1421_6906.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___1421_6906.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___1421_6906.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___1421_6906.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___1421_6906.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___1421_6906.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___1421_6906.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___1421_6906.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___1421_6906.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___1421_6906.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___1421_6906.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___1421_6906.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___1421_6906.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___1421_6906.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___1421_6906.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___1421_6906.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___1421_6906.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___1421_6906.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___1421_6906.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index = uu____6907;
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___1421_6906.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___1421_6906.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___1421_6906.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___1421_6906.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___1421_6906.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___1421_6906.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___1421_6906.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___1421_6906.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___1421_6906.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___1421_6906.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___1421_6906.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___1421_6906.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___1421_6906.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___1421_6906.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac =
                        (uu___1421_6906.FStar_TypeChecker_Env.enable_defer_to_tac)
                    } in
                  let uu____6957 =
                    let uu____6958 = FStar_Options.interactive () in
                    Prims.op_Negation uu____6958 in
                  if uu____6957
                  then
                    ((let uu____6960 =
                        FStar_Options.restore_cmd_line_options true in
                      FStar_All.pipe_right uu____6960 (fun uu____6961 -> ()));
                     en02)
                  else en02 in
                let uu____6963 = tc_modul en0 modul_iface true in
                match uu____6963 with
                | (modul_iface1, env) ->
                    ((let uu___1430_6975 = m in
                      {
                        FStar_Syntax_Syntax.name =
                          (uu___1430_6975.FStar_Syntax_Syntax.name);
                        FStar_Syntax_Syntax.declarations =
                          (uu___1430_6975.FStar_Syntax_Syntax.declarations);
                        FStar_Syntax_Syntax.exports =
                          (modul_iface1.FStar_Syntax_Syntax.exports);
                        FStar_Syntax_Syntax.is_interface =
                          (uu___1430_6975.FStar_Syntax_Syntax.is_interface)
                      }), env)))
            else
              (let modul =
                 let uu___1432_6978 = m in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___1432_6978.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations =
                     (uu___1432_6978.FStar_Syntax_Syntax.declarations);
                   FStar_Syntax_Syntax.exports = exports;
                   FStar_Syntax_Syntax.is_interface =
                     (uu___1432_6978.FStar_Syntax_Syntax.is_interface)
                 } in
               let env = FStar_TypeChecker_Env.finish_module en modul in
               (let uu____6981 =
                  FStar_All.pipe_right
                    env.FStar_TypeChecker_Env.qtbl_name_and_index
                    FStar_Pervasives_Native.fst in
                FStar_All.pipe_right uu____6981 FStar_Util.smap_clear);
               (let uu____7009 =
                  ((let uu____7012 = FStar_Options.lax () in
                    Prims.op_Negation uu____7012) &&
                     (Prims.op_Negation loading_from_cache))
                    &&
                    (let uu____7014 =
                       FStar_Options.use_extracted_interfaces () in
                     Prims.op_Negation uu____7014) in
                if uu____7009
                then
                  FStar_Syntax_Unionfind.with_uf_enabled
                    (fun uu____7016 -> check_exports env modul exports)
                else ());
               (let uu____7019 =
                  let uu____7020 =
                    let uu____7021 =
                      FStar_Ident.string_of_lid
                        modul.FStar_Syntax_Syntax.name in
                    Prims.op_Hat "Ending modul " uu____7021 in
                  pop_context env uu____7020 in
                FStar_All.pipe_right uu____7019 (fun uu____7022 -> ()));
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
        let uu____7035 =
          let uu____7036 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____7036 in
        push_context env uu____7035 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = add_sigelt_to_env env2 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____7055 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____7058 =
        finish_partial_modul true true env2 m m.FStar_Syntax_Syntax.exports in
      match uu____7058 with | (uu____7063, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu____7085 = FStar_Options.debug_any () in
         if uu____7085
         then
           let uu____7086 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____7086
         else ());
        (let uu____7090 =
           let uu____7091 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.dump_module uu____7091 in
         if uu____7090
         then
           let uu____7092 = FStar_Syntax_Print.modul_to_string m in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____7092
         else ());
        (let env1 =
           let uu___1463_7095 = env in
           let uu____7096 =
             let uu____7097 =
               let uu____7098 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu____7098 in
             Prims.op_Negation uu____7097 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1463_7095.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1463_7095.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1463_7095.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1463_7095.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1463_7095.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1463_7095.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1463_7095.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1463_7095.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1463_7095.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1463_7095.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1463_7095.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1463_7095.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1463_7095.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1463_7095.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1463_7095.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1463_7095.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1463_7095.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1463_7095.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1463_7095.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1463_7095.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____7096;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1463_7095.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1463_7095.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1463_7095.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1463_7095.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1463_7095.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1463_7095.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1463_7095.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1463_7095.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1463_7095.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1463_7095.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1463_7095.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1463_7095.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1463_7095.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1463_7095.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1463_7095.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1463_7095.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1463_7095.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1463_7095.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1463_7095.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1463_7095.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1463_7095.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1463_7095.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1463_7095.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1463_7095.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1463_7095.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___1463_7095.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         let uu____7099 = tc_modul env1 m b in
         match uu____7099 with
         | (m1, env2) ->
             ((let uu____7111 =
                 let uu____7112 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                 FStar_Options.dump_module uu____7112 in
               if uu____7111
               then
                 let uu____7113 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____7113
               else ());
              (let uu____7116 =
                 (let uu____7119 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                  FStar_Options.dump_module uu____7119) &&
                   (let uu____7121 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                    FStar_Options.debug_at_level uu____7121
                      (FStar_Options.Other "Normalize")) in
               if uu____7116
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
                         let uu____7154 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____7154 with
                         | (univnames, e) ->
                             let uu___1485_7161 = lb in
                             let uu____7162 =
                               let uu____7165 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu____7165 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____7162;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1485_7161.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___1487_7166 = se in
                       let uu____7167 =
                         let uu____7168 =
                           let uu____7175 =
                             let uu____7176 = FStar_List.map update lbs in
                             (b1, uu____7176) in
                           (uu____7175, ids) in
                         FStar_Syntax_Syntax.Sig_let uu____7168 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____7167;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1487_7166.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1487_7166.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1487_7166.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1487_7166.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1487_7166.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____7183 -> se in
                 let normalized_module =
                   let uu___1491_7185 = m1 in
                   let uu____7186 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1491_7185.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____7186;
                     FStar_Syntax_Syntax.exports =
                       (uu___1491_7185.FStar_Syntax_Syntax.exports);
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1491_7185.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____7187 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____7187
               else ());
              (m1, env2)))