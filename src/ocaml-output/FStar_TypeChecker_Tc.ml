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
          let uu___13_54 = env in
          let uu____55 =
            let uu____68 =
              let uu____75 = let uu____80 = get_n lid in (lid, uu____80) in
              FStar_Pervasives_Native.Some uu____75 in
            (tbl, uu____68) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___13_54.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___13_54.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___13_54.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___13_54.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___13_54.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___13_54.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___13_54.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___13_54.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___13_54.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___13_54.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___13_54.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___13_54.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___13_54.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___13_54.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___13_54.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___13_54.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___13_54.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___13_54.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___13_54.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___13_54.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___13_54.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___13_54.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___13_54.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___13_54.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___13_54.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___13_54.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___13_54.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___13_54.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___13_54.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___13_54.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___13_54.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____55;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___13_54.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___13_54.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___13_54.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___13_54.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___13_54.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___13_54.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___13_54.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___13_54.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___13_54.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___13_54.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___13_54.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___13_54.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___13_54.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___13_54.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___13_54.FStar_TypeChecker_Env.enable_defer_to_tac)
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
          let uu___22_104 = env in
          let uu____105 =
            let uu____118 =
              let uu____125 = let uu____130 = get_n lid in (lid, uu____130) in
              FStar_Pervasives_Native.Some uu____125 in
            (tbl, uu____118) in
          {
            FStar_TypeChecker_Env.solver =
              (uu___22_104.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___22_104.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___22_104.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___22_104.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (uu___22_104.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___22_104.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___22_104.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___22_104.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___22_104.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (uu___22_104.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___22_104.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___22_104.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___22_104.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___22_104.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (uu___22_104.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (uu___22_104.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___22_104.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.use_eq_strict =
              (uu___22_104.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (uu___22_104.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___22_104.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax =
              (uu___22_104.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (uu___22_104.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 =
              (uu___22_104.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (uu___22_104.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (uu___22_104.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (uu___22_104.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (uu___22_104.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.type_of =
              (uu___22_104.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___22_104.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.check_type_of =
              (uu___22_104.FStar_TypeChecker_Env.check_type_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___22_104.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qtbl_name_and_index = uu____105;
            FStar_TypeChecker_Env.normalized_eff_names =
              (uu___22_104.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (uu___22_104.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (uu___22_104.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (uu___22_104.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (uu___22_104.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice =
              (uu___22_104.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (uu___22_104.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (uu___22_104.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (uu___22_104.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (uu___22_104.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv =
              (uu___22_104.FStar_TypeChecker_Env.dsenv);
            FStar_TypeChecker_Env.nbe =
              (uu___22_104.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (uu___22_104.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (uu___22_104.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (uu___22_104.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                       FStar_TypeChecker_Generalize.generalize_universes env1
                         t2 in
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
              (fun uu___201_846 ->
                 match () with
                 | () ->
                     let uu____853 = tc_inductive' env1 ses quals attrs lids in
                     FStar_All.pipe_right uu____853 (fun r -> pop (); r)) ()
            with | uu___200_884 -> (pop (); FStar_Exn.raise uu___200_884)
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
        (fun uu____1200 ->
           let r = se.FStar_Syntax_Syntax.sigrng in
           let se1 =
             let uu____1203 = FStar_Options.record_options () in
             if uu____1203
             then
               let uu___248_1204 = se in
               let uu____1205 =
                 let uu____1208 = FStar_Options.peek () in
                 FStar_Pervasives_Native.Some uu____1208 in
               {
                 FStar_Syntax_Syntax.sigel =
                   (uu___248_1204.FStar_Syntax_Syntax.sigel);
                 FStar_Syntax_Syntax.sigrng =
                   (uu___248_1204.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___248_1204.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___248_1204.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___248_1204.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts = uu____1205
               }
             else se in
           match se1.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ uu____1220 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_datacon uu____1247 ->
               failwith "Impossible bare data-constructor"
           | FStar_Syntax_Syntax.Sig_fail (uu____1272, false, uu____1273)
               when
               (let uu____1284 = FStar_TypeChecker_Env.should_verify env in
                Prims.op_Negation uu____1284) ||
                 (FStar_Options.admit_smt_queries ())
               -> ([], [], env)
           | FStar_Syntax_Syntax.Sig_fail (expected_errors, lax, ses) ->
               let env' =
                 if lax
                 then
                   let uu___266_1301 = env in
                   {
                     FStar_TypeChecker_Env.solver =
                       (uu___266_1301.FStar_TypeChecker_Env.solver);
                     FStar_TypeChecker_Env.range =
                       (uu___266_1301.FStar_TypeChecker_Env.range);
                     FStar_TypeChecker_Env.curmodule =
                       (uu___266_1301.FStar_TypeChecker_Env.curmodule);
                     FStar_TypeChecker_Env.gamma =
                       (uu___266_1301.FStar_TypeChecker_Env.gamma);
                     FStar_TypeChecker_Env.gamma_sig =
                       (uu___266_1301.FStar_TypeChecker_Env.gamma_sig);
                     FStar_TypeChecker_Env.gamma_cache =
                       (uu___266_1301.FStar_TypeChecker_Env.gamma_cache);
                     FStar_TypeChecker_Env.modules =
                       (uu___266_1301.FStar_TypeChecker_Env.modules);
                     FStar_TypeChecker_Env.expected_typ =
                       (uu___266_1301.FStar_TypeChecker_Env.expected_typ);
                     FStar_TypeChecker_Env.sigtab =
                       (uu___266_1301.FStar_TypeChecker_Env.sigtab);
                     FStar_TypeChecker_Env.attrtab =
                       (uu___266_1301.FStar_TypeChecker_Env.attrtab);
                     FStar_TypeChecker_Env.instantiate_imp =
                       (uu___266_1301.FStar_TypeChecker_Env.instantiate_imp);
                     FStar_TypeChecker_Env.effects =
                       (uu___266_1301.FStar_TypeChecker_Env.effects);
                     FStar_TypeChecker_Env.generalize =
                       (uu___266_1301.FStar_TypeChecker_Env.generalize);
                     FStar_TypeChecker_Env.letrecs =
                       (uu___266_1301.FStar_TypeChecker_Env.letrecs);
                     FStar_TypeChecker_Env.top_level =
                       (uu___266_1301.FStar_TypeChecker_Env.top_level);
                     FStar_TypeChecker_Env.check_uvars =
                       (uu___266_1301.FStar_TypeChecker_Env.check_uvars);
                     FStar_TypeChecker_Env.use_eq =
                       (uu___266_1301.FStar_TypeChecker_Env.use_eq);
                     FStar_TypeChecker_Env.use_eq_strict =
                       (uu___266_1301.FStar_TypeChecker_Env.use_eq_strict);
                     FStar_TypeChecker_Env.is_iface =
                       (uu___266_1301.FStar_TypeChecker_Env.is_iface);
                     FStar_TypeChecker_Env.admit =
                       (uu___266_1301.FStar_TypeChecker_Env.admit);
                     FStar_TypeChecker_Env.lax = true;
                     FStar_TypeChecker_Env.lax_universes =
                       (uu___266_1301.FStar_TypeChecker_Env.lax_universes);
                     FStar_TypeChecker_Env.phase1 =
                       (uu___266_1301.FStar_TypeChecker_Env.phase1);
                     FStar_TypeChecker_Env.failhard =
                       (uu___266_1301.FStar_TypeChecker_Env.failhard);
                     FStar_TypeChecker_Env.nosynth =
                       (uu___266_1301.FStar_TypeChecker_Env.nosynth);
                     FStar_TypeChecker_Env.uvar_subtyping =
                       (uu___266_1301.FStar_TypeChecker_Env.uvar_subtyping);
                     FStar_TypeChecker_Env.tc_term =
                       (uu___266_1301.FStar_TypeChecker_Env.tc_term);
                     FStar_TypeChecker_Env.type_of =
                       (uu___266_1301.FStar_TypeChecker_Env.type_of);
                     FStar_TypeChecker_Env.universe_of =
                       (uu___266_1301.FStar_TypeChecker_Env.universe_of);
                     FStar_TypeChecker_Env.check_type_of =
                       (uu___266_1301.FStar_TypeChecker_Env.check_type_of);
                     FStar_TypeChecker_Env.use_bv_sorts =
                       (uu___266_1301.FStar_TypeChecker_Env.use_bv_sorts);
                     FStar_TypeChecker_Env.qtbl_name_and_index =
                       (uu___266_1301.FStar_TypeChecker_Env.qtbl_name_and_index);
                     FStar_TypeChecker_Env.normalized_eff_names =
                       (uu___266_1301.FStar_TypeChecker_Env.normalized_eff_names);
                     FStar_TypeChecker_Env.fv_delta_depths =
                       (uu___266_1301.FStar_TypeChecker_Env.fv_delta_depths);
                     FStar_TypeChecker_Env.proof_ns =
                       (uu___266_1301.FStar_TypeChecker_Env.proof_ns);
                     FStar_TypeChecker_Env.synth_hook =
                       (uu___266_1301.FStar_TypeChecker_Env.synth_hook);
                     FStar_TypeChecker_Env.try_solve_implicits_hook =
                       (uu___266_1301.FStar_TypeChecker_Env.try_solve_implicits_hook);
                     FStar_TypeChecker_Env.splice =
                       (uu___266_1301.FStar_TypeChecker_Env.splice);
                     FStar_TypeChecker_Env.mpreprocess =
                       (uu___266_1301.FStar_TypeChecker_Env.mpreprocess);
                     FStar_TypeChecker_Env.postprocess =
                       (uu___266_1301.FStar_TypeChecker_Env.postprocess);
                     FStar_TypeChecker_Env.identifier_info =
                       (uu___266_1301.FStar_TypeChecker_Env.identifier_info);
                     FStar_TypeChecker_Env.tc_hooks =
                       (uu___266_1301.FStar_TypeChecker_Env.tc_hooks);
                     FStar_TypeChecker_Env.dsenv =
                       (uu___266_1301.FStar_TypeChecker_Env.dsenv);
                     FStar_TypeChecker_Env.nbe =
                       (uu___266_1301.FStar_TypeChecker_Env.nbe);
                     FStar_TypeChecker_Env.strict_args_tab =
                       (uu___266_1301.FStar_TypeChecker_Env.strict_args_tab);
                     FStar_TypeChecker_Env.erasable_types_tab =
                       (uu___266_1301.FStar_TypeChecker_Env.erasable_types_tab);
                     FStar_TypeChecker_Env.enable_defer_to_tac =
                       (uu___266_1301.FStar_TypeChecker_Env.enable_defer_to_tac)
                   }
                 else env in
               let env'1 = FStar_TypeChecker_Env.push env' "expect_failure" in
               ((let uu____1305 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Low in
                 if uu____1305
                 then
                   let uu____1306 =
                     let uu____1307 =
                       FStar_List.map FStar_Util.string_of_int
                         expected_errors in
                     FStar_All.pipe_left (FStar_String.concat "; ")
                       uu____1307 in
                   FStar_Util.print1 ">> Expecting errors: [%s]\n" uu____1306
                 else ());
                (let uu____1313 =
                   FStar_Errors.catch_errors
                     (fun uu____1335 ->
                        FStar_Options.with_saved_options
                          (fun uu____1344 ->
                             let uu____1345 =
                               let uu____1362 =
                                 FStar_ST.op_Bang tc_decls_knot in
                               FStar_Util.must uu____1362 in
                             uu____1345 env'1 ses)) in
                 match uu____1313 with
                 | (errs, uu____1442) ->
                     ((let uu____1464 =
                         (FStar_Options.print_expected_failures ()) ||
                           (FStar_TypeChecker_Env.debug env FStar_Options.Low) in
                       if uu____1464
                       then
                         (FStar_Util.print_string ">> Got issues: [\n";
                          FStar_List.iter FStar_Errors.print_issue errs;
                          FStar_Util.print_string ">>]\n")
                       else ());
                      (let uu____1468 =
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
                        | uu____1476 ->
                            if expected_errors <> []
                            then
                              let uu____1481 =
                                FStar_Errors.find_multiset_discrepancy
                                  expected_errors actual_errors in
                              (match uu____1481 with
                               | FStar_Pervasives_Native.None -> ()
                               | FStar_Pervasives_Native.Some (e, n1, n2) ->
                                   (FStar_List.iter FStar_Errors.print_issue
                                      errs;
                                    (let uu____1506 =
                                       let uu____1511 =
                                         let uu____1512 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             expected_errors in
                                         let uu____1513 =
                                           FStar_Common.string_of_list
                                             FStar_Util.string_of_int
                                             actual_errors in
                                         let uu____1514 =
                                           FStar_Util.string_of_int e in
                                         let uu____1515 =
                                           FStar_Util.string_of_int n2 in
                                         let uu____1516 =
                                           FStar_Util.string_of_int n1 in
                                         FStar_Util.format5
                                           "This top-level definition was expected to raise error codes %s, but it raised %s. Error #%s was raised %s times, instead of %s."
                                           uu____1512 uu____1513 uu____1514
                                           uu____1515 uu____1516 in
                                       (FStar_Errors.Error_DidNotFail,
                                         uu____1511) in
                                     FStar_Errors.log_issue
                                       se1.FStar_Syntax_Syntax.sigrng
                                       uu____1506)))
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
                 let uu____1554 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env1) in
                 if uu____1554
                 then
                   let ses1 =
                     let uu____1560 =
                       let uu____1561 =
                         let uu____1562 =
                           tc_inductive
                             (let uu___308_1571 = env1 in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___308_1571.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___308_1571.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___308_1571.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___308_1571.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___308_1571.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___308_1571.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___308_1571.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___308_1571.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___308_1571.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___308_1571.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___308_1571.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___308_1571.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___308_1571.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___308_1571.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___308_1571.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___308_1571.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___308_1571.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___308_1571.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___308_1571.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___308_1571.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___308_1571.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___308_1571.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___308_1571.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___308_1571.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___308_1571.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___308_1571.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___308_1571.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___308_1571.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___308_1571.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___308_1571.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___308_1571.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___308_1571.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___308_1571.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___308_1571.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___308_1571.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___308_1571.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___308_1571.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___308_1571.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___308_1571.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___308_1571.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___308_1571.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___308_1571.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___308_1571.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___308_1571.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___308_1571.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) ses se1.FStar_Syntax_Syntax.sigquals
                             se1.FStar_Syntax_Syntax.sigattrs lids in
                         FStar_All.pipe_right uu____1562
                           FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____1561
                         (FStar_TypeChecker_Normalize.elim_uvars env1) in
                     FStar_All.pipe_right uu____1560
                       FStar_Syntax_Util.ses_of_sigbundle in
                   ((let uu____1583 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "TwoPhases") in
                     if uu____1583
                     then
                       let uu____1584 =
                         FStar_Syntax_Print.sigelt_to_string
                           (let uu___312_1587 = se1 in
                            {
                              FStar_Syntax_Syntax.sigel =
                                (FStar_Syntax_Syntax.Sig_bundle (ses1, lids));
                              FStar_Syntax_Syntax.sigrng =
                                (uu___312_1587.FStar_Syntax_Syntax.sigrng);
                              FStar_Syntax_Syntax.sigquals =
                                (uu___312_1587.FStar_Syntax_Syntax.sigquals);
                              FStar_Syntax_Syntax.sigmeta =
                                (uu___312_1587.FStar_Syntax_Syntax.sigmeta);
                              FStar_Syntax_Syntax.sigattrs =
                                (uu___312_1587.FStar_Syntax_Syntax.sigattrs);
                              FStar_Syntax_Syntax.sigopts =
                                (uu___312_1587.FStar_Syntax_Syntax.sigopts)
                            }) in
                       FStar_Util.print1 "Inductive after phase 1: %s\n"
                         uu____1584
                     else ());
                    ses1)
                 else ses in
               let uu____1594 =
                 tc_inductive env1 ses1 se1.FStar_Syntax_Syntax.sigquals
                   se1.FStar_Syntax_Syntax.sigattrs lids in
               (match uu____1594 with
                | (sigbndle, projectors_ses) ->
                    let sigbndle1 =
                      let uu___319_1618 = sigbndle in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___319_1618.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___319_1618.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___319_1618.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___319_1618.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (se1.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___319_1618.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([sigbndle1], projectors_ses, env0))
           | FStar_Syntax_Syntax.Sig_pragma p ->
               (FStar_Syntax_Util.process_pragma p r; ([se1], [], env0))
           | FStar_Syntax_Syntax.Sig_new_effect ne ->
               let is_unelaborated_dm4f =
                 match ne.FStar_Syntax_Syntax.combinators with
                 | FStar_Syntax_Syntax.DM4F_eff combs ->
                     let uu____1632 =
                       let uu____1635 =
                         FStar_All.pipe_right
                           combs.FStar_Syntax_Syntax.ret_wp
                           FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____1635
                         FStar_Syntax_Subst.compress in
                     (match uu____1632 with
                      | {
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_unknown;
                          FStar_Syntax_Syntax.pos = uu____1650;
                          FStar_Syntax_Syntax.vars = uu____1651;_} -> true
                      | uu____1654 -> false)
                 | uu____1657 -> false in
               if is_unelaborated_dm4f
               then
                 let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____1669 =
                   FStar_TypeChecker_TcEffect.dmff_cps_and_elaborate env1 ne in
                 (match uu____1669 with
                  | (ses, ne1, lift_from_pure_opt) ->
                      let effect_and_lift_ses =
                        match lift_from_pure_opt with
                        | FStar_Pervasives_Native.Some lift ->
                            [(let uu___344_1708 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___344_1708.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___344_1708.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___344_1708.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___344_1708.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___344_1708.FStar_Syntax_Syntax.sigopts)
                              });
                            lift]
                        | FStar_Pervasives_Native.None ->
                            [(let uu___347_1710 = se1 in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                FStar_Syntax_Syntax.sigrng =
                                  (uu___347_1710.FStar_Syntax_Syntax.sigrng);
                                FStar_Syntax_Syntax.sigquals =
                                  (uu___347_1710.FStar_Syntax_Syntax.sigquals);
                                FStar_Syntax_Syntax.sigmeta =
                                  (uu___347_1710.FStar_Syntax_Syntax.sigmeta);
                                FStar_Syntax_Syntax.sigattrs =
                                  (uu___347_1710.FStar_Syntax_Syntax.sigattrs);
                                FStar_Syntax_Syntax.sigopts =
                                  (uu___347_1710.FStar_Syntax_Syntax.sigopts)
                              })] in
                      ([], (FStar_List.append ses effect_and_lift_ses), env0))
               else
                 (let ne1 =
                    let uu____1717 =
                      (FStar_Options.use_two_phase_tc ()) &&
                        (FStar_TypeChecker_Env.should_verify env) in
                    if uu____1717
                    then
                      let ne1 =
                        let uu____1719 =
                          let uu____1720 =
                            let uu____1721 =
                              FStar_TypeChecker_TcEffect.tc_eff_decl
                                (let uu___351_1724 = env in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___351_1724.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___351_1724.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___351_1724.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___351_1724.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___351_1724.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___351_1724.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___351_1724.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___351_1724.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___351_1724.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___351_1724.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___351_1724.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___351_1724.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___351_1724.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___351_1724.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___351_1724.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___351_1724.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___351_1724.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___351_1724.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___351_1724.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___351_1724.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___351_1724.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 = true;
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___351_1724.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___351_1724.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___351_1724.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___351_1724.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___351_1724.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___351_1724.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___351_1724.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___351_1724.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___351_1724.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___351_1724.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___351_1724.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___351_1724.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___351_1724.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___351_1724.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___351_1724.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___351_1724.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___351_1724.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___351_1724.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___351_1724.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___351_1724.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___351_1724.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___351_1724.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___351_1724.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___351_1724.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) ne se1.FStar_Syntax_Syntax.sigquals
                                se1.FStar_Syntax_Syntax.sigattrs in
                            FStar_All.pipe_right uu____1721
                              (fun ne1 ->
                                 let uu___354_1728 = se1 in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (uu___354_1728.FStar_Syntax_Syntax.sigrng);
                                   FStar_Syntax_Syntax.sigquals =
                                     (uu___354_1728.FStar_Syntax_Syntax.sigquals);
                                   FStar_Syntax_Syntax.sigmeta =
                                     (uu___354_1728.FStar_Syntax_Syntax.sigmeta);
                                   FStar_Syntax_Syntax.sigattrs =
                                     (uu___354_1728.FStar_Syntax_Syntax.sigattrs);
                                   FStar_Syntax_Syntax.sigopts =
                                     (uu___354_1728.FStar_Syntax_Syntax.sigopts)
                                 }) in
                          FStar_All.pipe_right uu____1720
                            (FStar_TypeChecker_Normalize.elim_uvars env) in
                        FStar_All.pipe_right uu____1719
                          FStar_Syntax_Util.eff_decl_of_new_effect in
                      ((let uu____1730 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "TwoPhases") in
                        if uu____1730
                        then
                          let uu____1731 =
                            FStar_Syntax_Print.sigelt_to_string
                              (let uu___358_1734 = se1 in
                               {
                                 FStar_Syntax_Syntax.sigel =
                                   (FStar_Syntax_Syntax.Sig_new_effect ne1);
                                 FStar_Syntax_Syntax.sigrng =
                                   (uu___358_1734.FStar_Syntax_Syntax.sigrng);
                                 FStar_Syntax_Syntax.sigquals =
                                   (uu___358_1734.FStar_Syntax_Syntax.sigquals);
                                 FStar_Syntax_Syntax.sigmeta =
                                   (uu___358_1734.FStar_Syntax_Syntax.sigmeta);
                                 FStar_Syntax_Syntax.sigattrs =
                                   (uu___358_1734.FStar_Syntax_Syntax.sigattrs);
                                 FStar_Syntax_Syntax.sigopts =
                                   (uu___358_1734.FStar_Syntax_Syntax.sigopts)
                               }) in
                          FStar_Util.print1 "Effect decl after phase 1: %s\n"
                            uu____1731
                        else ());
                       ne1)
                    else ne in
                  let ne2 =
                    FStar_TypeChecker_TcEffect.tc_eff_decl env ne1
                      se1.FStar_Syntax_Syntax.sigquals
                      se1.FStar_Syntax_Syntax.sigattrs in
                  let se2 =
                    let uu___363_1739 = se1 in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_new_effect ne2);
                      FStar_Syntax_Syntax.sigrng =
                        (uu___363_1739.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___363_1739.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___363_1739.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___363_1739.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___363_1739.FStar_Syntax_Syntax.sigopts)
                    } in
                  ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_sub_effect sub ->
               let sub1 = FStar_TypeChecker_TcEffect.tc_lift env sub r in
               let se2 =
                 let uu___369_1747 = se1 in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect sub1);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___369_1747.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___369_1747.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___369_1747.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___369_1747.FStar_Syntax_Syntax.sigattrs);
                   FStar_Syntax_Syntax.sigopts =
                     (uu___369_1747.FStar_Syntax_Syntax.sigopts)
                 } in
               ([se2], [], env)
           | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uvs, tps, c, flags)
               ->
               let uu____1761 =
                 let uu____1770 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____1770
                 then
                   let uu____1779 =
                     let uu____1780 =
                       let uu____1781 =
                         FStar_TypeChecker_TcEffect.tc_effect_abbrev
                           (let uu___380_1792 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___380_1792.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___380_1792.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___380_1792.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___380_1792.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___380_1792.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___380_1792.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___380_1792.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___380_1792.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___380_1792.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___380_1792.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___380_1792.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___380_1792.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___380_1792.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___380_1792.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___380_1792.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___380_1792.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___380_1792.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___380_1792.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___380_1792.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___380_1792.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___380_1792.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 = true;
                              FStar_TypeChecker_Env.failhard =
                                (uu___380_1792.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___380_1792.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___380_1792.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___380_1792.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___380_1792.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___380_1792.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___380_1792.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___380_1792.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___380_1792.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___380_1792.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___380_1792.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___380_1792.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___380_1792.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___380_1792.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___380_1792.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___380_1792.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___380_1792.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___380_1792.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___380_1792.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___380_1792.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___380_1792.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___380_1792.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___380_1792.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___380_1792.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) (lid, uvs, tps, c) r in
                       FStar_All.pipe_right uu____1781
                         (fun uu____1807 ->
                            match uu____1807 with
                            | (lid1, uvs1, tps1, c1) ->
                                let uu___387_1820 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_effect_abbrev
                                       (lid1, uvs1, tps1, c1, flags));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___387_1820.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___387_1820.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___387_1820.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___387_1820.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___387_1820.FStar_Syntax_Syntax.sigopts)
                                }) in
                     FStar_All.pipe_right uu____1780
                       (FStar_TypeChecker_Normalize.elim_uvars env) in
                   FStar_All.pipe_right uu____1779
                     (fun se2 ->
                        match se2.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_effect_abbrev
                            (lid1, uvs1, tps1, c1, uu____1850) ->
                            (lid1, uvs1, tps1, c1)
                        | uu____1855 ->
                            failwith
                              "Did not expect Sig_effect_abbrev to not be one after phase 1")
                 else (lid, uvs, tps, c) in
               (match uu____1761 with
                | (lid1, uvs1, tps1, c1) ->
                    let uu____1879 =
                      FStar_TypeChecker_TcEffect.tc_effect_abbrev env
                        (lid1, uvs1, tps1, c1) r in
                    (match uu____1879 with
                     | (lid2, uvs2, tps2, c2) ->
                         let se2 =
                           let uu___408_1903 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (lid2, uvs2, tps2, c2, flags));
                             FStar_Syntax_Syntax.sigrng =
                               (uu___408_1903.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___408_1903.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___408_1903.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___408_1903.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___408_1903.FStar_Syntax_Syntax.sigopts)
                           } in
                         ([se2], [], env0)))
           | FStar_Syntax_Syntax.Sig_declare_typ
               (uu____1910, uu____1911, uu____1912) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1916 ->
                       match uu___0_1916 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1917 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_let (uu____1922, uu____1923) when
               FStar_All.pipe_right se1.FStar_Syntax_Syntax.sigquals
                 (FStar_Util.for_some
                    (fun uu___0_1931 ->
                       match uu___0_1931 with
                       | FStar_Syntax_Syntax.OnlyName -> true
                       | uu____1932 -> false))
               -> ([], [], env0)
           | FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) ->
               let env1 = FStar_TypeChecker_Env.set_range env r in
               ((let uu____1942 = FStar_TypeChecker_Env.lid_exists env1 lid in
                 if uu____1942
                 then
                   let uu____1943 =
                     let uu____1948 =
                       let uu____1949 = FStar_Ident.string_of_lid lid in
                       FStar_Util.format1
                         "Top-level declaration %s for a name that is already used in this module; top-level declarations must be unique in their module"
                         uu____1949 in
                     (FStar_Errors.Fatal_AlreadyDefinedTopLevelDeclaration,
                       uu____1948) in
                   FStar_Errors.raise_error uu____1943 r
                 else ());
                (let uu____1951 =
                   let uu____1960 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____1960
                   then
                     let uu____1969 =
                       tc_declare_typ
                         (let uu___432_1972 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___432_1972.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___432_1972.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___432_1972.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___432_1972.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___432_1972.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___432_1972.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___432_1972.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___432_1972.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___432_1972.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___432_1972.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___432_1972.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___432_1972.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___432_1972.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___432_1972.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___432_1972.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___432_1972.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___432_1972.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___432_1972.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___432_1972.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___432_1972.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___432_1972.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___432_1972.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___432_1972.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___432_1972.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___432_1972.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___432_1972.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___432_1972.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___432_1972.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___432_1972.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___432_1972.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___432_1972.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___432_1972.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___432_1972.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___432_1972.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___432_1972.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___432_1972.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___432_1972.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___432_1972.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___432_1972.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___432_1972.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___432_1972.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___432_1972.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___432_1972.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___432_1972.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___432_1972.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____1969 with
                     | (uvs1, t1) ->
                         ((let uu____1996 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____1996
                           then
                             let uu____1997 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____1998 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Val declaration after phase 1: %s and uvs: %s\n"
                               uu____1997 uu____1998
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____1951 with
                 | (uvs1, t1) ->
                     let uu____2029 =
                       tc_declare_typ env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2029 with
                      | (uvs2, t2) ->
                          ([(let uu___445_2059 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_declare_typ
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___445_2059.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___445_2059.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___445_2059.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___445_2059.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___445_2059.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_assume (lid, uvs, t) ->
               ((let uu____2064 =
                   let uu____2069 =
                     let uu____2070 = FStar_Syntax_Print.lid_to_string lid in
                     FStar_Util.format1 "Admitting a top-level assumption %s"
                       uu____2070 in
                   (FStar_Errors.Warning_WarnOnUse, uu____2069) in
                 FStar_Errors.log_issue r uu____2064);
                (let env1 = FStar_TypeChecker_Env.set_range env r in
                 let uu____2072 =
                   let uu____2081 =
                     (FStar_Options.use_two_phase_tc ()) &&
                       (FStar_TypeChecker_Env.should_verify env1) in
                   if uu____2081
                   then
                     let uu____2090 =
                       tc_assume
                         (let uu___455_2093 = env1 in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___455_2093.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___455_2093.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___455_2093.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___455_2093.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___455_2093.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___455_2093.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___455_2093.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___455_2093.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___455_2093.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___455_2093.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___455_2093.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___455_2093.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___455_2093.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___455_2093.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___455_2093.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___455_2093.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___455_2093.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___455_2093.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___455_2093.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___455_2093.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___455_2093.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 = true;
                            FStar_TypeChecker_Env.failhard =
                              (uu___455_2093.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___455_2093.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___455_2093.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___455_2093.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___455_2093.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___455_2093.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___455_2093.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___455_2093.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___455_2093.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___455_2093.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___455_2093.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___455_2093.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___455_2093.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___455_2093.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___455_2093.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___455_2093.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___455_2093.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___455_2093.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___455_2093.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___455_2093.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___455_2093.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___455_2093.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___455_2093.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___455_2093.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }) (uvs, t) se1.FStar_Syntax_Syntax.sigrng in
                     match uu____2090 with
                     | (uvs1, t1) ->
                         ((let uu____2117 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "TwoPhases") in
                           if uu____2117
                           then
                             let uu____2118 =
                               FStar_Syntax_Print.term_to_string t1 in
                             let uu____2119 =
                               FStar_Syntax_Print.univ_names_to_string uvs1 in
                             FStar_Util.print2
                               "Assume after phase 1: %s and uvs: %s\n"
                               uu____2118 uu____2119
                           else ());
                          (uvs1, t1))
                   else (uvs, t) in
                 match uu____2072 with
                 | (uvs1, t1) ->
                     let uu____2150 =
                       tc_assume env1 (uvs1, t1)
                         se1.FStar_Syntax_Syntax.sigrng in
                     (match uu____2150 with
                      | (uvs2, t2) ->
                          ([(let uu___468_2180 = se1 in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (FStar_Syntax_Syntax.Sig_assume
                                    (lid, uvs2, t2));
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___468_2180.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___468_2180.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___468_2180.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs =
                                 (uu___468_2180.FStar_Syntax_Syntax.sigattrs);
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___468_2180.FStar_Syntax_Syntax.sigopts)
                             })], [], env0))))
           | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
               ((let uu____2188 = FStar_Options.debug_any () in
                 if uu____2188
                 then
                   let uu____2189 =
                     FStar_Ident.string_of_lid
                       env.FStar_TypeChecker_Env.curmodule in
                   let uu____2190 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.print2 "%s: Found splice of (%s)\n" uu____2189
                     uu____2190
                 else ());
                (let uu____2192 =
                   FStar_TypeChecker_TcTerm.tc_tactic
                     FStar_Syntax_Syntax.t_unit FStar_Syntax_Syntax.t_decls
                     env t in
                 match uu____2192 with
                 | (t1, uu____2210, g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let ses =
                         env.FStar_TypeChecker_Env.splice env
                           se1.FStar_Syntax_Syntax.sigrng t1 in
                       let lids' =
                         FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                           ses in
                       FStar_List.iter
                         (fun lid ->
                            let uu____2224 =
                              FStar_List.tryFind (FStar_Ident.lid_equals lid)
                                lids' in
                            match uu____2224 with
                            | FStar_Pervasives_Native.None when
                                Prims.op_Negation
                                  env.FStar_TypeChecker_Env.nosynth
                                ->
                                let uu____2227 =
                                  let uu____2232 =
                                    let uu____2233 =
                                      FStar_Ident.string_of_lid lid in
                                    let uu____2234 =
                                      let uu____2235 =
                                        FStar_List.map
                                          FStar_Ident.string_of_lid lids' in
                                      FStar_All.pipe_left
                                        (FStar_String.concat ", ") uu____2235 in
                                    FStar_Util.format2
                                      "Splice declared the name %s but it was not defined.\nThose defined were: %s"
                                      uu____2233 uu____2234 in
                                  (FStar_Errors.Fatal_SplicedUndef,
                                    uu____2232) in
                                FStar_Errors.raise_error uu____2227 r
                            | uu____2240 -> ()) lids;
                       (let dsenv =
                          FStar_List.fold_left
                            FStar_Syntax_DsEnv.push_sigelt_force
                            env.FStar_TypeChecker_Env.dsenv ses in
                        let env1 =
                          let uu___488_2245 = env in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___488_2245.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___488_2245.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___488_2245.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___488_2245.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___488_2245.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___488_2245.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___488_2245.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___488_2245.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___488_2245.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___488_2245.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___488_2245.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___488_2245.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___488_2245.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___488_2245.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___488_2245.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___488_2245.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___488_2245.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___488_2245.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___488_2245.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___488_2245.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___488_2245.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___488_2245.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___488_2245.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___488_2245.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___488_2245.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___488_2245.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___488_2245.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___488_2245.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___488_2245.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___488_2245.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___488_2245.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___488_2245.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___488_2245.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___488_2245.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___488_2245.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___488_2245.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___488_2245.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___488_2245.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___488_2245.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___488_2245.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___488_2245.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___488_2245.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv = dsenv;
                            FStar_TypeChecker_Env.nbe =
                              (uu___488_2245.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___488_2245.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___488_2245.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___488_2245.FStar_TypeChecker_Env.enable_defer_to_tac)
                          } in
                        (let uu____2247 =
                           FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                         if uu____2247
                         then
                           let uu____2248 =
                             let uu____2249 =
                               FStar_List.map
                                 FStar_Syntax_Print.sigelt_to_string ses in
                             FStar_All.pipe_left (FStar_String.concat "\n")
                               uu____2249 in
                           FStar_Util.print1
                             "Splice returned sigelts {\n%s\n}\n" uu____2248
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
                     let uu____2322 =
                       let uu____2323 =
                         let uu____2332 = drop_logic val_q in
                         let uu____2335 = drop_logic q' in
                         (uu____2332, uu____2335) in
                       match uu____2323 with
                       | (val_q1, q'1) ->
                           ((FStar_List.length val_q1) =
                              (FStar_List.length q'1))
                             &&
                             (FStar_List.forall2
                                FStar_Syntax_Util.qualifier_equal val_q1 q'1) in
                     if uu____2322
                     then FStar_Pervasives_Native.Some q'
                     else
                       (let uu____2359 =
                          let uu____2364 =
                            let uu____2365 =
                              FStar_Syntax_Print.lid_to_string l in
                            let uu____2366 =
                              FStar_Syntax_Print.quals_to_string val_q in
                            let uu____2367 =
                              FStar_Syntax_Print.quals_to_string q' in
                            FStar_Util.format3
                              "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                              uu____2365 uu____2366 uu____2367 in
                          (FStar_Errors.Fatal_InconsistentQualifierAnnotation,
                            uu____2364) in
                        FStar_Errors.raise_error uu____2359 r) in
               let rename_parameters lb =
                 let rename_in_typ def typ =
                   let typ1 = FStar_Syntax_Subst.compress typ in
                   let def_bs =
                     let uu____2401 =
                       let uu____2402 = FStar_Syntax_Subst.compress def in
                       uu____2402.FStar_Syntax_Syntax.n in
                     match uu____2401 with
                     | FStar_Syntax_Syntax.Tm_abs
                         (binders, uu____2414, uu____2415) -> binders
                     | uu____2440 -> [] in
                   match typ1 with
                   | {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_arrow
                         (val_bs, c);
                       FStar_Syntax_Syntax.pos = r1;
                       FStar_Syntax_Syntax.vars = uu____2452;_} ->
                       let has_auto_name bv =
                         let uu____2481 =
                           FStar_Ident.string_of_id
                             bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.starts_with uu____2481
                           FStar_Ident.reserved_prefix in
                       let rec rename_binders def_bs1 val_bs1 =
                         match (def_bs1, val_bs1) with
                         | ([], uu____2557) -> val_bs1
                         | (uu____2588, []) -> val_bs1
                         | ((body_bv, uu____2620)::bt, (val_bv, aqual)::vt)
                             ->
                             let uu____2677 =
                               let uu____2684 =
                                 let uu____2689 = has_auto_name body_bv in
                                 let uu____2690 = has_auto_name val_bv in
                                 (uu____2689, uu____2690) in
                               match uu____2684 with
                               | (true, uu____2697) -> (val_bv, aqual)
                               | (false, true) ->
                                   let uu____2700 =
                                     let uu___559_2701 = val_bv in
                                     let uu____2702 =
                                       let uu____2703 =
                                         let uu____2708 =
                                           FStar_Ident.string_of_id
                                             body_bv.FStar_Syntax_Syntax.ppname in
                                         let uu____2709 =
                                           FStar_Ident.range_of_id
                                             val_bv.FStar_Syntax_Syntax.ppname in
                                         (uu____2708, uu____2709) in
                                       FStar_Ident.mk_ident uu____2703 in
                                     {
                                       FStar_Syntax_Syntax.ppname =
                                         uu____2702;
                                       FStar_Syntax_Syntax.index =
                                         (uu___559_2701.FStar_Syntax_Syntax.index);
                                       FStar_Syntax_Syntax.sort =
                                         (uu___559_2701.FStar_Syntax_Syntax.sort)
                                     } in
                                   (uu____2700, aqual)
                               | (false, false) -> (val_bv, aqual) in
                             let uu____2714 = rename_binders bt vt in
                             uu____2677 :: uu____2714 in
                       let uu____2729 =
                         let uu____2730 =
                           let uu____2745 = rename_binders def_bs val_bs in
                           (uu____2745, c) in
                         FStar_Syntax_Syntax.Tm_arrow uu____2730 in
                       FStar_Syntax_Syntax.mk uu____2729 r1
                   | uu____2764 -> typ1 in
                 let uu___565_2765 = lb in
                 let uu____2766 =
                   rename_in_typ lb.FStar_Syntax_Syntax.lbdef
                     lb.FStar_Syntax_Syntax.lbtyp in
                 {
                   FStar_Syntax_Syntax.lbname =
                     (uu___565_2765.FStar_Syntax_Syntax.lbname);
                   FStar_Syntax_Syntax.lbunivs =
                     (uu___565_2765.FStar_Syntax_Syntax.lbunivs);
                   FStar_Syntax_Syntax.lbtyp = uu____2766;
                   FStar_Syntax_Syntax.lbeff =
                     (uu___565_2765.FStar_Syntax_Syntax.lbeff);
                   FStar_Syntax_Syntax.lbdef =
                     (uu___565_2765.FStar_Syntax_Syntax.lbdef);
                   FStar_Syntax_Syntax.lbattrs =
                     (uu___565_2765.FStar_Syntax_Syntax.lbattrs);
                   FStar_Syntax_Syntax.lbpos =
                     (uu___565_2765.FStar_Syntax_Syntax.lbpos)
                 } in
               let uu____2769 =
                 FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                   (FStar_List.fold_left
                      (fun uu____2820 ->
                         fun lb ->
                           match uu____2820 with
                           | (gen, lbs1, quals_opt) ->
                               let lbname =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname in
                               let uu____2862 =
                                 let uu____2873 =
                                   FStar_TypeChecker_Env.try_lookup_val_decl
                                     env1
                                     (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 match uu____2873 with
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
                                       | uu____2946 ->
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
                                      (let uu____2989 =
                                         FStar_Syntax_Syntax.mk_lb
                                           ((FStar_Util.Inr lbname), uvs,
                                             FStar_Parser_Const.effect_ALL_lid,
                                             tval, def, [],
                                             (lb.FStar_Syntax_Syntax.lbpos)) in
                                       (false, uu____2989, quals_opt1))) in
                               (match uu____2862 with
                                | (gen1, lb1, quals_opt1) ->
                                    (gen1, (lb1 :: lbs1), quals_opt1)))
                      (true, [],
                        (if se1.FStar_Syntax_Syntax.sigquals = []
                         then FStar_Pervasives_Native.None
                         else
                           FStar_Pervasives_Native.Some
                             (se1.FStar_Syntax_Syntax.sigquals)))) in
               (match uu____2769 with
                | (should_generalize, lbs', quals_opt) ->
                    let quals =
                      match quals_opt with
                      | FStar_Pervasives_Native.None ->
                          [FStar_Syntax_Syntax.Visible_default]
                      | FStar_Pervasives_Native.Some q ->
                          let uu____3081 =
                            FStar_All.pipe_right q
                              (FStar_Util.for_some
                                 (fun uu___1_3085 ->
                                    match uu___1_3085 with
                                    | FStar_Syntax_Syntax.Irreducible -> true
                                    | FStar_Syntax_Syntax.Visible_default ->
                                        true
                                    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                        -> true
                                    | uu____3086 -> false)) in
                          if uu____3081
                          then q
                          else FStar_Syntax_Syntax.Visible_default :: q in
                    let lbs'1 = FStar_List.rev lbs' in
                    let uu____3093 =
                      let uu____3102 =
                        FStar_Syntax_Util.extract_attr'
                          FStar_Parser_Const.preprocess_with
                          se1.FStar_Syntax_Syntax.sigattrs in
                      match uu____3102 with
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
                    (match uu____3093 with
                     | (attrs, pre_tau) ->
                         let se2 =
                           let uu___623_3205 = se1 in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (uu___623_3205.FStar_Syntax_Syntax.sigel);
                             FStar_Syntax_Syntax.sigrng =
                               (uu___623_3205.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___623_3205.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___623_3205.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs = attrs;
                             FStar_Syntax_Syntax.sigopts =
                               (uu___623_3205.FStar_Syntax_Syntax.sigopts)
                           } in
                         let preprocess_lb tau lb =
                           let lbdef =
                             FStar_TypeChecker_Env.preprocess env1 tau
                               lb.FStar_Syntax_Syntax.lbdef in
                           (let uu____3219 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "TwoPhases") in
                            if uu____3219
                            then
                              let uu____3220 =
                                FStar_Syntax_Print.term_to_string lbdef in
                              FStar_Util.print1 "lb preprocessed into: %s\n"
                                uu____3220
                            else ());
                           (let uu___632_3222 = lb in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___632_3222.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___632_3222.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (uu___632_3222.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (uu___632_3222.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___632_3222.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___632_3222.FStar_Syntax_Syntax.lbpos)
                            }) in
                         let lbs'2 =
                           match pre_tau with
                           | FStar_Pervasives_Native.Some tau ->
                               FStar_List.map (preprocess_lb tau) lbs'1
                           | FStar_Pervasives_Native.None -> lbs'1 in
                         let e =
                           let uu____3232 =
                             let uu____3233 =
                               let uu____3246 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_constant
                                      FStar_Const.Const_unit) r in
                               (((FStar_Pervasives_Native.fst lbs), lbs'2),
                                 uu____3246) in
                             FStar_Syntax_Syntax.Tm_let uu____3233 in
                           FStar_Syntax_Syntax.mk uu____3232 r in
                         let env' =
                           let uu___639_3262 = env1 in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___639_3262.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___639_3262.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___639_3262.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___639_3262.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___639_3262.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___639_3262.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___639_3262.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___639_3262.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___639_3262.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___639_3262.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___639_3262.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___639_3262.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               should_generalize;
                             FStar_TypeChecker_Env.letrecs =
                               (uu___639_3262.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level = true;
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___639_3262.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___639_3262.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___639_3262.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___639_3262.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___639_3262.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax =
                               (uu___639_3262.FStar_TypeChecker_Env.lax);
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___639_3262.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___639_3262.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___639_3262.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___639_3262.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___639_3262.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___639_3262.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___639_3262.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___639_3262.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___639_3262.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___639_3262.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___639_3262.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___639_3262.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___639_3262.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___639_3262.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___639_3262.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___639_3262.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___639_3262.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___639_3262.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___639_3262.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___639_3262.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___639_3262.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___639_3262.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___639_3262.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___639_3262.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___639_3262.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___639_3262.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let e1 =
                           let uu____3264 =
                             (FStar_Options.use_two_phase_tc ()) &&
                               (FStar_TypeChecker_Env.should_verify env') in
                           if uu____3264
                           then
                             let drop_lbtyp e_lax =
                               let uu____3271 =
                                 let uu____3272 =
                                   FStar_Syntax_Subst.compress e_lax in
                                 uu____3272.FStar_Syntax_Syntax.n in
                               match uu____3271 with
                               | FStar_Syntax_Syntax.Tm_let
                                   ((false, lb::[]), e2) ->
                                   let lb_unannotated =
                                     let uu____3290 =
                                       let uu____3291 =
                                         FStar_Syntax_Subst.compress e in
                                       uu____3291.FStar_Syntax_Syntax.n in
                                     match uu____3290 with
                                     | FStar_Syntax_Syntax.Tm_let
                                         ((uu____3294, lb1::[]), uu____3296)
                                         ->
                                         let uu____3309 =
                                           let uu____3310 =
                                             FStar_Syntax_Subst.compress
                                               lb1.FStar_Syntax_Syntax.lbtyp in
                                           uu____3310.FStar_Syntax_Syntax.n in
                                         (match uu____3309 with
                                          | FStar_Syntax_Syntax.Tm_unknown ->
                                              true
                                          | uu____3313 -> false)
                                     | uu____3314 ->
                                         failwith
                                           "Impossible: first phase lb and second phase lb differ in structure!" in
                                   if lb_unannotated
                                   then
                                     let uu___664_3315 = e_lax in
                                     {
                                       FStar_Syntax_Syntax.n =
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((false,
                                               [(let uu___666_3327 = lb in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbname);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbunivs);
                                                   FStar_Syntax_Syntax.lbtyp
                                                     =
                                                     FStar_Syntax_Syntax.tun;
                                                   FStar_Syntax_Syntax.lbeff
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbeff);
                                                   FStar_Syntax_Syntax.lbdef
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbdef);
                                                   FStar_Syntax_Syntax.lbattrs
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbattrs);
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (uu___666_3327.FStar_Syntax_Syntax.lbpos)
                                                 })]), e2));
                                       FStar_Syntax_Syntax.pos =
                                         (uu___664_3315.FStar_Syntax_Syntax.pos);
                                       FStar_Syntax_Syntax.vars =
                                         (uu___664_3315.FStar_Syntax_Syntax.vars)
                                     }
                                   else e_lax
                               | uu____3329 -> e_lax in
                             let uu____3330 =
                               FStar_Util.record_time
                                 (fun uu____3337 ->
                                    let uu____3338 =
                                      let uu____3339 =
                                        let uu____3340 =
                                          FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                            (let uu___670_3349 = env' in
                                             {
                                               FStar_TypeChecker_Env.solver =
                                                 (uu___670_3349.FStar_TypeChecker_Env.solver);
                                               FStar_TypeChecker_Env.range =
                                                 (uu___670_3349.FStar_TypeChecker_Env.range);
                                               FStar_TypeChecker_Env.curmodule
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.curmodule);
                                               FStar_TypeChecker_Env.gamma =
                                                 (uu___670_3349.FStar_TypeChecker_Env.gamma);
                                               FStar_TypeChecker_Env.gamma_sig
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.gamma_sig);
                                               FStar_TypeChecker_Env.gamma_cache
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.gamma_cache);
                                               FStar_TypeChecker_Env.modules
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.modules);
                                               FStar_TypeChecker_Env.expected_typ
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.expected_typ);
                                               FStar_TypeChecker_Env.sigtab =
                                                 (uu___670_3349.FStar_TypeChecker_Env.sigtab);
                                               FStar_TypeChecker_Env.attrtab
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.attrtab);
                                               FStar_TypeChecker_Env.instantiate_imp
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.instantiate_imp);
                                               FStar_TypeChecker_Env.effects
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.effects);
                                               FStar_TypeChecker_Env.generalize
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.generalize);
                                               FStar_TypeChecker_Env.letrecs
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.letrecs);
                                               FStar_TypeChecker_Env.top_level
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.top_level);
                                               FStar_TypeChecker_Env.check_uvars
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.check_uvars);
                                               FStar_TypeChecker_Env.use_eq =
                                                 (uu___670_3349.FStar_TypeChecker_Env.use_eq);
                                               FStar_TypeChecker_Env.use_eq_strict
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.use_eq_strict);
                                               FStar_TypeChecker_Env.is_iface
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.is_iface);
                                               FStar_TypeChecker_Env.admit =
                                                 (uu___670_3349.FStar_TypeChecker_Env.admit);
                                               FStar_TypeChecker_Env.lax =
                                                 true;
                                               FStar_TypeChecker_Env.lax_universes
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.lax_universes);
                                               FStar_TypeChecker_Env.phase1 =
                                                 true;
                                               FStar_TypeChecker_Env.failhard
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.failhard);
                                               FStar_TypeChecker_Env.nosynth
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.nosynth);
                                               FStar_TypeChecker_Env.uvar_subtyping
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.uvar_subtyping);
                                               FStar_TypeChecker_Env.tc_term
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.tc_term);
                                               FStar_TypeChecker_Env.type_of
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.type_of);
                                               FStar_TypeChecker_Env.universe_of
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.universe_of);
                                               FStar_TypeChecker_Env.check_type_of
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.check_type_of);
                                               FStar_TypeChecker_Env.use_bv_sorts
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.use_bv_sorts);
                                               FStar_TypeChecker_Env.qtbl_name_and_index
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.qtbl_name_and_index);
                                               FStar_TypeChecker_Env.normalized_eff_names
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.normalized_eff_names);
                                               FStar_TypeChecker_Env.fv_delta_depths
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.fv_delta_depths);
                                               FStar_TypeChecker_Env.proof_ns
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.proof_ns);
                                               FStar_TypeChecker_Env.synth_hook
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.synth_hook);
                                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                               FStar_TypeChecker_Env.splice =
                                                 (uu___670_3349.FStar_TypeChecker_Env.splice);
                                               FStar_TypeChecker_Env.mpreprocess
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.mpreprocess);
                                               FStar_TypeChecker_Env.postprocess
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.postprocess);
                                               FStar_TypeChecker_Env.identifier_info
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.identifier_info);
                                               FStar_TypeChecker_Env.tc_hooks
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.tc_hooks);
                                               FStar_TypeChecker_Env.dsenv =
                                                 (uu___670_3349.FStar_TypeChecker_Env.dsenv);
                                               FStar_TypeChecker_Env.nbe =
                                                 (uu___670_3349.FStar_TypeChecker_Env.nbe);
                                               FStar_TypeChecker_Env.strict_args_tab
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.strict_args_tab);
                                               FStar_TypeChecker_Env.erasable_types_tab
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.erasable_types_tab);
                                               FStar_TypeChecker_Env.enable_defer_to_tac
                                                 =
                                                 (uu___670_3349.FStar_TypeChecker_Env.enable_defer_to_tac)
                                             }) e in
                                        FStar_All.pipe_right uu____3340
                                          (fun uu____3360 ->
                                             match uu____3360 with
                                             | (e1, uu____3368, uu____3369)
                                                 -> e1) in
                                      FStar_All.pipe_right uu____3339
                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                           env') in
                                    FStar_All.pipe_right uu____3338
                                      drop_lbtyp) in
                             match uu____3330 with
                             | (e1, ms) ->
                                 ((let uu____3373 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TwoPhases") in
                                   if uu____3373
                                   then
                                     let uu____3374 =
                                       FStar_Syntax_Print.term_to_string e1 in
                                     FStar_Util.print1
                                       "Let binding after phase 1: %s\n"
                                       uu____3374
                                   else ());
                                  (let uu____3377 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env1)
                                       (FStar_Options.Other "TCDeclTime") in
                                   if uu____3377
                                   then
                                     let uu____3378 =
                                       FStar_Util.string_of_int ms in
                                     FStar_Util.print1
                                       "Let binding elaborated (phase 1) in %s milliseconds\n"
                                       uu____3378
                                   else ());
                                  e1)
                           else e in
                         let uu____3381 =
                           let uu____3390 =
                             FStar_Syntax_Util.extract_attr'
                               FStar_Parser_Const.postprocess_with
                               se2.FStar_Syntax_Syntax.sigattrs in
                           match uu____3390 with
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
                         (match uu____3381 with
                          | (attrs1, post_tau) ->
                              let se3 =
                                let uu___700_3493 = se2 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (uu___700_3493.FStar_Syntax_Syntax.sigel);
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___700_3493.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___700_3493.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___700_3493.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs = attrs1;
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___700_3493.FStar_Syntax_Syntax.sigopts)
                                } in
                              let postprocess_lb tau lb =
                                let uu____3505 =
                                  FStar_Syntax_Subst.univ_var_opening
                                    lb.FStar_Syntax_Syntax.lbunivs in
                                match uu____3505 with
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
                                    let uu___714_3529 = lb in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbname);
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef = lbdef2;
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___714_3529.FStar_Syntax_Syntax.lbpos)
                                    } in
                              let uu____3530 =
                                FStar_Util.record_time
                                  (fun uu____3548 ->
                                     FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                                       env' e1) in
                              (match uu____3530 with
                               | (r1, ms) ->
                                   ((let uu____3574 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "TCDeclTime") in
                                     if uu____3574
                                     then
                                       let uu____3575 =
                                         FStar_Util.string_of_int ms in
                                       FStar_Util.print1
                                         "Let binding typechecked in phase 2 in %s milliseconds\n"
                                         uu____3575
                                     else ());
                                    (let uu____3577 =
                                       match r1 with
                                       | ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_let
                                              (lbs1, e2);
                                            FStar_Syntax_Syntax.pos =
                                              uu____3600;
                                            FStar_Syntax_Syntax.vars =
                                              uu____3601;_},
                                          uu____3602, g) when
                                           FStar_TypeChecker_Env.is_trivial g
                                           ->
                                           let lbs2 =
                                             let uu____3629 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.snd
                                                    lbs1)
                                                 (FStar_List.map
                                                    rename_parameters) in
                                             ((FStar_Pervasives_Native.fst
                                                 lbs1), uu____3629) in
                                           let lbs3 =
                                             let uu____3649 =
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
                                                 lbs2), uu____3649) in
                                           let quals1 =
                                             match e2.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_meta
                                                 (uu____3668,
                                                  FStar_Syntax_Syntax.Meta_desugared
                                                  (FStar_Syntax_Syntax.Masked_effect))
                                                 ->
                                                 FStar_Syntax_Syntax.HasMaskedEffect
                                                 :: quals
                                             | uu____3673 -> quals in
                                           ((let uu___744_3681 = se3 in
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_let
                                                    (lbs3, lids));
                                               FStar_Syntax_Syntax.sigrng =
                                                 (uu___744_3681.FStar_Syntax_Syntax.sigrng);
                                               FStar_Syntax_Syntax.sigquals =
                                                 quals1;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 (uu___744_3681.FStar_Syntax_Syntax.sigmeta);
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (uu___744_3681.FStar_Syntax_Syntax.sigattrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 (uu___744_3681.FStar_Syntax_Syntax.sigopts)
                                             }), lbs3)
                                       | uu____3684 ->
                                           failwith
                                             "impossible (typechecking should preserve Tm_let)" in
                                     match uu____3577 with
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
                                          (let uu____3735 = log env1 in
                                           if uu____3735
                                           then
                                             let uu____3736 =
                                               let uu____3737 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.snd
                                                      lbs1)
                                                   (FStar_List.map
                                                      (fun lb ->
                                                         let should_log =
                                                           let uu____3752 =
                                                             let uu____3761 =
                                                               let uu____3762
                                                                 =
                                                                 let uu____3765
                                                                   =
                                                                   FStar_Util.right
                                                                    lb.FStar_Syntax_Syntax.lbname in
                                                                 uu____3765.FStar_Syntax_Syntax.fv_name in
                                                               uu____3762.FStar_Syntax_Syntax.v in
                                                             FStar_TypeChecker_Env.try_lookup_val_decl
                                                               env1
                                                               uu____3761 in
                                                           match uu____3752
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                               -> true
                                                           | uu____3772 ->
                                                               false in
                                                         if should_log
                                                         then
                                                           let uu____3781 =
                                                             FStar_Syntax_Print.lbname_to_string
                                                               lb.FStar_Syntax_Syntax.lbname in
                                                           let uu____3782 =
                                                             FStar_Syntax_Print.term_to_string
                                                               lb.FStar_Syntax_Syntax.lbtyp in
                                                           FStar_Util.format2
                                                             "let %s : %s"
                                                             uu____3781
                                                             uu____3782
                                                         else "")) in
                                               FStar_All.pipe_right
                                                 uu____3737
                                                 (FStar_String.concat "\n") in
                                             FStar_Util.print1 "%s\n"
                                               uu____3736
                                           else ());
                                          check_must_erase_attribute env0 se4;
                                          ([se4], [], env0))))))))
           | FStar_Syntax_Syntax.Sig_polymonadic_bind
               (m, n, p, t, uu____3796) ->
               let t1 =
                 let uu____3798 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3798
                 then
                   let uu____3799 =
                     let uu____3804 =
                       let uu____3805 =
                         let uu____3806 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_bind
                             (let uu___769_3813 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___769_3813.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___769_3813.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___769_3813.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___769_3813.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___769_3813.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___769_3813.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___769_3813.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___769_3813.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___769_3813.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___769_3813.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___769_3813.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___769_3813.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___769_3813.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___769_3813.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___769_3813.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___769_3813.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___769_3813.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___769_3813.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___769_3813.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___769_3813.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___769_3813.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___769_3813.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___769_3813.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___769_3813.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___769_3813.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___769_3813.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___769_3813.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___769_3813.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___769_3813.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___769_3813.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___769_3813.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___769_3813.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___769_3813.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___769_3813.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___769_3813.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___769_3813.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___769_3813.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___769_3813.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___769_3813.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___769_3813.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___769_3813.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___769_3813.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___769_3813.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___769_3813.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___769_3813.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n p t in
                         FStar_All.pipe_right uu____3806
                           (fun uu____3822 ->
                              match uu____3822 with
                              | (t1, ty) ->
                                  let uu___774_3829 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                         (m, n, p, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___774_3829.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___774_3829.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___774_3829.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___774_3829.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___774_3829.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3805
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3804
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_bind
                              (uu____3845, uu____3846, uu____3847, t1, ty) ->
                              (t1, ty)
                          | uu____3850 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_bind must be a Sig_polymonadic_bind") in
                   match uu____3799 with
                   | (t1, ty) ->
                       ((let uu____3858 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3858
                         then
                           let uu____3859 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___789_3862 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                       (m, n, p, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___789_3862.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___789_3862.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___789_3862.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___789_3862.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___789_3862.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic bind after phase 1: %s\n"
                             uu____3859
                         else ());
                        t1)
                 else t in
               let uu____3865 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_bind env m n p t1 in
               (match uu____3865 with
                | (t2, ty) ->
                    let se2 =
                      let uu___796_3883 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_bind
                             (m, n, p, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___796_3883.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___796_3883.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___796_3883.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___796_3883.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___796_3883.FStar_Syntax_Syntax.sigopts)
                      } in
                    ([se2], [], env0))
           | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
               (m, n, t, uu____3891) ->
               let t1 =
                 let uu____3893 =
                   (FStar_Options.use_two_phase_tc ()) &&
                     (FStar_TypeChecker_Env.should_verify env) in
                 if uu____3893
                 then
                   let uu____3894 =
                     let uu____3899 =
                       let uu____3900 =
                         let uu____3901 =
                           FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp
                             (let uu___806_3908 = env in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___806_3908.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___806_3908.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___806_3908.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___806_3908.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_sig =
                                  (uu___806_3908.FStar_TypeChecker_Env.gamma_sig);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___806_3908.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___806_3908.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___806_3908.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___806_3908.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.attrtab =
                                  (uu___806_3908.FStar_TypeChecker_Env.attrtab);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___806_3908.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___806_3908.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___806_3908.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___806_3908.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___806_3908.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___806_3908.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___806_3908.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.use_eq_strict =
                                  (uu___806_3908.FStar_TypeChecker_Env.use_eq_strict);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___806_3908.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___806_3908.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___806_3908.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.phase1 = true;
                                FStar_TypeChecker_Env.failhard =
                                  (uu___806_3908.FStar_TypeChecker_Env.failhard);
                                FStar_TypeChecker_Env.nosynth =
                                  (uu___806_3908.FStar_TypeChecker_Env.nosynth);
                                FStar_TypeChecker_Env.uvar_subtyping =
                                  (uu___806_3908.FStar_TypeChecker_Env.uvar_subtyping);
                                FStar_TypeChecker_Env.tc_term =
                                  (uu___806_3908.FStar_TypeChecker_Env.tc_term);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___806_3908.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___806_3908.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.check_type_of =
                                  (uu___806_3908.FStar_TypeChecker_Env.check_type_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___806_3908.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qtbl_name_and_index =
                                  (uu___806_3908.FStar_TypeChecker_Env.qtbl_name_and_index);
                                FStar_TypeChecker_Env.normalized_eff_names =
                                  (uu___806_3908.FStar_TypeChecker_Env.normalized_eff_names);
                                FStar_TypeChecker_Env.fv_delta_depths =
                                  (uu___806_3908.FStar_TypeChecker_Env.fv_delta_depths);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___806_3908.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth_hook =
                                  (uu___806_3908.FStar_TypeChecker_Env.synth_hook);
                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                  =
                                  (uu___806_3908.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                FStar_TypeChecker_Env.splice =
                                  (uu___806_3908.FStar_TypeChecker_Env.splice);
                                FStar_TypeChecker_Env.mpreprocess =
                                  (uu___806_3908.FStar_TypeChecker_Env.mpreprocess);
                                FStar_TypeChecker_Env.postprocess =
                                  (uu___806_3908.FStar_TypeChecker_Env.postprocess);
                                FStar_TypeChecker_Env.identifier_info =
                                  (uu___806_3908.FStar_TypeChecker_Env.identifier_info);
                                FStar_TypeChecker_Env.tc_hooks =
                                  (uu___806_3908.FStar_TypeChecker_Env.tc_hooks);
                                FStar_TypeChecker_Env.dsenv =
                                  (uu___806_3908.FStar_TypeChecker_Env.dsenv);
                                FStar_TypeChecker_Env.nbe =
                                  (uu___806_3908.FStar_TypeChecker_Env.nbe);
                                FStar_TypeChecker_Env.strict_args_tab =
                                  (uu___806_3908.FStar_TypeChecker_Env.strict_args_tab);
                                FStar_TypeChecker_Env.erasable_types_tab =
                                  (uu___806_3908.FStar_TypeChecker_Env.erasable_types_tab);
                                FStar_TypeChecker_Env.enable_defer_to_tac =
                                  (uu___806_3908.FStar_TypeChecker_Env.enable_defer_to_tac)
                              }) m n t in
                         FStar_All.pipe_right uu____3901
                           (fun uu____3917 ->
                              match uu____3917 with
                              | (t1, ty) ->
                                  let uu___811_3924 = se1 in
                                  {
                                    FStar_Syntax_Syntax.sigel =
                                      (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                         (m, n, t1, ty));
                                    FStar_Syntax_Syntax.sigrng =
                                      (uu___811_3924.FStar_Syntax_Syntax.sigrng);
                                    FStar_Syntax_Syntax.sigquals =
                                      (uu___811_3924.FStar_Syntax_Syntax.sigquals);
                                    FStar_Syntax_Syntax.sigmeta =
                                      (uu___811_3924.FStar_Syntax_Syntax.sigmeta);
                                    FStar_Syntax_Syntax.sigattrs =
                                      (uu___811_3924.FStar_Syntax_Syntax.sigattrs);
                                    FStar_Syntax_Syntax.sigopts =
                                      (uu___811_3924.FStar_Syntax_Syntax.sigopts)
                                  }) in
                       FStar_All.pipe_right uu____3900
                         (FStar_TypeChecker_Normalize.elim_uvars env) in
                     FStar_All.pipe_right uu____3899
                       (fun se2 ->
                          match se2.FStar_Syntax_Syntax.sigel with
                          | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                              (uu____3939, uu____3940, t1, ty) -> (t1, ty)
                          | uu____3943 ->
                              failwith
                                "Impossible! tc for Sig_polymonadic_subcomp must be a Sig_polymonadic_subcomp") in
                   match uu____3894 with
                   | (t1, ty) ->
                       ((let uu____3951 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "TwoPhases") in
                         if uu____3951
                         then
                           let uu____3952 =
                             FStar_Syntax_Print.sigelt_to_string
                               (let uu___825_3955 = se1 in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                       (m, n, t1, ty));
                                  FStar_Syntax_Syntax.sigrng =
                                    (uu___825_3955.FStar_Syntax_Syntax.sigrng);
                                  FStar_Syntax_Syntax.sigquals =
                                    (uu___825_3955.FStar_Syntax_Syntax.sigquals);
                                  FStar_Syntax_Syntax.sigmeta =
                                    (uu___825_3955.FStar_Syntax_Syntax.sigmeta);
                                  FStar_Syntax_Syntax.sigattrs =
                                    (uu___825_3955.FStar_Syntax_Syntax.sigattrs);
                                  FStar_Syntax_Syntax.sigopts =
                                    (uu___825_3955.FStar_Syntax_Syntax.sigopts)
                                }) in
                           FStar_Util.print1
                             "Polymonadic subcomp after phase 1: %s\n"
                             uu____3952
                         else ());
                        t1)
                 else t in
               let uu____3958 =
                 FStar_TypeChecker_TcEffect.tc_polymonadic_subcomp env m n t1 in
               (match uu____3958 with
                | (t2, ty) ->
                    let se2 =
                      let uu___832_3976 = se1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                             (m, n, t2, ty));
                        FStar_Syntax_Syntax.sigrng =
                          (uu___832_3976.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___832_3976.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___832_3976.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___832_3976.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___832_3976.FStar_Syntax_Syntax.sigopts)
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
      (let uu____4013 =
         let uu____4014 =
           FStar_Ident.string_of_lid env1.FStar_TypeChecker_Env.curmodule in
         FStar_Options.debug_module uu____4014 in
       if uu____4013
       then
         let uu____4015 =
           let uu____4016 =
             FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
               (FStar_List.map FStar_Ident.string_of_lid) in
           FStar_All.pipe_right uu____4016 (FStar_String.concat ", ") in
         FStar_Util.print1 "Processing %s\n" uu____4015
       else ());
      (let uu____4027 = FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
       if uu____4027
       then
         let uu____4028 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 ">>>>>>>>>>>>>>tc_decl %s\n" uu____4028
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
        (let uu____4071 = FStar_TypeChecker_Env.debug env FStar_Options.Low in
         if uu____4071
         then
           let uu____4072 = FStar_Syntax_Print.sigelt_to_string se in
           let uu____4073 = FStar_Util.string_of_bool from_cache in
           FStar_Util.print2
             ">>>>>>>>>>>>>>Adding top-level decl to environment: %s (from_cache:%s)\n"
             uu____4072 uu____4073
         else ());
        (match se.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_inductive_typ uu____4075 ->
             let uu____4092 =
               let uu____4097 =
                 let uu____4098 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4098 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4097) in
             FStar_Errors.raise_error uu____4092
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_datacon uu____4099 ->
             let uu____4114 =
               let uu____4119 =
                 let uu____4120 = FStar_Syntax_Print.sigelt_to_string se in
                 FStar_Util.format1
                   "add_sigelt_to_env: unexpected bare type/data constructor: %s"
                   uu____4120 in
               (FStar_Errors.Fatal_UnexpectedInductivetype, uu____4119) in
             FStar_Errors.raise_error uu____4114
               se.FStar_Syntax_Syntax.sigrng
         | FStar_Syntax_Syntax.Sig_declare_typ
             (uu____4121, uu____4122, uu____4123) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___2_4127 ->
                     match uu___2_4127 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4128 -> false))
             -> env
         | FStar_Syntax_Syntax.Sig_let (uu____4129, uu____4130) when
             FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___2_4138 ->
                     match uu___2_4138 with
                     | FStar_Syntax_Syntax.OnlyName -> true
                     | uu____4139 -> false))
             -> env
         | uu____4140 ->
             let env1 = FStar_TypeChecker_Env.push_sigelt env se in
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PushOptions uu____4142) ->
                  if from_cache
                  then env1
                  else
                    (let uu___882_4146 = env1 in
                     let uu____4147 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___882_4146.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___882_4146.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___882_4146.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___882_4146.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___882_4146.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___882_4146.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___882_4146.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___882_4146.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___882_4146.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___882_4146.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___882_4146.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___882_4146.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___882_4146.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___882_4146.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___882_4146.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___882_4146.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___882_4146.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___882_4146.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___882_4146.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___882_4146.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___882_4146.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___882_4146.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___882_4146.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___882_4146.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___882_4146.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___882_4146.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___882_4146.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___882_4146.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___882_4146.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___882_4146.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___882_4146.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___882_4146.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___882_4146.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___882_4146.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4147;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___882_4146.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___882_4146.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___882_4146.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___882_4146.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___882_4146.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___882_4146.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___882_4146.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___882_4146.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___882_4146.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___882_4146.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___882_4146.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___882_4146.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.PopOptions) ->
                  if from_cache
                  then env1
                  else
                    (let uu___882_4149 = env1 in
                     let uu____4150 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___882_4149.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___882_4149.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___882_4149.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___882_4149.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___882_4149.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___882_4149.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___882_4149.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___882_4149.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___882_4149.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___882_4149.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___882_4149.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___882_4149.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___882_4149.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___882_4149.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___882_4149.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___882_4149.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___882_4149.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___882_4149.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___882_4149.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___882_4149.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___882_4149.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___882_4149.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___882_4149.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___882_4149.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___882_4149.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___882_4149.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___882_4149.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___882_4149.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___882_4149.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___882_4149.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___882_4149.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___882_4149.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___882_4149.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___882_4149.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4150;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___882_4149.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___882_4149.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___882_4149.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___882_4149.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___882_4149.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___882_4149.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___882_4149.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___882_4149.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___882_4149.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___882_4149.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___882_4149.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___882_4149.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.SetOptions uu____4151) ->
                  if from_cache
                  then env1
                  else
                    (let uu___882_4153 = env1 in
                     let uu____4154 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___882_4153.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___882_4153.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___882_4153.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___882_4153.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___882_4153.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___882_4153.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___882_4153.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___882_4153.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___882_4153.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___882_4153.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___882_4153.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___882_4153.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___882_4153.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___882_4153.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___882_4153.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___882_4153.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___882_4153.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___882_4153.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___882_4153.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___882_4153.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___882_4153.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___882_4153.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___882_4153.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___882_4153.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___882_4153.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___882_4153.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___882_4153.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___882_4153.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___882_4153.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___882_4153.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___882_4153.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___882_4153.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___882_4153.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___882_4153.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4154;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___882_4153.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___882_4153.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___882_4153.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___882_4153.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___882_4153.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___882_4153.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___882_4153.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___882_4153.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___882_4153.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___882_4153.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___882_4153.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___882_4153.FStar_TypeChecker_Env.enable_defer_to_tac)
                     })
              | FStar_Syntax_Syntax.Sig_pragma
                  (FStar_Syntax_Syntax.ResetOptions uu____4155) ->
                  if from_cache
                  then env1
                  else
                    (let uu___882_4159 = env1 in
                     let uu____4160 = FStar_Options.using_facts_from () in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___882_4159.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___882_4159.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___882_4159.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___882_4159.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_sig =
                         (uu___882_4159.FStar_TypeChecker_Env.gamma_sig);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___882_4159.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___882_4159.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___882_4159.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___882_4159.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.attrtab =
                         (uu___882_4159.FStar_TypeChecker_Env.attrtab);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___882_4159.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___882_4159.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___882_4159.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___882_4159.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___882_4159.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___882_4159.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___882_4159.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.use_eq_strict =
                         (uu___882_4159.FStar_TypeChecker_Env.use_eq_strict);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___882_4159.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___882_4159.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax =
                         (uu___882_4159.FStar_TypeChecker_Env.lax);
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___882_4159.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.phase1 =
                         (uu___882_4159.FStar_TypeChecker_Env.phase1);
                       FStar_TypeChecker_Env.failhard =
                         (uu___882_4159.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___882_4159.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.uvar_subtyping =
                         (uu___882_4159.FStar_TypeChecker_Env.uvar_subtyping);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___882_4159.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___882_4159.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___882_4159.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.check_type_of =
                         (uu___882_4159.FStar_TypeChecker_Env.check_type_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___882_4159.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qtbl_name_and_index =
                         (uu___882_4159.FStar_TypeChecker_Env.qtbl_name_and_index);
                       FStar_TypeChecker_Env.normalized_eff_names =
                         (uu___882_4159.FStar_TypeChecker_Env.normalized_eff_names);
                       FStar_TypeChecker_Env.fv_delta_depths =
                         (uu___882_4159.FStar_TypeChecker_Env.fv_delta_depths);
                       FStar_TypeChecker_Env.proof_ns = uu____4160;
                       FStar_TypeChecker_Env.synth_hook =
                         (uu___882_4159.FStar_TypeChecker_Env.synth_hook);
                       FStar_TypeChecker_Env.try_solve_implicits_hook =
                         (uu___882_4159.FStar_TypeChecker_Env.try_solve_implicits_hook);
                       FStar_TypeChecker_Env.splice =
                         (uu___882_4159.FStar_TypeChecker_Env.splice);
                       FStar_TypeChecker_Env.mpreprocess =
                         (uu___882_4159.FStar_TypeChecker_Env.mpreprocess);
                       FStar_TypeChecker_Env.postprocess =
                         (uu___882_4159.FStar_TypeChecker_Env.postprocess);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___882_4159.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___882_4159.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___882_4159.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.nbe =
                         (uu___882_4159.FStar_TypeChecker_Env.nbe);
                       FStar_TypeChecker_Env.strict_args_tab =
                         (uu___882_4159.FStar_TypeChecker_Env.strict_args_tab);
                       FStar_TypeChecker_Env.erasable_types_tab =
                         (uu___882_4159.FStar_TypeChecker_Env.erasable_types_tab);
                       FStar_TypeChecker_Env.enable_defer_to_tac =
                         (uu___882_4159.FStar_TypeChecker_Env.enable_defer_to_tac)
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
                            let uu____4174 =
                              FStar_Syntax_Util.action_as_lb
                                ne.FStar_Syntax_Syntax.mname a
                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                            FStar_TypeChecker_Env.push_sigelt env3 uu____4174)
                       env2)
              | FStar_Syntax_Syntax.Sig_sub_effect sub ->
                  FStar_TypeChecker_Util.update_env_sub_eff env1 sub
                    se.FStar_Syntax_Syntax.sigrng
              | FStar_Syntax_Syntax.Sig_polymonadic_bind
                  (m, n, p, uu____4179, ty) ->
                  FStar_TypeChecker_Util.update_env_polymonadic_bind env1 m n
                    p ty
              | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                  (m, n, uu____4183, ty) ->
                  FStar_TypeChecker_Env.add_polymonadic_subcomp env1 m n ty
              | uu____4185 -> env1))
let (tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun ses ->
      let rec process_one_decl uu____4233 se =
        match uu____4233 with
        | (ses1, env1) ->
            let uu____4259 =
              env1.FStar_TypeChecker_Env.nosynth &&
                (FStar_Options.debug_any ()) in
            if uu____4259
            then ((ses1, env1), [])
            else
              ((let uu____4284 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.Low in
                if uu____4284
                then
                  let uu____4285 = FStar_Syntax_Print.tag_of_sigelt se in
                  let uu____4286 = FStar_Syntax_Print.sigelt_to_string se in
                  FStar_Util.print2
                    ">>>>>>>>>>>>>>Checking top-level %s decl %s\n"
                    uu____4285 uu____4286
                else ());
               (let uu____4288 = tc_decl env1 se in
                match uu____4288 with
                | (ses', ses_elaborated, env2) ->
                    let ses'1 =
                      FStar_All.pipe_right ses'
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4333 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4333
                               then
                                 let uu____4334 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from %s\n" uu____4334
                               else ());
                              FStar_TypeChecker_Normalize.elim_uvars env2 se1)) in
                    let ses_elaborated1 =
                      FStar_All.pipe_right ses_elaborated
                        (FStar_List.map
                           (fun se1 ->
                              (let uu____4347 =
                                 FStar_TypeChecker_Env.debug env2
                                   (FStar_Options.Other "UF") in
                               if uu____4347
                               then
                                 let uu____4348 =
                                   FStar_Syntax_Print.sigelt_to_string se1 in
                                 FStar_Util.print1
                                   "About to elim vars from (elaborated) %s\n"
                                   uu____4348
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
                      (let uu____4362 =
                         (FStar_Options.log_types ()) ||
                           (FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env3)
                              (FStar_Options.Other "LogTypes")) in
                       if uu____4362
                       then
                         let uu____4363 =
                           FStar_List.fold_left
                             (fun s ->
                                fun se1 ->
                                  let uu____4369 =
                                    let uu____4370 =
                                      FStar_Syntax_Print.sigelt_to_string se1 in
                                    Prims.op_Hat uu____4370 "\n" in
                                  Prims.op_Hat s uu____4369) "" ses'1 in
                         FStar_Util.print1 "Checked: %s\n" uu____4363
                       else ());
                      FStar_List.iter
                        (fun se1 ->
                           (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                             env3 se1) ses'1;
                      (((FStar_List.rev_append ses'1 ses1), env3),
                        ses_elaborated1))))) in
      let process_one_decl_timed acc se =
        let uu____4420 = acc in
        match uu____4420 with
        | (uu____4439, env1) ->
            let r =
              let uu____4458 =
                let uu____4461 =
                  let uu____4462 = FStar_TypeChecker_Env.current_module env1 in
                  FStar_Ident.string_of_lid uu____4462 in
                FStar_Pervasives_Native.Some uu____4461 in
              FStar_Profiling.profile
                (fun uu____4476 -> process_one_decl acc se) uu____4458
                "FStar.TypeChecker.Tc.process_one_decl" in
            ((let uu____4478 = FStar_Options.profile_group_by_decls () in
              if uu____4478
              then
                let tag =
                  match FStar_Syntax_Util.lids_of_sigelt se with
                  | hd::uu____4481 -> FStar_Ident.string_of_lid hd
                  | uu____4484 ->
                      FStar_Range.string_of_range
                        (FStar_Syntax_Util.range_of_sigelt se) in
                FStar_Profiling.report_and_clear tag
              else ());
             r) in
      let uu____4488 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____4502 ->
             FStar_Util.fold_flatten process_one_decl_timed ([], env) ses) in
      match uu____4488 with
      | (ses1, env1) -> ((FStar_List.rev_append ses1 []), env1)
let (uu___962 : unit) =
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
        (fun uu____4604 -> FStar_TypeChecker_Env.snapshot env msg)
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
          (fun uu____4642 ->
             let env = FStar_TypeChecker_Env.rollback solver msg depth in env)
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun msg ->
      let uu____4654 = snapshot_context env msg in
      FStar_Pervasives_Native.snd uu____4654
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
        let uu____4708 =
          FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
        FStar_Options.should_verify uu____4708 in
      let action = if verify then "Verifying" else "Lax-checking" in
      let label =
        if modul.FStar_Syntax_Syntax.is_interface
        then "interface"
        else "implementation" in
      (let uu____4714 = FStar_Options.debug_any () in
       if uu____4714
       then
         let uu____4715 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.print3 "%s %s of %s\n" action label uu____4715
       else ());
      (let name =
         let uu____4718 =
           FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
         FStar_Util.format2 "%s %s"
           (if modul.FStar_Syntax_Syntax.is_interface
            then "interface"
            else "module") uu____4718 in
       let env1 =
         let uu___986_4721 = env in
         {
           FStar_TypeChecker_Env.solver =
             (uu___986_4721.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___986_4721.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___986_4721.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___986_4721.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___986_4721.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___986_4721.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___986_4721.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___986_4721.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___986_4721.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___986_4721.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___986_4721.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___986_4721.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___986_4721.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___986_4721.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___986_4721.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___986_4721.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___986_4721.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.use_eq_strict =
             (uu___986_4721.FStar_TypeChecker_Env.use_eq_strict);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___986_4721.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___986_4721.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___986_4721.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___986_4721.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___986_4721.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___986_4721.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___986_4721.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___986_4721.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___986_4721.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___986_4721.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___986_4721.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___986_4721.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___986_4721.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___986_4721.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___986_4721.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___986_4721.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___986_4721.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___986_4721.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.mpreprocess =
             (uu___986_4721.FStar_TypeChecker_Env.mpreprocess);
           FStar_TypeChecker_Env.postprocess =
             (uu___986_4721.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.identifier_info =
             (uu___986_4721.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___986_4721.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___986_4721.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___986_4721.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___986_4721.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___986_4721.FStar_TypeChecker_Env.erasable_types_tab);
           FStar_TypeChecker_Env.enable_defer_to_tac =
             (uu___986_4721.FStar_TypeChecker_Env.enable_defer_to_tac)
         } in
       let env2 =
         FStar_TypeChecker_Env.set_current_module env1
           modul.FStar_Syntax_Syntax.name in
       let uu____4723 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations in
       match uu____4723 with
       | (ses, env3) ->
           ((let uu___993_4741 = modul in
             {
               FStar_Syntax_Syntax.name =
                 (uu___993_4741.FStar_Syntax_Syntax.name);
               FStar_Syntax_Syntax.declarations = ses;
               FStar_Syntax_Syntax.is_interface =
                 (uu___993_4741.FStar_Syntax_Syntax.is_interface)
             }), env3))
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
        let uu____4769 = tc_decls env decls in
        match uu____4769 with
        | (ses, env1) ->
            let modul1 =
              let uu___1001_4791 = modul in
              {
                FStar_Syntax_Syntax.name =
                  (uu___1001_4791.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.is_interface =
                  (uu___1001_4791.FStar_Syntax_Syntax.is_interface)
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
          (let uu____4824 =
             FStar_All.pipe_right
               env.FStar_TypeChecker_Env.qtbl_name_and_index
               FStar_Pervasives_Native.fst in
           FStar_All.pipe_right uu____4824 FStar_Util.smap_clear);
          (let uu____4852 =
             let uu____4853 =
               let uu____4854 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               Prims.op_Hat "Ending modul " uu____4854 in
             pop_context env uu____4853 in
           FStar_All.pipe_right uu____4852 (fun uu____4855 -> ()));
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
          let uu____4880 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____4880 in
        let env01 = push_context env0 msg in
        let uu____4882 = tc_partial_modul env01 m in
        match uu____4882 with
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
        let uu____4905 =
          let uu____4906 =
            FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
          Prims.op_Hat "Internals for " uu____4906 in
        push_context env uu____4905 in
      let env2 =
        FStar_List.fold_left
          (fun env2 ->
             fun se ->
               let env3 = add_sigelt_to_env env2 se true in
               let lids = FStar_Syntax_Util.lids_of_sigelt se in
               FStar_All.pipe_right lids
                 (FStar_List.iter
                    (fun lid ->
                       let uu____4925 =
                         FStar_TypeChecker_Env.lookup_sigelt env3 lid in
                       ()));
               env3) env1 m.FStar_Syntax_Syntax.declarations in
      let uu____4928 = finish_partial_modul true true env2 m in
      match uu____4928 with | (uu____4933, env3) -> env3
let (check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      Prims.bool -> (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env))
  =
  fun env ->
    fun m ->
      fun b ->
        (let uu____4955 = FStar_Options.debug_any () in
         if uu____4955
         then
           let uu____4956 =
             FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
           FStar_Util.print2 "Checking %s: %s\n"
             (if m.FStar_Syntax_Syntax.is_interface
              then "i'face"
              else "module") uu____4956
         else ());
        (let uu____4960 =
           let uu____4961 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.dump_module uu____4961 in
         if uu____4960
         then
           let uu____4962 = FStar_Syntax_Print.modul_to_string m in
           FStar_Util.print1 "Module before type checking:\n%s\n" uu____4962
         else ());
        (let env1 =
           let uu___1041_4965 = env in
           let uu____4966 =
             let uu____4967 =
               let uu____4968 =
                 FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
               FStar_Options.should_verify uu____4968 in
             Prims.op_Negation uu____4967 in
           {
             FStar_TypeChecker_Env.solver =
               (uu___1041_4965.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___1041_4965.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___1041_4965.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___1041_4965.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___1041_4965.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___1041_4965.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___1041_4965.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___1041_4965.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___1041_4965.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___1041_4965.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___1041_4965.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___1041_4965.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___1041_4965.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___1041_4965.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___1041_4965.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___1041_4965.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___1041_4965.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___1041_4965.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___1041_4965.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___1041_4965.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = uu____4966;
             FStar_TypeChecker_Env.lax_universes =
               (uu___1041_4965.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___1041_4965.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___1041_4965.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___1041_4965.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___1041_4965.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___1041_4965.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___1041_4965.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___1041_4965.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___1041_4965.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___1041_4965.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___1041_4965.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___1041_4965.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___1041_4965.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___1041_4965.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___1041_4965.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___1041_4965.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___1041_4965.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___1041_4965.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___1041_4965.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___1041_4965.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___1041_4965.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___1041_4965.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___1041_4965.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___1041_4965.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___1041_4965.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___1041_4965.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         let uu____4969 = tc_modul env1 m b in
         match uu____4969 with
         | (m1, env2) ->
             ((let uu____4981 =
                 let uu____4982 =
                   FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                 FStar_Options.dump_module uu____4982 in
               if uu____4981
               then
                 let uu____4983 = FStar_Syntax_Print.modul_to_string m1 in
                 FStar_Util.print1 "Module after type checking:\n%s\n"
                   uu____4983
               else ());
              (let uu____4986 =
                 (let uu____4989 =
                    FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                  FStar_Options.dump_module uu____4989) &&
                   (let uu____4991 =
                      FStar_Ident.string_of_lid m1.FStar_Syntax_Syntax.name in
                    FStar_Options.debug_at_level uu____4991
                      (FStar_Options.Other "Normalize")) in
               if uu____4986
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
                         let uu____5024 =
                           FStar_Syntax_Subst.open_univ_vars
                             lb.FStar_Syntax_Syntax.lbunivs
                             lb.FStar_Syntax_Syntax.lbdef in
                         match uu____5024 with
                         | (univnames, e) ->
                             let uu___1063_5031 = lb in
                             let uu____5032 =
                               let uu____5035 =
                                 FStar_TypeChecker_Env.push_univ_vars env2
                                   univnames in
                               n uu____5035 e in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____5032;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1063_5031.FStar_Syntax_Syntax.lbpos)
                             } in
                       let uu___1065_5036 = se in
                       let uu____5037 =
                         let uu____5038 =
                           let uu____5045 =
                             let uu____5046 = FStar_List.map update lbs in
                             (b1, uu____5046) in
                           (uu____5045, ids) in
                         FStar_Syntax_Syntax.Sig_let uu____5038 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____5037;
                         FStar_Syntax_Syntax.sigrng =
                           (uu___1065_5036.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___1065_5036.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___1065_5036.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___1065_5036.FStar_Syntax_Syntax.sigattrs);
                         FStar_Syntax_Syntax.sigopts =
                           (uu___1065_5036.FStar_Syntax_Syntax.sigopts)
                       }
                   | uu____5053 -> se in
                 let normalized_module =
                   let uu___1069_5055 = m1 in
                   let uu____5056 =
                     FStar_List.map normalize_toplevel_lets
                       m1.FStar_Syntax_Syntax.declarations in
                   {
                     FStar_Syntax_Syntax.name =
                       (uu___1069_5055.FStar_Syntax_Syntax.name);
                     FStar_Syntax_Syntax.declarations = uu____5056;
                     FStar_Syntax_Syntax.is_interface =
                       (uu___1069_5055.FStar_Syntax_Syntax.is_interface)
                   } in
                 let uu____5057 =
                   FStar_Syntax_Print.modul_to_string normalized_module in
                 FStar_Util.print1 "%s\n" uu____5057
               else ());
              (m1, env2)))